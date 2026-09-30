//! Brainfuck JIT.

use capstone::prelude::*;
use onlineasm::asmkit::Span;
use onlineasm::{onlineasm, regs, Assembler, JitAllocator, Label, Target, VReg};
use std::io::{self, Read, Write};
use std::time::Instant;

const TAPE_LEN: usize = 30_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Add(u8),
    Move(isize),
    Clear,
    Output,
    Input,
    LoopStart(usize),
    LoopEnd(usize),
}

fn parse(src: &str) -> Result<Vec<Op>, String> {
    let mut ops = Vec::new();
    let mut open = Vec::new();
    for (pos, c) in src.bytes().enumerate() {
        match c {
            b'+' | b'-' => {
                let d = if c == b'+' { 1u8 } else { 255u8 };
                match ops.last_mut() {
                    Some(Op::Add(n)) => *n = n.wrapping_add(d),
                    _ => ops.push(Op::Add(d)),
                }
            }
            b'>' | b'<' => {
                let d = if c == b'>' { 1 } else { -1 };
                match ops.last_mut() {
                    Some(Op::Move(n)) => *n += d,
                    _ => ops.push(Op::Move(d)),
                }
            }
            b'.' => ops.push(Op::Output),
            b',' => ops.push(Op::Input),
            b'[' => {
                open.push(ops.len());
                ops.push(Op::LoopStart(0));
            }
            b']' => {
                let start = open.pop().ok_or(format!("unmatched `]` at byte {pos}"))?;
                // `[-]` and `[+]` zero the cell whatever its value.
                if ops.len() == start + 2 && matches!(ops[start + 1], Op::Add(1 | 255)) {
                    ops.truncate(start);
                    ops.push(Op::Clear);
                    continue;
                }
                let end = ops.len();
                ops[start] = Op::LoopStart(end);
                ops.push(Op::LoopEnd(start));
            }
            _ => {}
        }

        if matches!(ops.last(), Some(Op::Add(0) | Op::Move(0))) {
            ops.pop();
        }
    }
    if let Some(start) = open.pop() {
        return Err(format!("unmatched `[` (instruction {start})"));
    }
    Ok(ops)
}

struct Io {
    input: io::StdinLock<'static>,
    output: io::BufWriter<io::StdoutLock<'static>>,
}

impl Io {
    fn new() -> Self {
        Io {
            input: io::stdin().lock(),
            output: io::BufWriter::new(io::stdout().lock()),
        }
    }

    fn putc(&mut self, c: u8) {
        let res = self.output.write_all(&[c]);
        let res = res.and_then(|()| {
            if c == b'\n' {
                self.output.flush()
            } else {
                Ok(())
            }
        });
        if res.is_err() {
            // Closed pipe or similar. There is no way to report it through
            // the generated code, so stop here.
            std::process::exit(1);
        }
    }

    /// Returns the next input byte, or 0 at end of input.
    fn getc(&mut self) -> u8 {
        let _ = self.output.flush();
        let mut c = [0u8];
        match self.input.read(&mut c) {
            Ok(1) => c[0],
            _ => 0,
        }
    }
}

extern "C" fn bf_putc(io: *mut Io, c: u64) -> u64 {
    // SAFETY: the JIT passes back the `Io` pointer `run_jit` gave it.
    unsafe { &mut *io }.putc(c as u8);
    0
}

extern "C" fn bf_getc(io: *mut Io) -> u64 {
    // SAFETY: same as `bf_putc`.
    u64::from(unsafe { &mut *io }.getc())
}

type BfFn = extern "C" fn(*mut u8, *mut Io);

struct Compiled {
    _span: Span,
    _jit: Box<JitAllocator>,
    entry: BfFn,
    code: Vec<u8>,
    addr: u64,
    target: Target,
}

fn compile(ops: &[Op]) -> Result<Compiled, Box<dyn std::error::Error>> {
    let mut asm = Assembler::native();
    let target = asm.target();
    // onlineasm has no aliases for argument registers, map them manually.
    // (see reference).
    let (arg0, arg1): (VReg, VReg) = match target {
        Target::X64 => (regs::t6, regs::t1),
        Target::AArch64 | Target::RISCV64 => (regs::t0, regs::t1),
    };

    // Frame: csr0 (tape pointer), csr1 (Io pointer), plus `lr` on targets
    // where `call` writes it.
    let frame: i32 = if target == Target::X64 { 24 } else { 32 };

    onlineasm!(asm;
        =>entry;
        subp sp, {frame};
        storeq [sp], csr0;
        storeq [sp + 8], csr1;
        move csr0, {arg0};
        move csr1, {arg1};
    );
    if target != Target::X64 {
        onlineasm!(asm; storeq [sp + 16], lr;);
    }

    // One (start, end) label pair per loop, indexed by `LoopStart`.
    let mut loop_labels: Vec<Option<(Label, Label)>> = vec![None; ops.len()];
    for (i, op) in ops.iter().enumerate() {
        match *op {
            Op::Add(n) => onlineasm!(asm;
                loadb t0, [csr0];
                addi t0, {n};
                storeb [csr0], t0;
            ),
            Op::Move(n) => onlineasm!(asm; addp csr0, {n as i64};),
            Op::Clear => onlineasm!(asm;
                move t0, 0;
                storeb [csr0], t0;
            ),
            Op::Output => onlineasm!(asm;
                loadb {arg1}, [csr0];
                move {arg0}, csr1;
                move t2, {bf_putc as *const () as u64};
                call t2;
            ),
            Op::Input => onlineasm!(asm;
                move {arg0}, csr1;
                move t2, {bf_getc as *const () as u64};
                call t2;
                storeb [csr0], t0;
            ),
            Op::LoopStart(_) => {
                let (start, end) = (asm.label(), asm.label());
                loop_labels[i] = Some((start, end));
                onlineasm!(asm;
                    loadb t0, [csr0];
                    btbz t0, {end};
                );
                asm.bind(start);
            }
            Op::LoopEnd(open) => {
                let (start, end) = loop_labels[open].ok_or("loop end before its start")?;
                onlineasm!(asm;
                    loadb t0, [csr0];
                    btbnz t0, {start};
                );
                asm.bind(end);
            }
        }
    }

    if target != Target::X64 {
        onlineasm!(asm; loadq lr, [sp + 16];);
    }
    onlineasm!(asm;
        loadq csr0, [sp];
        loadq csr1, [sp + 8];
        addp sp, {frame};
        ret;
    );

    let code = asm.finish()?;
    let offset = code.offset(entry).ok_or("entry is unbound")?;
    let mut jit = JitAllocator::new(Default::default());
    let span = code.allocate(&mut jit)?;
    // SAFETY: `entry` is the start of a function with the `BfFn` signature,
    // and the allocator that owns the mapping is stored next to it.
    let entry: BfFn = unsafe { std::mem::transmute(span.rx().add(offset as usize)) };
    let addr = span.rx() as u64;
    Ok(Compiled {
        _span: span,
        _jit: jit,
        entry,
        code: code.data().to_vec(),
        addr,
        target,
    })
}

fn run_jit(compiled: &Compiled, io: &mut Io) {
    let mut tape = vec![0u8; TAPE_LEN];
    (compiled.entry)(tape.as_mut_ptr(), io);
}

fn interpret(ops: &[Op], io: &mut Io) {
    let mut tape = vec![0u8; TAPE_LEN];
    let (mut ptr, mut pc) = (0usize, 0usize);
    while pc < ops.len() {
        match ops[pc] {
            Op::Add(n) => tape[ptr] = tape[ptr].wrapping_add(n),
            Op::Move(n) => ptr = ptr.wrapping_add_signed(n),
            Op::Clear => tape[ptr] = 0,
            Op::Output => io.putc(tape[ptr]),
            Op::Input => tape[ptr] = io.getc(),
            Op::LoopStart(end) if tape[ptr] == 0 => pc = end,
            Op::LoopEnd(start) if tape[ptr] != 0 => pc = start,
            Op::LoopStart(_) | Op::LoopEnd(_) => {}
        }
        pc += 1;
    }
}

fn disasm(target: Target, code: &[u8], addr: u64) -> CsResult<()> {
    let cs = match target {
        Target::X64 => Capstone::new()
            .x86()
            .mode(arch::x86::ArchMode::Mode64)
            .build(),
        Target::AArch64 => Capstone::new()
            .arm64()
            .mode(arch::arm64::ArchMode::Arm)
            .build(),
        Target::RISCV64 => Capstone::new()
            .riscv()
            .mode(arch::riscv::ArchMode::RiscV64)
            .extra_mode([arch::riscv::ArchExtraMode::RiscVC].into_iter())
            .build(),
    }?;
    for insn in cs.disasm_all(code, addr)?.iter() {
        let bytes: String = insn.bytes().iter().map(|b| format!("{b:02x}")).collect();
        eprintln!(
            "{:#014x}  {bytes:<20} {:<8} {}",
            insn.address(),
            insn.mnemonic().unwrap_or("?"),
            insn.op_str().unwrap_or(""),
        );
    }
    Ok(())
}

const USAGE: &str = "usage: bf_jit [--interpreter] [--stats] [--disasm] <program.bf>";

fn main() {
    if let Err(e) = run() {
        eprintln!("bf_jit: {e}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let (mut use_interpreter, mut stats, mut show_disasm, mut path) = (false, false, false, None);
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--interpreter" => use_interpreter = true,
            "--stats" => stats = true,
            "--disasm" => show_disasm = true,
            "-h" | "--help" => {
                println!("{USAGE}");
                return Ok(());
            }
            _ if arg.starts_with('-') || path.is_some() => return Err(USAGE.into()),
            _ => path = Some(arg),
        }
    }
    let path = path.ok_or(USAGE)?;
    let src = std::fs::read_to_string(&path).map_err(|e| format!("{path}: {e}"))?;
    let ops = parse(&src)?;
    let mut io = Io::new();

    let t = Instant::now();
    let compiled = if use_interpreter {
        None
    } else {
        Some(compile(&ops)?)
    };
    let compile_time = t.elapsed();
    if let Some(c) = compiled.as_ref().filter(|_| show_disasm) {
        disasm(c.target, &c.code, c.addr)?;
    }

    let t = Instant::now();
    match &compiled {
        None => interpret(&ops, &mut io),
        Some(compiled) => run_jit(compiled, &mut io),
    }
    io.output.flush()?;
    let run_time = t.elapsed();

    if stats {
        eprintln!("ops:     {}", ops.len());
        if let Some(compiled) = &compiled {
            eprintln!("code:    {} bytes", compiled.code.len());
            eprintln!("compile: {compile_time:?}");
        }
        eprintln!(
            "run:     {run_time:?} ({})",
            if use_interpreter {
                "interpreter"
            } else {
                "jit"
            }
        );
    }
    Ok(())
}
