//! A low-level bytecode interpreter with indirect (token) threaded and direct
//! threaded dispatch.
//!
//!
//! Needs nightly for `rust_preserve_none_cc` (the rloop backend).
#![feature(rust_preserve_none_cc)]

use std::sync::Mutex;
use std::time::{Duration, Instant};

mod native {
    offlineasm::offlineasm!(settings { backend = native } "examples/llint/llint.asm");

    extern "C" {
        pub fn llint_entry(code: *mut u64, context: *mut super::Context, threaded: u64) -> u64;
    }
}

mod rloop {
    use offlineasm::rt::*;

    offlineasm::offlineasm!(settings { backend = rloop } "examples/llint/llint.asm");

    pub use offlineasm_rloop_config_0::{InterpretedCode, Opcode};

    pub struct Host;

    impl InterpretedCode for Host {
        unsafe fn call_native(&mut self, _m: &mut Machine, target: u64, a0: u64, a1: u64) -> u64 {
            let f: extern "C" fn(u64, u64) -> u64 = unsafe { core::mem::transmute(target) };
            f(a0, a1)
        }
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(u64)]
enum Op {
    Enter = 0,
    Movi,
    Mov,
    Add,
    Sub,
    Mul,
    Jlt,
    Jmp,
    Call,
    Ret,
    Print,
}

const NUM_OPCODES: usize = 11;

impl Op {
    fn len(self) -> usize {
        match self {
            Op::Enter | Op::Jmp | Op::Ret | Op::Print => 2,
            Op::Movi | Op::Mov => 3,
            Op::Add | Op::Sub | Op::Mul | Op::Jlt => 4,
            Op::Call => 5,
        }
    }
}

#[repr(C)]
struct Context {
    token_table: [u64; NUM_OPCODES],
    threaded_table: [u64; NUM_OPCODES],
    lengths: [u64; NUM_OPCODES],
    host_print: u64,
    code_words: u64,
}

impl Context {
    fn new(code_words: usize) -> Self {
        Self {
            token_table: [0; NUM_OPCODES],
            threaded_table: [0; NUM_OPCODES],
            lengths: [0; NUM_OPCODES],
            host_print: host_print as *const () as u64,
            code_words: code_words as u64,
        }
    }
}

static PRINTED: Mutex<Vec<u64>> = Mutex::new(Vec::new());

extern "C" fn host_print(value: u64, _unused: u64) -> u64 {
    PRINTED.lock().expect("print log").push(value);
    0
}

fn r(n: u64) -> u64 {
    (-8 * (n as i64 + 1) - 16) as u64
}

#[derive(Clone, Copy)]
struct Label(usize);

#[derive(Default)]
struct Builder {
    code: Vec<u64>,
    bound: Vec<Option<usize>>,
    fixups: Vec<(usize, usize, Label)>,
}

enum Operand {
    Word(u64),
    To(Label),
}
use Operand::{To, Word};

impl Builder {
    fn label(&mut self) -> Label {
        self.bound.push(None);
        Label(self.bound.len() - 1)
    }

    fn bind(&mut self, l: Label) {
        self.bound[l.0] = Some(self.code.len());
    }

    fn emit(&mut self, op: Op, operands: &[Operand]) {
        assert_eq!(operands.len() + 1, op.len(), "{op:?} operand count");
        let start = self.code.len();
        self.code.push(op as u64);
        for operand in operands {
            match *operand {
                Word(w) => self.code.push(w),
                To(l) => {
                    self.fixups.push((start, self.code.len(), l));
                    self.code.push(0);
                }
            }
        }
    }

    fn finish(mut self) -> Vec<u64> {
        for (start, at, l) in self.fixups {
            let target = self.bound[l.0].expect("label bound");
            self.code[at] = (target as i64 - start as i64) as u64;
        }
        self.code
    }
}

fn program(n: u64, limit: u64) -> Vec<u64> {
    let mut b = Builder::default();
    let fib = b.label();

    // main: r0 = n, r1 = fib(n), r2 = sum, r3 = i, r4 = bound, r5 = 1,
    // r6 = factorial, r7 = copy of fib(n)
    b.emit(Op::Enter, &[Word(8)]);
    b.emit(Op::Movi, &[Word(r(0)), Word(n)]);
    b.emit(Op::Call, &[Word(r(1)), To(fib), Word(1), Word(r(0))]);
    b.emit(Op::Mov, &[Word(r(7)), Word(r(1))]);
    b.emit(Op::Print, &[Word(r(7))]);
    b.emit(Op::Movi, &[Word(r(2)), Word(0)]);
    b.emit(Op::Movi, &[Word(r(3)), Word(1)]);
    b.emit(Op::Movi, &[Word(r(4)), Word(limit + 1)]);
    b.emit(Op::Movi, &[Word(r(5)), Word(1)]);
    let body = b.label();
    b.bind(body);
    b.emit(Op::Add, &[Word(r(2)), Word(r(2)), Word(r(3))]);
    b.emit(Op::Add, &[Word(r(3)), Word(r(3)), Word(r(5))]);
    b.emit(Op::Jlt, &[Word(r(3)), Word(r(4)), To(body)]);
    b.emit(Op::Print, &[Word(r(2))]);

    // 20!, as a while loop: jump to the test first.
    let (test, again) = (b.label(), b.label());
    b.emit(Op::Movi, &[Word(r(6)), Word(1)]);
    b.emit(Op::Movi, &[Word(r(3)), Word(1)]);
    b.emit(Op::Movi, &[Word(r(4)), Word(21)]);
    b.emit(Op::Jmp, &[To(test)]);
    b.bind(again);
    b.emit(Op::Mul, &[Word(r(6)), Word(r(6)), Word(r(3))]);
    b.emit(Op::Add, &[Word(r(3)), Word(r(3)), Word(r(5))]);
    b.bind(test);
    b.emit(Op::Jlt, &[Word(r(3)), Word(r(4)), To(again)]);
    b.emit(Op::Print, &[Word(r(6))]);

    b.emit(Op::Add, &[Word(r(1)), Word(r(1)), Word(r(2))]);
    b.emit(Op::Ret, &[Word(r(1))]);

    // fib: r0 = n, r1 = scratch, r2 = 2, r3 = fib(n - 1), r4 = fib(n - 2)
    let base = b.label();
    b.bind(fib);
    b.emit(Op::Enter, &[Word(5)]);
    b.emit(Op::Movi, &[Word(r(2)), Word(2)]);
    b.emit(Op::Jlt, &[Word(r(0)), Word(r(2)), To(base)]);
    b.emit(Op::Movi, &[Word(r(1)), Word(1)]);
    b.emit(Op::Sub, &[Word(r(1)), Word(r(0)), Word(r(1))]);
    b.emit(Op::Call, &[Word(r(3)), To(fib), Word(1), Word(r(1))]);
    b.emit(Op::Sub, &[Word(r(1)), Word(r(0)), Word(r(2))]);
    b.emit(Op::Call, &[Word(r(4)), To(fib), Word(1), Word(r(1))]);
    b.emit(Op::Add, &[Word(r(3)), Word(r(3)), Word(r(4))]);
    b.emit(Op::Ret, &[Word(r(3))]);
    b.bind(base);
    b.emit(Op::Ret, &[Word(r(0))]);

    b.finish()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    Native,
    Rloop,
}

fn run(backend: Backend, threaded: bool, code: &[u64]) -> (u64, Vec<u64>, Duration) {
    let mut code = code.to_vec();
    let mut context = Context::new(code.len());
    PRINTED.lock().expect("print log").clear();
    let start = Instant::now();
    let result = match backend {
        Backend::Native => {
            // SAFETY: `code` is a complete program for this interpreter and
            // `context` is laid out as `llint.asm` expects.
            unsafe { native::llint_entry(code.as_mut_ptr(), &mut context, threaded as u64) }
        }
        Backend::Rloop => {
            use offlineasm::rt::Machine;
            use rloop::InterpretedCode;
            // rloop has no machine stack of its own: `sp` and `cfr` point
            // into this one.
            let mut stack = vec![0u64; 1 << 20];
            let top = stack.as_mut_ptr_range().end as u64 & !15;
            let mut m = Machine::new();
            m.regs.t0 = code.as_mut_ptr() as u64;
            m.regs.t1 = &mut context as *mut Context as u64;
            m.regs.t2 = threaded as u64;
            m.regs.sp = top;
            let stopped = rloop::Host.run(&mut m);
            assert_eq!(stopped, rloop::Opcode::Done);
            assert_eq!(m.regs.sp, top, "the interpreter rebalanced the stack");
            m.regs.t0
        }
    };
    let elapsed = start.elapsed();
    let printed = std::mem::take(&mut *PRINTED.lock().expect("print log"));
    (result, printed, elapsed)
}

fn fib(n: u64) -> u64 {
    if n < 2 {
        n
    } else {
        fib(n - 1) + fib(n - 2)
    }
}

fn main() {
    let (n, limit) = (24, 1_000_000);
    let code = program(n, limit);
    let expected = [fib(n), limit * (limit + 1) / 2, (1..=20).product()];
    println!(
        "{} words of bytecode, fib({n}) = {}, sum(1..={limit}) = {}, 20! = {}",
        code.len(),
        expected[0],
        expected[1],
        expected[2],
    );

    for backend in [Backend::Native, Backend::Rloop] {
        for threaded in [false, true] {
            let (result, printed, time) = run(backend, threaded, &code);
            assert_eq!(printed, expected, "{backend:?} threaded={threaded}");
            assert_eq!(result, expected[0] + expected[1]);
            let style = if threaded {
                "direct threaded"
            } else {
                "token threaded"
            };
            println!("{backend:?}, {style:<15} {time:>12.3?}");
        }
    }
}
