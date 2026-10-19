use super::text::{self, TextTarget};
use super::LowerCtx;
use crate::ast::Node;
use offlineasm_ir::{
    op_eq, Alu3, AluOp, AtomicOp, BitcastDir, Disp, Extern, FAlu, FArith3, FCc, FKind, FlagAlu,
    FmaOp, Fpr, Gpr, Inst, IntCc, Lbl, LeaSrc, Mem, Mnemonic, Op, PairW, PredFlag, Reach,
    RoundMode, ShiftCnt, ShiftOp, Sx, Target, TestKind, Width,
};

type LabelFlags<'a> = &'a dyn Fn(&str) -> (bool, bool, bool, bool, Option<String>);

/// The `t0` accumulator role (`x0`): dividend/quotient, CAS expected value.
const T0: Gpr = Gpr(0);
/// The `t2` accumulator role (`x2`): multiply high half, CAS old value.
const T2: Gpr = Gpr(2);
/// Address and immediate synthesis scratch.
const SCRATCH: Gpr = Gpr(16);
/// Second synthesis scratch.
const SCRATCH2: Gpr = Gpr(17);
/// Float/vector synthesis scratch.
const FSCRATCH: Fpr = Fpr(31);
/// The stack pointer.
const SP: Gpr = Gpr(31);

fn gpr(g: Gpr, w: Width) -> Result<String, String> {
    let wide = w == Width::B64;
    Ok(match g.0 {
        31 => if wide { "sp" } else { "wsp" }.to_string(),
        63 => if wide { "xzr" } else { "wzr" }.to_string(),
        n @ 0..=30 => format!("{}{}", if wide { 'x' } else { 'w' }, n),
        n => return Err(format!("aarch64: register id {} is out of range", n)),
    })
}

pub(super) fn stack_group(ctx: &mut LowerCtx, mn: Mnemonic, ops: &[Op]) -> Result<(), String> {
    let push = matches!(mn, Mnemonic::Push | Mnemonic::PushCalleeSaves);
    let n = ops.len();
    if n == 0 {
        return Err(format!("{mn}: needs at least one operand"));
    }
    let bytes = offlineasm_ir::aligned_push_bytes(n);
    if bytes > 512 {
        return Err(format!(
            "{mn}: too many operands for one aarch64 stack block"
        ));
    }
    for op in ops {
        match op {
            Op::Gpr(SP) => return Err(format!("{mn}: aarch64 cannot push or pop `sp`")),
            Op::Gpr(_) => {}
            Op::Imm(_) if push => {}
            Op::Mem(m) if m.base == Some(SP) || m.index.is_some_and(|(i, _)| i == SP) => {
                return Err(format!(
                    "{mn}: `sp`-relative memory operands are not supported on aarch64"
                ))
            }
            Op::Mem(_) => {}
            other => return Err(format!("{mn}: unsupported operand {other:?}")),
        }
    }
    let off = |i: usize| offlineasm_ir::aligned_push_offset(n, i);
    let mut units: Vec<(usize, Option<usize>)> = Vec::new();
    let mut i = n;
    while i >= 2 {
        units.push((i - 1, Some(i - 2)));
        i -= 2;
    }
    if i == 1 {
        units.push((0, None));
    }

    if push {
        for (k, &(lo, hi)) in units.iter().enumerate() {
            let r_hi = match hi {
                Some(h) => Some(op_to_reg(ctx, &ops[h], Width::B64, SCRATCH2)?),
                None => None,
            };
            let r_lo = op_to_reg(ctx, &ops[lo], Width::B64, SCRATCH)?;
            let addr = if k == 0 {
                format!("[sp, #-{bytes}]!")
            } else {
                format!("[sp, #{}]", off(lo))
            };
            ctx.emitter.puts(&match r_hi {
                Some(r_hi) => format!("stp {r_lo}, {r_hi}, {addr}"),
                None => format!("str {r_lo}, {addr}"),
            });
        }
        return Ok(());
    }

    for (k, &(lo, hi)) in units.iter().enumerate().rev() {
        let last = k == 0;
        let pair = hi.and_then(|h| match (&ops[lo], &ops[h]) {
            (Op::Gpr(a), Op::Gpr(b)) if a != b => Some((*a, *b)),
            _ => None,
        });
        if let Some((a, b)) = pair {
            let (a, b) = (gpr(a, Width::B64)?, gpr(b, Width::B64)?);
            let addr = if last {
                format!("[sp], #{bytes}")
            } else {
                format!("[sp, #{}]", off(lo))
            };
            ctx.emitter.puts(&format!("ldp {a}, {b}, {addr}"));
            continue;
        }
        if let (None, Op::Gpr(g), true) = (hi, &ops[lo], last) {
            let r = gpr(*g, Width::B64)?;
            ctx.emitter.puts(&format!("ldr {r}, [sp], #{bytes}"));
            continue;
        }

        for idx in hi.into_iter().chain(std::iter::once(lo)) {
            let slot = format!("[sp, #{}]", off(idx));
            match &ops[idx] {
                Op::Gpr(g) => {
                    let r = gpr(*g, Width::B64)?;
                    ctx.emitter.puts(&format!("ldr {r}, {slot}"));
                }
                Op::Mem(m) => {
                    let t = gpr(SCRATCH2, Width::B64)?;
                    ctx.emitter.puts(&format!("ldr {t}, {slot}"));
                    let addr = addr_operand(ctx, m, 8)?;
                    ctx.emitter.puts(&format!("str {t}, {addr}"));
                }
                _ => unreachable!("operands were checked above"),
            }
        }
        if last {
            ctx.emitter.puts(&format!("add sp, sp, #{bytes}"));
        }
    }
    Ok(())
}

fn fpr(f: Fpr, k: FKind) -> String {
    match k {
        FKind::F32 => format!("s{}", f.0),
        FKind::F64 => format!("d{}", f.0),
    }
}

fn vreg(f: Fpr) -> String {
    format!("v{}", f.0)
}

fn qreg(f: Fpr) -> String {
    format!("q{}", f.0)
}

fn view(w: Width) -> Width {
    if w == Width::B64 {
        Width::B64
    } else {
        Width::B32
    }
}

fn load_mnemonic(w: Width) -> &'static str {
    match w {
        Width::B8 => "ldrb",
        Width::B16 => "ldrh",
        Width::B32 | Width::B64 => "ldr",
    }
}

fn store_mnemonic(w: Width) -> &'static str {
    match w {
        Width::B8 => "strb",
        Width::B16 => "strh",
        Width::B32 | Width::B64 => "str",
    }
}

/// Materialize `v` into the `x`/`w` register named `reg`.
fn mov_imm(ctx: &mut LowerCtx, reg: &str, wide: bool, v: i64) -> Result<(), String> {
    let uval: u64 = if wide { v as u64 } else { u64::from(v as u32) };
    let shifts: &[u32] = if wide { &[48, 32, 16, 0] } else { &[16, 0] };
    let mut ones = 0usize;
    let mut zeros = 0usize;
    for &shift in shifts {
        let chunk = (uval >> shift) & 0xffff;
        if chunk == 0xffff {
            ones += 1;
        } else if chunk == 0 {
            zeros += 1;
        }
    }

    let fill_ones = ones > zeros;
    let neutral = if fill_ones { 0xffff } else { 0 };
    let mut first = true;
    for &shift in shifts {
        let chunk = (uval >> shift) & 0xffff;
        if chunk == neutral && (shift != 0 || !first) {
            continue;
        }
        let line = if first {
            first = false;
            if fill_ones {
                let inv = (!chunk) & 0xffff;
                if shift == 0 {
                    format!("movn {}, #{}", reg, inv)
                } else {
                    format!("movn {}, #{}, lsl #{}", reg, inv, shift)
                }
            } else if shift == 0 {
                format!("movz {}, #{}", reg, chunk)
            } else {
                format!("movz {}, #{}, lsl #{}", reg, chunk, shift)
            }
        } else if shift == 0 {
            format!("movk {}, #{}", reg, chunk)
        } else {
            format!("movk {}, #{}, lsl #{}", reg, chunk, shift)
        };
        ctx.emitter.puts(&line);
    }
    Ok(())
}

/// Whether `v` is encodable as an AArch64 logical immediate.
fn fits_logical_imm(v: i64, wide: bool) -> bool {
    let target = if wide {
        u128::from(v as u64)
    } else {
        u128::from(v as u32)
    };
    let top: u32 = if wide { 64 } else { 32 };
    let mut size: u32 = 2;
    while size <= top {
        for length in 1..size {
            for rotation in 0..size {
                let mask: u128 = (1u128 << size) - 1;
                let base: u128 = (1u128 << length) - 1;
                let shifted = base << rotation;
                let rotated = (shifted & mask) | ((shifted & !mask) >> size);
                let mut replicated = rotated;
                let mut grown = size;
                while grown < 64 {
                    replicated |= replicated << grown;
                    grown *= 2;
                }
                if replicated == target {
                    return true;
                }
            }
        }
        size *= 2;
    }
    false
}

/// The immediate text of a logical operand (`#0xff`, `#0xffff0000`, and so on).
fn logical_imm_text(v: i64, wide: bool) -> String {
    if wide {
        format!("#0x{:x}", v as u64)
    } else {
        format!("#0x{:x}", v as u32)
    }
}

/// Fold a whole address (`base + index * scale + disp`) into [`SCRATCH`],
/// returning the scratch register's text.
fn synth_addr(ctx: &mut LowerCtx, m: &Mem) -> Result<String, String> {
    let Some(base) = m.base else {
        let t = gpr(SCRATCH, Width::B64)?;
        if let Disp::Sym(s) = m.disp {
            let text = text::sym_text(ctx, s)?;
            ctx.emitter.puts(&format!("ldr {}, ={}", t, text));
            return add_index(ctx, &t, m);
        }
        mov_imm(ctx, &t, true, m.disp.const_or_zero() as i64)?;
        return add_index(ctx, &t, m);
    };
    let b = gpr(base, Width::B64)?;
    let t = gpr(SCRATCH, Width::B64)?;
    let disp = match m.disp {
        Disp::Const(disp) => disp,
        Disp::Sym(_) => {
            return Err("aarch64: a symbolic displacement needs a base-only address".to_string())
        }
    };
    let magnitude = u64::from(disp.unsigned_abs());
    if magnitude == 0 {
        if b != t {
            ctx.emitter.puts(&format!("mov {}, {}", t, b));
        }
    } else if magnitude <= 4095 {
        let mnemonic = if disp >= 0 { "add" } else { "sub" };
        ctx.emitter
            .puts(&format!("{} {}, {}, #{}", mnemonic, t, b, magnitude));
    } else {
        mov_imm(ctx, &t, true, i64::from(disp))?;
        ctx.emitter.puts(&format!("add {}, {}, {}", t, b, t));
    }
    add_index(ctx, &t, m)
}

/// Add `index * scale` (if any) to the register named `t`.
fn add_index(ctx: &mut LowerCtx, t: &str, m: &Mem) -> Result<String, String> {
    if let Some((index, scale)) = m.index {
        let shift = match scale {
            1 => 0,
            2 => 1,
            4 => 2,
            8 => 3,
            other => return Err(format!("aarch64: bad address scale {}", other)),
        };
        let i = gpr(index, Width::B64)?;
        if shift == 0 {
            ctx.emitter.puts(&format!("add {}, {}, {}", t, t, i));
        } else {
            ctx.emitter
                .puts(&format!("add {}, {}, {}, lsl #{}", t, t, i, shift));
        }
    }
    Ok(t.to_string())
}

/// The text of a memory operand for an access of `size` bytes: a direct
/// `[base, #disp]` / `[base, index, lsl #s]` / `[base, #{sym}]` form
/// whenever the ISA can encode it, else the address folded into
/// [`SCRATCH`].
fn addr_operand(ctx: &mut LowerCtx, m: &Mem, size: u32) -> Result<String, String> {
    let Some(base) = m.base else {
        // Absolute address: materialize the value into scratch.
        let t = synth_addr(ctx, m)?;
        return Ok(format!("[{}]", t));
    };
    let b = gpr(base, Width::B64)?;
    match (m.index, m.disp) {
        (None, Disp::Const(0)) => Ok(format!("[{}]", b)),
        (None, Disp::Const(disp)) => {
            let scaled =
                disp >= 0 && size != 0 && disp % size as i32 == 0 && disp < 4096 * size as i32;
            if scaled || (-256..=255).contains(&disp) {
                Ok(format!("[{}, #{}]", b, disp))
            } else {
                let t = synth_addr(ctx, m)?;
                Ok(format!("[{}]", t))
            }
        }
        (None, Disp::Sym(s)) => {
            let text = text::sym_text(ctx, s)?;
            Ok(format!("[{}, #{}]", b, text))
        }
        (Some((index, scale)), Disp::Const(0)) => {
            let shift = if scale == 1 {
                Some(0)
            } else if u32::from(scale) == size && size.is_power_of_two() {
                Some(size.trailing_zeros())
            } else {
                None
            };
            match shift {
                Some(shift) => {
                    let i = gpr(index, Width::B64)?;
                    Ok(if shift == 0 {
                        format!("[{}, {}]", b, i)
                    } else {
                        format!("[{}, {}, lsl #{}]", b, i, shift)
                    })
                }
                None => {
                    let t = synth_addr(ctx, m)?;
                    Ok(format!("[{}]", t))
                }
            }
        }
        (Some(_), _) => {
            let t = synth_addr(ctx, m)?;
            Ok(format!("[{}]", t))
        }
    }
}

fn addr_base_only(ctx: &mut LowerCtx, m: &Mem) -> Result<String, String> {
    if m.index.is_none() && matches!(m.disp, Disp::Const(0)) {
        if let Some(base) = m.base {
            let b = gpr(base, Width::B64)?;
            return Ok(format!("[{}]", b));
        }
    }
    let t = synth_addr(ctx, m)?;
    Ok(format!("[{}]", t))
}

fn pair_addr_operand(ctx: &mut LowerCtx, m: &Mem, scale: i64) -> Result<String, String> {
    if m.base.is_none() {
        let t = synth_addr(ctx, m)?;
        return Ok(format!("[{}]", t));
    }
    let base = m.base_reg();
    if m.index.is_none() {
        if let Disp::Const(disp) = m.disp {
            let disp = i64::from(disp);
            if disp % scale == 0 && (-64 * scale..64 * scale).contains(&disp) {
                let b = gpr(base, Width::B64)?;
                return Ok(format!("[{}, #{}]", b, disp));
            }
        }
    }
    let t = synth_addr(ctx, m)?;
    Ok(format!("[{}]", t))
}

fn op_to_reg(ctx: &mut LowerCtx, op: &Op, w: Width, scratch: Gpr) -> Result<String, String> {
    let vw = view(w);
    match op {
        Op::Gpr(g) => gpr(*g, vw),
        Op::Imm(v) => {
            let r = gpr(scratch, vw)?;
            mov_imm(ctx, &r, vw == Width::B64, *v)?;
            Ok(r)
        }
        Op::Mem(m) => {
            let r = gpr(scratch, vw)?;
            let addr = addr_operand(ctx, m, w.bytes())?;
            ctx.emitter
                .puts(&format!("{} {}, {}", load_mnemonic(w), r, addr));
            Ok(r)
        }
        Op::Sym(s) => {
            let r = gpr(scratch, vw)?;
            let text = text::sym_text(ctx, *s)?;
            ctx.emitter.puts(&format!("mov {}, #{}", r, text));
            Ok(r)
        }
        other => Err(format!(
            "aarch64: operand {:?} cannot be loaded into a register",
            other
        )),
    }
}

fn into_reg(ctx: &mut LowerCtx, op: &Op, w: Width, scratch: Gpr) -> Result<String, String> {
    let r = gpr(scratch, view(w))?;
    load_into(ctx, op, &r, w)?;
    Ok(r)
}

fn load_into(ctx: &mut LowerCtx, op: &Op, dst: &str, w: Width) -> Result<(), String> {
    let vw = view(w);
    match op {
        Op::Gpr(g) => {
            let s = gpr(*g, vw)?;
            if s != dst {
                ctx.emitter.puts(&format!("mov {}, {}", dst, s));
            }
            Ok(())
        }
        Op::Imm(v) => mov_imm(ctx, dst, vw == Width::B64, *v),
        Op::Mem(m) => {
            let addr = addr_operand(ctx, m, w.bytes())?;
            ctx.emitter
                .puts(&format!("{} {}, {}", load_mnemonic(w), dst, addr));
            Ok(())
        }
        Op::Sym(s) => {
            let text = text::sym_text(ctx, *s)?;
            ctx.emitter.puts(&format!("mov {}, #{}", dst, text));
            Ok(())
        }
        other => Err(format!(
            "aarch64: operand {:?} cannot be loaded into a register",
            other
        )),
    }
}

fn fp_src_id(ctx: &mut LowerCtx, k: FKind, op: &Op) -> Result<Fpr, String> {
    match op {
        Op::Fpr(f) => Ok(*f),
        Op::Mem(m) => {
            let addr = addr_operand(ctx, m, if k == FKind::F32 { 4 } else { 8 })?;
            ctx.emitter
                .puts(&format!("ldr {}, {}", fpr(FSCRATCH, k), addr));
            Ok(FSCRATCH)
        }
        Op::Imm(v) => {
            let wide = k != FKind::F32;
            let t = gpr(SCRATCH, if wide { Width::B64 } else { Width::B32 })?;
            mov_imm(ctx, &t, wide, *v)?;
            ctx.emitter
                .puts(&format!("fmov {}, {}", fpr(FSCRATCH, k), t));
            Ok(FSCRATCH)
        }
        other => Err(format!(
            "aarch64: operand {:?} cannot be loaded into a float register",
            other
        )),
    }
}

fn fp_src(ctx: &mut LowerCtx, k: FKind, op: &Op) -> Result<String, String> {
    fp_src_id(ctx, k, op).map(|f| fpr(f, k))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AluKind {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
}

impl AluKind {
    fn base(self) -> &'static str {
        match self {
            AluKind::Add => "add",
            AluKind::Sub => "sub",
            AluKind::Mul => "mul",
            AluKind::And => "and",
            AluKind::Or => "orr",
            AluKind::Xor => "eor",
        }
    }

    fn mnemonic(self, sf: bool) -> String {
        if sf && matches!(self, AluKind::Add | AluKind::Sub) {
            format!("{}s", self.base())
        } else {
            self.base().to_string()
        }
    }

    fn commutative(self) -> bool {
        self != AluKind::Sub
    }
}

fn alu_reg_sp_rhs(
    ctx: &mut LowerCtx,
    k: AluKind,
    w: Width,
    dst: &str,
    tmp: Gpr,
    sf: bool,
) -> Result<(), String> {
    let vw = view(w);
    let mnemonic = k.mnemonic(sf);
    let spname = gpr(SP, vw)?;
    match k {
        AluKind::Add => {
            ctx.emitter
                .puts(&format!("{} {}, {}, {}", mnemonic, dst, spname, dst));
            Ok(())
        }
        AluKind::Sub => {
            let t = gpr(tmp, vw)?;
            ctx.emitter.puts(&format!("mov {}, {}", t, spname));
            ctx.emitter
                .puts(&format!("{} {}, {}, {}", mnemonic, dst, dst, t));
            Ok(())
        }
        _ => unreachable!("alu_reg_sp_rhs only handles Add/Sub"),
    }
}

fn alu_reg(
    ctx: &mut LowerCtx,
    k: AluKind,
    w: Width,
    dst: &str,
    rhs: &Op,
    tmp: Gpr,
    sf: bool,
) -> Result<(), String> {
    let vw = view(w);
    let mnemonic = k.mnemonic(sf);
    match rhs {
        Op::Gpr(g) if *g == SP && matches!(k, AluKind::Add | AluKind::Sub) => {
            alu_reg_sp_rhs(ctx, k, w, dst, tmp, sf)
        }
        Op::Gpr(g) => {
            let s = gpr(*g, vw)?;
            ctx.emitter
                .puts(&format!("{} {}, {}, {}", mnemonic, dst, dst, s));
            Ok(())
        }
        Op::Sym(s) => {
            let text = text::sym_text(ctx, *s)?;
            ctx.emitter
                .puts(&format!("{} {}, {}, #{}", mnemonic, dst, dst, text));
            Ok(())
        }
        Op::Imm(v) => {
            match k {
                AluKind::Add | AluKind::Sub => {
                    let use_sub = if k == AluKind::Add { *v < 0 } else { *v >= 0 };
                    let magnitude = v.unsigned_abs();
                    if magnitude <= 4095 {
                        let base = if use_sub { "sub" } else { "add" };
                        let mnemonic = if sf {
                            format!("{}s", base)
                        } else {
                            base.to_string()
                        };
                        ctx.emitter
                            .puts(&format!("{} {}, {}, #{}", mnemonic, dst, dst, magnitude));
                        return Ok(());
                    }
                }
                AluKind::And | AluKind::Or | AluKind::Xor => {
                    if fits_logical_imm(*v, vw == Width::B64) {
                        let text = logical_imm_text(*v, vw == Width::B64);
                        ctx.emitter
                            .puts(&format!("{} {}, {}, {}", mnemonic, dst, dst, text));
                        return Ok(());
                    }
                }
                AluKind::Mul => {}
            }
            let s = op_to_reg(ctx, rhs, w, tmp)?;
            ctx.emitter
                .puts(&format!("{} {}, {}, {}", mnemonic, dst, dst, s));
            Ok(())
        }
        Op::Mem(_) => {
            let s = op_to_reg(ctx, rhs, w, tmp)?;
            ctx.emitter
                .puts(&format!("{} {}, {}, {}", mnemonic, dst, dst, s));
            Ok(())
        }
        other => Err(format!("aarch64: ALU operand {:?} is not usable", other)),
    }
}

fn three_op_direct(
    k: AluKind,
    w: Width,
    left: &Op,
    right: &Op,
) -> Option<(String, String, String)> {
    let vw = view(w);
    let wide = vw == Width::B64;
    let reg = |op: &Op| match op {
        Op::Gpr(g) => gpr(*g, vw).ok(),
        _ => None,
    };
    if let (Some(l), Some(r)) = (reg(left), reg(right)) {
        if matches!(k, AluKind::Add | AluKind::Sub) && matches!(right, Op::Gpr(g) if *g == SP) {
            return match k {
                AluKind::Add => Some((k.base().to_string(), r, l)),
                AluKind::Sub => None,
                _ => unreachable!(),
            };
        }
        return Some((k.base().to_string(), l, r));
    }
    match k {
        AluKind::Add | AluKind::Sub => {
            let (imm, other, left_is_imm) = match (left, right) {
                (Op::Imm(v), other) => (*v, other, true),
                (other, Op::Imm(v)) => (*v, other, false),
                _ => return None,
            };
            if !(0..=4095).contains(&imm) || (left_is_imm && k == AluKind::Sub) {
                return None;
            }
            let other = reg(other)?;
            let immediate = format!("#{}", imm);
            Some((k.base().to_string(), other, immediate))
        }
        AluKind::And | AluKind::Or | AluKind::Xor => {
            let (imm, other) = match (left, right) {
                (Op::Imm(v), other) => (*v, other),
                (other, Op::Imm(v)) => (*v, other),
                _ => return None,
            };
            if !fits_logical_imm(imm, wide) {
                return None;
            }
            Some((
                k.base().to_string(),
                reg(other)?,
                logical_imm_text(imm, wide),
            ))
        }
        AluKind::Mul => None,
    }
}

fn alu(ctx: &mut LowerCtx, k: AluKind, w: Width, shape: &Alu3, sf: bool) -> Result<(), String> {
    match &shape.dst {
        Op::Gpr(dst) => {
            let d = gpr(*dst, view(w))?;
            if op_eq(&shape.lhs, &shape.dst) {
                return alu_reg(ctx, k, w, &d, &shape.rhs, SCRATCH2, sf);
            }
            if op_eq(&shape.rhs, &shape.dst) {
                if k.commutative() {
                    return alu_reg(ctx, k, w, &d, &shape.lhs, SCRATCH2, sf);
                }
                let t = gpr(SCRATCH2, view(w))?;
                ctx.emitter.puts(&format!("mov {}, {}", t, d));
                load_into(ctx, &shape.lhs, &d, w)?;
                return alu_reg(ctx, k, w, &d, &Op::Gpr(SCRATCH2), SCRATCH, sf);
            }
            if let Some((mnemonic, l, r)) = three_op_direct(k, w, &shape.lhs, &shape.rhs) {
                let flags = if sf && matches!(k, AluKind::Add | AluKind::Sub) {
                    "s"
                } else {
                    ""
                };
                ctx.emitter
                    .puts(&format!("{}{} {}, {}, {}", mnemonic, flags, d, l, r));
                return Ok(());
            }
            load_into(ctx, &shape.lhs, &d, w)?;
            alu_reg(ctx, k, w, &d, &shape.rhs, SCRATCH2, sf)
        }
        Op::Mem(m) => {
            let v = gpr(SCRATCH2, view(w))?;
            load_into(ctx, &shape.lhs, &v, w)?;
            alu_reg(ctx, k, w, &v, &shape.rhs, SCRATCH, sf)?;
            let addr = addr_operand(ctx, m, w.bytes())?;
            ctx.emitter
                .puts(&format!("{} {}, {}", store_mnemonic(w), v, addr));
            Ok(())
        }
        other => Err(format!(
            "aarch64: ALU destination {:?} is not usable",
            other
        )),
    }
}

fn alu3_from_args(args: &[Op]) -> Option<Alu3> {
    match args {
        [rhs, dst] => Some(Alu3 {
            dst: *dst,
            lhs: *dst,
            rhs: *rhs,
        }),
        [lhs, rhs, dst] => Some(Alu3 {
            dst: *dst,
            lhs: *lhs,
            rhs: *rhs,
        }),
        _ => None,
    }
}

fn int_cc(cc: IntCc) -> &'static str {
    match cc {
        IntCc::Eq => "eq",
        IntCc::Ne => "ne",
        IntCc::Hi => "hi",
        IntCc::Hs => "hs",
        IntCc::Lo => "lo",
        IntCc::Ls => "ls",
        IntCc::Gt => "gt",
        IntCc::Ge => "ge",
        IntCc::Lt => "lt",
        IntCc::Le => "le",
    }
}

fn flip_cc(cc: IntCc) -> IntCc {
    match cc {
        IntCc::Eq => IntCc::Eq,
        IntCc::Ne => IntCc::Ne,
        IntCc::Hi => IntCc::Lo,
        IntCc::Hs => IntCc::Ls,
        IntCc::Lo => IntCc::Hi,
        IntCc::Ls => IntCc::Hs,
        IntCc::Gt => IntCc::Lt,
        IntCc::Ge => IntCc::Le,
        IntCc::Lt => IntCc::Gt,
        IntCc::Le => IntCc::Ge,
    }
}

fn flag_cc(flag: PredFlag) -> &'static str {
    match flag {
        PredFlag::O => "vs",
        PredFlag::S => "mi",
        PredFlag::Z => "eq",
        PredFlag::Nz => "ne",
    }
}

fn cmp_side(
    ctx: &mut LowerCtx,
    w: Width,
    sign_extend: bool,
    op: &Op,
    scratch: Gpr,
) -> Result<String, String> {
    let wide = sign_extend || w == Width::B64;
    let vw = if wide { Width::B64 } else { Width::B32 };
    match op {
        Op::Gpr(g) => {
            if sign_extend {
                let t = gpr(scratch, Width::B64)?;
                let s = gpr(*g, Width::B32)?;
                let mnemonic = if w == Width::B8 { "sxtb" } else { "sxth" };
                ctx.emitter.puts(&format!("{} {}, {}", mnemonic, t, s));
                Ok(t)
            } else {
                gpr(*g, vw)
            }
        }
        Op::Mem(m) => {
            let t = gpr(scratch, vw)?;
            let addr = addr_operand(ctx, m, w.bytes())?;
            let mnemonic = match (w, sign_extend) {
                (Width::B8, true) => "ldrsb",
                (Width::B16, true) => "ldrsh",
                _ => load_mnemonic(w),
            };
            ctx.emitter.puts(&format!("{} {}, {}", mnemonic, t, addr));
            Ok(t)
        }
        Op::Imm(v) => {
            let t = gpr(scratch, vw)?;
            mov_imm(ctx, &t, vw == Width::B64, *v)?;
            Ok(t)
        }
        Op::Sym(s) => {
            let text = text::sym_text(ctx, *s)?;
            Ok(format!("#{}", text))
        }
        other => Err(format!(
            "aarch64: comparison operand {:?} is not usable",
            other
        )),
    }
}

fn emit_cmp(ctx: &mut LowerCtx, w: Width, cc: IntCc, lhs: &Op, rhs: &Op) -> Result<IntCc, String> {
    let (cc, lhs, rhs) = match (lhs, rhs) {
        (Op::Imm(_), Op::Gpr(_) | Op::Mem(_)) => (flip_cc(cc), rhs, lhs),
        _ => (cc, lhs, rhs),
    };
    let signed_narrow = matches!(w, Width::B8 | Width::B16)
        && matches!(cc, IntCc::Gt | IntCc::Ge | IntCc::Lt | IntCc::Le);
    let left = cmp_side(ctx, w, signed_narrow, lhs, SCRATCH)?;
    match rhs {
        Op::Imm(v) if !signed_narrow && (0..=4095).contains(v) => {
            ctx.emitter.puts(&format!("cmp {}, #{}", left, v));
        }
        Op::Imm(v) if !signed_narrow && *v < 0 && v.unsigned_abs() <= 4095 => {
            ctx.emitter
                .puts(&format!("cmn {}, #{}", left, v.unsigned_abs()));
        }
        _ => {
            let right = cmp_side(ctx, w, signed_narrow, rhs, SCRATCH2)?;
            ctx.emitter.puts(&format!("cmp {}, {}", left, right));
        }
    }
    Ok(cc)
}

fn test_flags(ctx: &mut LowerCtx, w: Width, value: &Op, mask: Option<&Op>) -> Result<(), String> {
    let v = op_to_reg(ctx, value, w, SCRATCH)?;
    let v = match mask {
        Some(m) => {
            let mv = op_to_reg(ctx, m, w, SCRATCH2)?;
            ctx.emitter.puts(&format!("and {}, {}, {}", v, v, mv));
            v
        }
        None => v,
    };
    match w {
        Width::B8 | Width::B16 => {
            let mnemonic = if w == Width::B8 { "sxtb" } else { "sxth" };
            let t = gpr(SCRATCH2, Width::B32)?;
            ctx.emitter.puts(&format!("{} {}, {}", mnemonic, t, v));
            ctx.emitter.puts(&format!("tst {}, {}", t, t));
        }
        _ => ctx.emitter.puts(&format!("tst {}, {}", v, v)),
    }
    Ok(())
}

fn dst_reg(ctx: &mut LowerCtx, w: Width, dst: &Op) -> Result<String, String> {
    match dst {
        Op::Gpr(g) => gpr(*g, view(w)),
        Op::Mem(m) => {
            let r = gpr(SCRATCH, view(w))?;
            let addr = addr_operand(ctx, m, w.bytes())?;
            ctx.emitter
                .puts(&format!("{} {}, {}", load_mnemonic(w), r, addr));
            Ok(r)
        }
        other => Err(format!(
            "aarch64: op-branch destination {:?} is not usable",
            other
        )),
    }
}

fn flags_from_dst(ctx: &mut LowerCtx, w: Width, dst: &Op, flag: PredFlag) -> Result<(), String> {
    let r = dst_reg(ctx, w, dst)?;
    match w {
        Width::B8 | Width::B16 => {
            let mnemonic = if w == Width::B8 { "sxtb" } else { "sxth" };
            let mask = if w == Width::B8 { 0xff } else { 0xffff };
            match flag {
                PredFlag::O | PredFlag::S => {
                    let t = gpr(SCRATCH2, Width::B32)?;
                    ctx.emitter.puts(&format!("{} {}, {}", mnemonic, t, r));
                    if flag == PredFlag::O {
                        ctx.emitter.puts(&format!("cmp {}, {}", r, t));
                    } else {
                        ctx.emitter.puts(&format!("tst {}, {}", t, t));
                    }
                }
                PredFlag::Z | PredFlag::Nz => {
                    ctx.emitter.puts(&format!("ands wzr, {}, #{}", r, mask));
                }
            }
        }
        _ => ctx.emitter.puts(&format!("tst {}, {}", r, r)),
    }
    Ok(())
}

fn factor_reg(ctx: &mut LowerCtx, op: &Op, w: Width, scratch: Gpr) -> Result<String, String> {
    match op {
        Op::Gpr(g) => gpr(*g, view(w)),
        _ => into_reg(ctx, op, w, scratch),
    }
}

fn mul_overflow(ctx: &mut LowerCtx, w: Width, lhs: &Op, rhs: &Op) -> Result<(), String> {
    if !matches!(w, Width::B32 | Width::B64) {
        return Err("aarch64: mul-overflow branch is defined for 32/64-bit widths".to_string());
    }

    let r = factor_reg(ctx, rhs, w, SCRATCH2)?;
    let l = factor_reg(ctx, lhs, w, SCRATCH)?;
    let (lo_x, hi_x) = (gpr(SCRATCH, Width::B64)?, gpr(SCRATCH2, Width::B64)?);
    if w == Width::B64 {
        if l == lo_x && r == hi_x {
            let out = [
                format!("str {}, [sp, #-16]!", lo_x),
                format!("smulh {}, {}, {}", lo_x, lo_x, hi_x),
                format!("str {}, [sp, #8]", lo_x),
                format!("ldr {}, [sp]", lo_x),
                format!("mul {}, {}, {}", lo_x, lo_x, hi_x),
                format!("asr {}, {}, #63", lo_x, lo_x),
                format!("ldr {}, [sp, #8]", hi_x),
                "add sp, sp, #16".to_string(),
                format!("cmp {}, {}", hi_x, lo_x),
            ];
            for line in out {
                ctx.emitter.puts(&line);
            }
            return Ok(());
        }
        let (hi, lo) = if r == hi_x {
            (lo_x.clone(), hi_x.clone())
        } else {
            (hi_x, lo_x)
        };
        ctx.emitter.puts(&format!("smulh {}, {}, {}", hi, l, r));
        ctx.emitter.puts(&format!("mul {}, {}, {}", lo, l, r));
        ctx.emitter.puts(&format!("asr {}, {}, #63", lo, lo));
        ctx.emitter.puts(&format!("cmp {}, {}", hi, lo));
    } else {
        let lo_w = gpr(SCRATCH, Width::B32)?;
        ctx.emitter.puts(&format!("smull {}, {}, {}", lo_x, l, r));
        ctx.emitter.puts(&format!("sxtw {}, {}", hi_x, lo_w));
        ctx.emitter.puts(&format!("cmp {}, {}", lo_x, hi_x));
    }
    Ok(())
}

fn op_branch(
    ctx: &mut LowerCtx,
    op: FlagAlu,
    w: Width,
    flag: PredFlag,
    args: &[Op],
    target: Lbl,
) -> Result<(), String> {
    let label = text::label_text(ctx, target)?;
    let shape = alu3_from_args(args)
        .ok_or_else(|| "aarch64: op-branch takes 2 or 3 leading operands".to_string())?;
    let k = match op {
        FlagAlu::Add => AluKind::Add,
        FlagAlu::Sub => AluKind::Sub,
        FlagAlu::Mul => AluKind::Mul,
        FlagAlu::Or => AluKind::Or,
    };
    let narrow = matches!(w, Width::B8 | Width::B16);
    if k == AluKind::Or && flag == PredFlag::O {
        return alu(ctx, k, w, &shape, false);
    }
    let take = |ctx: &mut LowerCtx, cond: &str| {
        ctx.emitter.puts(&format!("b.{} {}", cond, label));
    };
    if k == AluKind::Mul && flag == PredFlag::O {
        mul_overflow(ctx, w, &shape.lhs, &shape.rhs)?;
        alu(ctx, k, w, &shape, false)?;
        take(ctx, "ne");
        return Ok(());
    }

    let native = !narrow && matches!(k, AluKind::Add | AluKind::Sub);
    if native {
        alu(ctx, k, w, &shape, true)?;
        take(
            ctx,
            if flag == PredFlag::O {
                "vs"
            } else {
                flag_cc(flag)
            },
        );
        return Ok(());
    }
    alu(ctx, k, w, &shape, false)?;
    flags_from_dst(ctx, w, &shape.dst, flag)?;
    take(
        ctx,
        if flag == PredFlag::O {
            "ne"
        } else {
            flag_cc(flag)
        },
    );
    Ok(())
}

fn stack_slot(ctx: &mut LowerCtx, disp: i32) -> Result<String, String> {
    if disp >= 0 && disp % 8 == 0 && disp < 4096 * 8 {
        return Ok(format!("[sp, #{}]", disp));
    }
    let t = gpr(SCRATCH, Width::B64)?;
    let magnitude = u64::from(disp.unsigned_abs());
    if magnitude <= 4095 {
        let mnemonic = if disp >= 0 { "add" } else { "sub" };
        ctx.emitter
            .puts(&format!("{} {}, sp, #{}", mnemonic, t, magnitude));
    } else {
        mov_imm(ctx, &t, true, i64::from(disp))?;
        ctx.emitter.puts(&format!("add {}, sp, {}", t, t));
    }
    Ok(format!("[{}]", t))
}

fn emit_label_address(ctx: &mut LowerCtx, xd: &str, label: &str) {
    if ctx.macho {
        ctx.emitter.puts(&format!("adrp {}, {}@PAGE", xd, label));
        ctx.emitter
            .puts(&format!("add {}, {}, {}@PAGEOFF", xd, xd, label));
    } else {
        ctx.emitter.puts(&format!("adrp {}, {}", xd, label));
        ctx.emitter
            .puts(&format!("add {}, {}, :lo12:{}", xd, xd, label));
    }
}

fn emit_extern_address(ctx: &mut LowerCtx, xd: &str, e: Extern) -> Result<(), String> {
    if e.reach == Reach::Near {
        let sym = text::extern_text(ctx, e.id)?;
        emit_label_address(ctx, xd, &sym);
        return Ok(());
    }
    let (page, pageoff) = if ctx.coff() {
        let slot = text::extern_slot(ctx, e.id)?;
        (slot.clone(), format!(":lo12:{}", slot))
    } else if ctx.macho {
        let sym = text::extern_text(ctx, e.id)?;
        (format!("{}@GOTPAGE", sym), format!("{}@GOTPAGEOFF", sym))
    } else {
        let sym = text::extern_text(ctx, e.id)?;
        (format!(":got:{}", sym), format!(":got_lo12:{}", sym))
    };
    ctx.emitter.puts(&format!("adrp {}, {}", xd, page));
    ctx.emitter
        .puts(&format!("ldr {}, [{}, {}]", xd, xd, pageoff));
    Ok(())
}

fn emit_mov(ctx: &mut LowerCtx, w: Width, dst: &Op, src: &Op) -> Result<(), String> {
    match (dst, src) {
        (Op::Gpr(g), Op::Label(l)) => {
            let xd = gpr(*g, Width::B64)?;
            let label = text::label_text(ctx, *l)?;
            emit_label_address(ctx, &xd, &label);
            if w != Width::B64 {
                let wd = gpr(*g, Width::B32)?;
                ctx.emitter.puts(&format!("mov {}, {}", wd, wd));
            }
            Ok(())
        }
        (Op::Gpr(g), src) => {
            let d = gpr(*g, view(w))?;
            load_into(ctx, src, &d, w)
        }
        (Op::Mem(m), src) => {
            if matches!(src, Op::Label(_)) {
                return Err("aarch64: cannot store a label address".to_string());
            }
            let value = op_to_reg(ctx, src, w, SCRATCH2)?;
            let addr = addr_operand(ctx, m, w.bytes())?;
            ctx.emitter
                .puts(&format!("{} {}, {}", store_mnemonic(w), value, addr));
            Ok(())
        }
        (Op::Fpr(_), _) => Err(
            "aarch64: move needs a GPR or memory destination (use moved/movev for floats)"
                .to_string(),
        ),
        (other, _) => Err(format!(
            "aarch64: move destination {:?} is not usable",
            other
        )),
    }
}

/// `leai`/`leap`/`pcrtoaddr`/`globaladdr`/`la`.
fn emit_lea(ctx: &mut LowerCtx, w: Width, dst: Gpr, src: &LeaSrc) -> Result<(), String> {
    let xd = gpr(dst, Width::B64)?;
    match src {
        LeaSrc::Label(l) => {
            let label = text::label_text(ctx, *l)?;
            emit_label_address(ctx, &xd, &label);
        }
        LeaSrc::Extern(e) => emit_extern_address(ctx, &xd, *e)?,
        LeaSrc::Mem(m) => {
            if m.index.is_none() && matches!(m.disp, Disp::Const(0)) {
                let b = gpr(m.base_reg(), Width::B64)?;
                if b != xd {
                    ctx.emitter.puts(&format!("mov {}, {}", xd, b));
                }
            } else {
                let t = synth_addr(ctx, m)?;
                if t != xd {
                    ctx.emitter.puts(&format!("mov {}, {}", xd, t));
                }
            }
        }
    }
    if w != Width::B64 {
        let wd = gpr(dst, Width::B32)?;
        ctx.emitter.puts(&format!("mov {}, {}", wd, wd));
    }
    Ok(())
}

fn emit_not_neg(ctx: &mut LowerCtx, w: Width, dst: &Op, neg: bool) -> Result<(), String> {
    let vw = view(w);
    let mnemonic = if neg { "neg" } else { "mvn" };
    match dst {
        Op::Gpr(d) => {
            let d = gpr(*d, vw)?;
            ctx.emitter.puts(&format!("{} {}, {}", mnemonic, d, d));
            Ok(())
        }
        Op::Mem(m) => {
            let t = gpr(SCRATCH2, vw)?;
            load_into(ctx, &Op::Mem(*m), &t, w)?;
            ctx.emitter.puts(&format!("{} {}, {}", mnemonic, t, t));
            let addr = addr_operand(ctx, m, w.bytes())?;
            ctx.emitter
                .puts(&format!("{} {}, {}", store_mnemonic(w), t, addr));
            Ok(())
        }
        other => Err(format!(
            "aarch64: not/neg destination {:?} is not usable",
            other
        )),
    }
}

fn emit_shift(
    ctx: &mut LowerCtx,
    w: Width,
    op: ShiftOp,
    dst: Gpr,
    cnt: &ShiftCnt,
) -> Result<(), String> {
    let vw = view(w);
    let width: u64 = if vw == Width::B64 { 64 } else { 32 };
    let d = gpr(dst, vw)?;
    match cnt {
        ShiftCnt::Imm(v) => {
            let count = (*v as u64) & (width - 1);
            let (mnemonic, amount) = match op {
                ShiftOp::Shl => ("lsl", count),
                ShiftOp::ShrSar => ("asr", count),
                ShiftOp::Shr => ("lsr", count),
                ShiftOp::Rotr => ("ror", count),
                ShiftOp::Rotl => ("ror", (width - count) % width),
            };
            ctx.emitter
                .puts(&format!("{} {}, {}, #{}", mnemonic, d, d, amount));
            Ok(())
        }
        ShiftCnt::Reg(g) => {
            let s = gpr(*g, vw)?;
            match op {
                ShiftOp::Shl => ctx.emitter.puts(&format!("lsl {}, {}, {}", d, d, s)),
                ShiftOp::ShrSar => ctx.emitter.puts(&format!("asr {}, {}, {}", d, d, s)),
                ShiftOp::Shr => ctx.emitter.puts(&format!("lsr {}, {}, {}", d, d, s)),
                ShiftOp::Rotr => ctx.emitter.puts(&format!("ror {}, {}, {}", d, d, s)),
                ShiftOp::Rotl => {
                    // Rotate-left by `n` is rotate-right by `-n`.
                    let t = gpr(SCRATCH2, vw)?;
                    ctx.emitter.puts(&format!("neg {}, {}", t, s));
                    ctx.emitter.puts(&format!("ror {}, {}, {}", d, d, t));
                }
            }
            Ok(())
        }
    }
}

fn emit_adc(ctx: &mut LowerCtx, dst: &Op, src: &Op, borrow: bool) -> Result<(), String> {
    let mnemonic = if borrow { "sbcs" } else { "adcs" };
    match dst {
        Op::Gpr(d) => {
            let d = gpr(*d, Width::B64)?;
            let s = op_to_reg(ctx, src, Width::B64, SCRATCH)?;
            ctx.emitter
                .puts(&format!("{} {}, {}, {}", mnemonic, d, d, s));
            Ok(())
        }
        Op::Mem(m) => {
            let t = gpr(SCRATCH2, Width::B64)?;
            load_into(ctx, &Op::Mem(*m), &t, Width::B64)?;
            let s = op_to_reg(ctx, src, Width::B64, SCRATCH)?;
            ctx.emitter
                .puts(&format!("{} {}, {}, {}", mnemonic, t, t, s));
            let addr = addr_operand(ctx, m, 8)?;
            ctx.emitter.puts(&format!("str {}, {}", t, addr));
            Ok(())
        }
        other => Err(format!(
            "aarch64: adc/sbb destination {:?} is not usable",
            other
        )),
    }
}

fn emit_divmod1(ctx: &mut LowerCtx, signed: bool, w: Width, divisor: &Op) -> Result<(), String> {
    let vw = view(w);
    let lo = gpr(T0, vw)?;
    let hi = gpr(T2, vw)?;
    let dvs = into_reg(ctx, divisor, w, SCRATCH2)?;
    let trap = text::synth_name(ctx, "div0", 0);
    let done = text::synth_name(ctx, "divdone", 0);
    ctx.emitter.puts(&format!("cbz {}, {}", dvs, trap));
    if signed {
        // Trap on the one overflow case, `INT_MIN / -1`.
        let ok = text::synth_name(ctx, "divok", 0);
        let t = gpr(SCRATCH, vw)?;
        let bound = if vw == Width::B64 {
            i64::MIN
        } else {
            i64::from(i32::MIN)
        };
        mov_imm(ctx, &t, vw == Width::B64, bound)?;
        ctx.emitter.puts(&format!("cmp {}, {}", lo, t));
        ctx.emitter.puts(&format!("b.ne {}", ok));
        ctx.emitter.puts(&format!("cmn {}, #1", dvs));
        ctx.emitter.puts(&format!("b.ne {}", ok));
        ctx.emitter.puts(&format!("b {}", trap));
        ctx.emitter.puts_local_label(&ok);
    }
    // The dividend's low half dies with the quotient: copy it aside first.
    let save = gpr(SCRATCH, vw)?;
    ctx.emitter.puts(&format!("mov {}, {}", save, lo));
    let mnemonic = if signed { "sdiv" } else { "udiv" };
    ctx.emitter
        .puts(&format!("{} {}, {}, {}", mnemonic, lo, lo, dvs));
    ctx.emitter
        .puts(&format!("msub {}, {}, {}, {}", hi, lo, dvs, save));
    ctx.emitter.puts(&format!("b {}", done));
    ctx.emitter.puts_local_label(&trap);
    ctx.emitter.puts("brk #0");
    ctx.emitter.puts_local_label(&done);
    Ok(())
}

fn emit_div3(
    ctx: &mut LowerCtx,
    signed: bool,
    w: Width,
    dst: Gpr,
    dvd: &Op,
    dvs: &Op,
    is_rem: bool,
) -> Result<(), String> {
    let vw = view(w);
    let d = gpr(dst, vw)?;
    let mnemonic = if signed { "sdiv" } else { "udiv" };
    if !is_rem {
        load_into(ctx, dvd, &d, w)?;
        let r = op_to_reg(ctx, dvs, w, SCRATCH)?;
        ctx.emitter
            .puts(&format!("{} {}, {}, {}", mnemonic, d, d, r));
        return Ok(());
    }

    let saved = into_reg(ctx, dvd, w, SCRATCH2)?;
    let r = op_to_reg(ctx, dvs, w, SCRATCH)?;
    ctx.emitter
        .puts(&format!("{} {}, {}, {}", mnemonic, d, saved, r));
    ctx.emitter
        .puts(&format!("msub {}, {}, {}, {}", d, d, r, saved));
    Ok(())
}

fn emit_extend(
    ctx: &mut LowerCtx,
    from: Width,
    to: Width,
    sx: Sx,
    dst: Gpr,
    src: &Op,
) -> Result<(), String> {
    let s = op_to_reg(ctx, src, from, SCRATCH)?;
    let d = gpr(dst, view(to))?;
    match (from, to, sx) {
        (Width::B64, _, _) => {
            if s != d {
                ctx.emitter.puts(&format!("mov {}, {}", d, s));
            }
        }
        (Width::B32, Width::B64, Sx::Zero) => {
            ctx.emitter.puts(&format!("uxtw {}, {}", d, s));
        }
        (Width::B32, Width::B64, Sx::Sign) => {
            ctx.emitter.puts(&format!("sxtw {}, {}", d, s));
        }
        (Width::B32, _, _) => {
            if s != d {
                ctx.emitter.puts(&format!("mov {}, {}", d, s));
            }
        }
        (Width::B8 | Width::B16, _, Sx::Sign) => {
            let mnemonic = if from == Width::B8 { "sxtb" } else { "sxth" };
            ctx.emitter.puts(&format!("{} {}, {}", mnemonic, d, s));
        }
        (Width::B8 | Width::B16, _, Sx::Zero) => {
            let mnemonic = if from == Width::B8 { "uxtb" } else { "uxth" };
            ctx.emitter.puts(&format!("{} {}, {}", mnemonic, d, s));
        }
    }
    Ok(())
}

fn emit_popcnt(ctx: &mut LowerCtx, w: Width, dst: Gpr, src: &Op) -> Result<(), String> {
    let s = into_reg(ctx, src, w, SCRATCH)?;
    let x = gpr(SCRATCH, Width::B64)?;
    let dv = vreg(FSCRATCH);
    let d = gpr(dst, Width::B32)?;
    ctx.emitter
        .puts(&format!("fmov {}, {}", fpr(FSCRATCH, FKind::F64), x));
    let _ = s;
    ctx.emitter.puts(&format!("cnt {}.8b, {}.8b", dv, dv));
    ctx.emitter
        .puts(&format!("uaddlv h{}, {}.8b", FSCRATCH.0, dv));
    ctx.emitter.puts(&format!("umov {}, {}.h[0]", d, dv));
    Ok(())
}

fn emit_farith(ctx: &mut LowerCtx, op: FAlu, k: FKind, arith: &FArith3) -> Result<(), String> {
    let mnemonic = match op {
        FAlu::Add => "fadd",
        FAlu::Sub => "fsub",
        FAlu::Mul => "fmul",
        FAlu::Div => "fdiv",
        FAlu::Min => "fmin",
        FAlu::Max => "fmax",
    };
    let d = fpr(arith.dst, k);
    match &arith.rhs {
        Some(rhs) => {
            let r = match rhs {
                Op::Fpr(f) if *f != arith.dst => fpr(*f, k),
                Op::Fpr(_) => {
                    ctx.emitter
                        .puts(&format!("fmov {}, {}", fpr(FSCRATCH, k), d));
                    fpr(FSCRATCH, k)
                }
                _ => fp_src(ctx, k, rhs)?,
            };
            let l = match &arith.lhs {
                Op::Fpr(f) => fpr(*f, k),
                Op::Mem(m) => {
                    let addr = addr_operand(ctx, m, if k == FKind::F32 { 4 } else { 8 })?;
                    ctx.emitter.puts(&format!("ldr {}, {}", d, addr));
                    d.clone()
                }
                Op::Imm(v) => {
                    let wide = k != FKind::F32;
                    let t = gpr(SCRATCH, if wide { Width::B64 } else { Width::B32 })?;
                    mov_imm(ctx, &t, wide, *v)?;
                    ctx.emitter.puts(&format!("fmov {}, {}", d, t));
                    d.clone()
                }
                other => {
                    return Err(format!(
                        "aarch64: fp arithmetic operand {:?} is not usable",
                        other
                    ))
                }
            };
            ctx.emitter
                .puts(&format!("{} {}, {}, {}", mnemonic, d, l, r));
            Ok(())
        }
        None => {
            let l = fp_src(ctx, k, &arith.lhs)?;
            ctx.emitter
                .puts(&format!("{} {}, {}, {}", mnemonic, d, d, l));
            Ok(())
        }
    }
}

fn emit_fma(
    ctx: &mut LowerCtx,
    op: FmaOp,
    k: FKind,
    a: &Op,
    b: &Op,
    c: &Op,
    dst: Fpr,
) -> Result<(), String> {
    let mnemonic = match op {
        FmaOp::Add => "fmadd",
        FmaOp::Sub => "fnmsub",
        FmaOp::NegAdd => "fmsub",
        FmaOp::NegSub => "fnmadd",
    };
    let spilled = [a, b, c]
        .iter()
        .filter(|op| !matches!(op, Op::Fpr(_)))
        .count();
    if spilled > 1 {
        return Err("aarch64: fma needs at most one spilled operand".to_string());
    }
    let ra = fp_src(ctx, k, a)?;
    let rb = fp_src(ctx, k, b)?;
    let rc = fp_src(ctx, k, c)?;
    ctx.emitter.puts(&format!(
        "{} {}, {}, {}, {}",
        mnemonic,
        fpr(dst, k),
        ra,
        rb,
        rc
    ));
    Ok(())
}

fn emit_bitcast(ctx: &mut LowerCtx, dir: BitcastDir, dst: &Op, src: &Op) -> Result<(), String> {
    match (dir, dst, src) {
        (BitcastDir::Q2D, Op::Fpr(d), Op::Gpr(s)) => {
            ctx.emitter.puts(&format!(
                "fmov {}, {}",
                fpr(*d, FKind::F64),
                gpr(*s, Width::B64)?
            ));
            Ok(())
        }
        (BitcastDir::D2Q, Op::Gpr(d), Op::Fpr(s)) => {
            ctx.emitter.puts(&format!(
                "fmov {}, {}",
                gpr(*d, Width::B64)?,
                fpr(*s, FKind::F64)
            ));
            Ok(())
        }
        (BitcastDir::I2F, Op::Fpr(d), Op::Gpr(s)) => {
            ctx.emitter.puts(&format!(
                "fmov {}, {}",
                fpr(*d, FKind::F32),
                gpr(*s, Width::B32)?
            ));
            Ok(())
        }
        (BitcastDir::F2I, Op::Gpr(d), Op::Fpr(s)) => {
            ctx.emitter.puts(&format!(
                "fmov {}, {}",
                gpr(*d, Width::B32)?,
                fpr(*s, FKind::F32)
            ));
            Ok(())
        }
        (dir, dst, src) => Err(format!(
            "aarch64: unsupported bit-cast {:?} from {:?} to {:?}",
            dir, src, dst
        )),
    }
}

fn emit_set(ctx: &mut LowerCtx, w: Width, dst: &Op, cond: &str) -> Result<(), String> {
    match dst {
        Op::Gpr(d) => {
            let d = gpr(*d, Width::B32)?;
            ctx.emitter.puts(&format!("cset {}, {}", d, cond));
            Ok(())
        }
        Op::Mem(m) => {
            let t = gpr(SCRATCH2, view(w))?;
            ctx.emitter.puts(&format!("cset {}, {}", t, cond));
            let addr = addr_operand(ctx, m, w.bytes())?;
            ctx.emitter
                .puts(&format!("{} {}, {}", store_mnemonic(w), t, addr));
            Ok(())
        }
        other => Err(format!(
            "aarch64: set destination {:?} is not usable",
            other
        )),
    }
}

fn emit_branch(
    ctx: &mut LowerCtx,
    cc: IntCc,
    w: Width,
    lhs: &Op,
    rhs: &Op,
    target: Lbl,
) -> Result<(), String> {
    let label = text::label_text(ctx, target)?;
    let zero_cmp = match (cc, lhs, rhs) {
        (IntCc::Eq, Op::Gpr(g), Op::Imm(0)) | (IntCc::Eq, Op::Imm(0), Op::Gpr(g)) => {
            Some((*g, "cbz"))
        }
        (IntCc::Ne, Op::Gpr(g), Op::Imm(0)) | (IntCc::Ne, Op::Imm(0), Op::Gpr(g)) => {
            Some((*g, "cbnz"))
        }
        _ => None,
    };
    if let Some((g, mnemonic)) = zero_cmp {
        let r = gpr(g, view(w))?;
        ctx.emitter.puts(&format!("{} {}, {}", mnemonic, r, label));
        return Ok(());
    }
    let cc = emit_cmp(ctx, w, cc, lhs, rhs)?;
    ctx.emitter.puts(&format!("b.{} {}", int_cc(cc), label));
    Ok(())
}

fn emit_test_branch(
    ctx: &mut LowerCtx,
    w: Width,
    value: &Op,
    mask: Option<&Op>,
    test: TestKind,
    target: Lbl,
) -> Result<(), String> {
    let label = text::label_text(ctx, target)?;
    if mask.is_none() {
        if let Op::Gpr(g) = value {
            let r = gpr(*g, view(w))?;
            match test {
                TestKind::Zero => {
                    ctx.emitter.puts(&format!("cbz {}, {}", r, label));
                    return Ok(());
                }
                TestKind::NonZero => {
                    ctx.emitter.puts(&format!("cbnz {}, {}", r, label));
                    return Ok(());
                }
                TestKind::Sign => {
                    let bit = match w {
                        Width::B8 => 7,
                        Width::B16 => 15,
                        Width::B32 => 31,
                        Width::B64 => 63,
                    };
                    ctx.emitter
                        .puts(&format!("tbnz {}, #{}, {}", r, bit, label));
                    return Ok(());
                }
            }
        }
    }
    test_flags(ctx, w, value, mask)?;
    let cond = match test {
        TestKind::Sign => "mi",
        TestKind::Zero => "eq",
        TestKind::NonZero => "ne",
    };
    ctx.emitter.puts(&format!("b.{} {}", cond, label));
    Ok(())
}

fn emit_jump(ctx: &mut LowerCtx, target: &Target, call: bool) -> Result<(), String> {
    let direct = if call { "bl" } else { "b" };
    let indirect = if call { "blr" } else { "br" };
    match target {
        Target::Label(l) => {
            let label = text::label_text(ctx, *l)?;
            ctx.emitter.puts(&format!("{} {}", direct, label));
            Ok(())
        }
        Target::Reg(g) => {
            let r = gpr(*g, Width::B64)?;
            ctx.emitter.puts(&format!("{} {}", indirect, r));
            Ok(())
        }
        Target::Mem(m) => {
            let t = gpr(SCRATCH, Width::B64)?;
            let addr = addr_operand(ctx, m, 8)?;
            ctx.emitter.puts(&format!("ldr {}, {}", t, addr));
            ctx.emitter.puts(&format!("{} {}", indirect, t));
            Ok(())
        }
        Target::Abs(v) => {
            let t = gpr(SCRATCH, Width::B64)?;
            mov_imm(ctx, &t, true, *v)?;
            ctx.emitter.puts(&format!("{} {}", indirect, t));
            Ok(())
        }
        Target::Extern(e) if e.reach == Reach::Near => {
            let sym = text::extern_text(ctx, e.id)?;
            ctx.emitter.puts(&format!("{} {}", direct, sym));
            Ok(())
        }
        Target::Extern(e) => {
            let t = gpr(SCRATCH, Width::B64)?;
            emit_extern_address(ctx, &t, *e)?;
            ctx.emitter.puts(&format!("{} {}", indirect, t));
            Ok(())
        }
    }
}

fn emit_branch_f(
    ctx: &mut LowerCtx,
    cc: FCc,
    k: FKind,
    lhs: &Op,
    rhs: &Op,
    target: Lbl,
) -> Result<(), String> {
    let label = text::label_text(ctx, target)?;
    let spilled = [!matches!(lhs, Op::Fpr(_)), !matches!(rhs, Op::Fpr(_))];
    if spilled[0] && spilled[1] {
        return Err("aarch64: float compare needs two live registers".to_string());
    }

    let (first, second) = match cc {
        FCc::Lt | FCc::Le => (rhs, lhs),
        _ => (lhs, rhs),
    };
    let l = fp_src(ctx, k, first)?;
    let r = fp_src(ctx, k, second)?;
    ctx.emitter.puts(&format!("fcmp {}, {}", l, r));
    match cc {
        FCc::Eq => ctx.emitter.puts(&format!("b.eq {}", label)),
        FCc::Ne => {
            // Ordered not-equal: skip the unordered case.
            let skip = text::synth_name(ctx, "fne", 0);
            ctx.emitter.puts(&format!("b.vs {}", skip));
            ctx.emitter.puts(&format!("b.ne {}", label));
            ctx.emitter.puts_local_label(&skip);
        }
        FCc::NeUn => ctx.emitter.puts(&format!("b.ne {}", label)),
        FCc::Gt | FCc::Lt => ctx.emitter.puts(&format!("b.gt {}", label)),
        FCc::Ge | FCc::Le => ctx.emitter.puts(&format!("b.ge {}", label)),
        FCc::GtUn | FCc::LtUn => {
            ctx.emitter.puts(&format!("b.lo {}", label));
            ctx.emitter.puts(&format!("b.vs {}", label));
        }
        FCc::GeUn | FCc::LeUn => {
            ctx.emitter.puts(&format!("b.ls {}", label));
            ctx.emitter.puts(&format!("b.vs {}", label));
        }
        FCc::EqUn => {
            ctx.emitter.puts(&format!("b.eq {}", label));
            ctx.emitter.puts(&format!("b.vs {}", label));
        }
    }
    Ok(())
}

fn emit_fset(
    ctx: &mut LowerCtx,
    cc: FCc,
    k: FKind,
    dst: &Op,
    lhs: &Op,
    rhs: &Op,
) -> Result<(), String> {
    let (swap, cond, unordered_and) = match cc {
        FCc::Eq => (false, "eq", true),
        FCc::Ne => (false, "ne", true),
        FCc::NeUn => (false, "ne", false),
        FCc::Gt => (false, "gt", false),
        FCc::Ge => (false, "ge", false),
        FCc::Lt => (true, "gt", false),
        FCc::Le => (true, "ge", false),
        other => {
            return Err(format!(
                "aarch64: unordered float set {:?} is only defined for eq/ne",
                other
            ))
        }
    };
    let spilled = [!matches!(lhs, Op::Fpr(_)), !matches!(rhs, Op::Fpr(_))];
    if spilled[0] && spilled[1] {
        return Err("aarch64: float compare needs two live registers".to_string());
    }
    let (first, second) = if swap { (rhs, lhs) } else { (lhs, rhs) };
    let l = fp_src(ctx, k, first)?;
    let r = fp_src(ctx, k, second)?;

    let t = match dst {
        Op::Gpr(d) => gpr(*d, Width::B32)?,
        Op::Mem(_) => gpr(SCRATCH2, Width::B32)?,
        other => {
            return Err(format!(
                "aarch64: float set destination {:?} is not usable",
                other
            ))
        }
    };
    ctx.emitter.puts(&format!("fcmp {}, {}", l, r));
    ctx.emitter.puts(&format!("cset {}, {}", t, cond));
    if unordered_and {
        ctx.emitter.puts(&format!("csel {}, {}, wzr, vc", t, t));
    }
    match dst {
        Op::Mem(m) => {
            let addr = addr_operand(ctx, m, 4)?;
            ctx.emitter.puts(&format!("str {}, {}", t, addr));
            Ok(())
        }
        _ => Ok(()),
    }
}

fn tls_base_register(ctx: &LowerCtx) -> &'static str {
    if ctx.macho {
        "tpidrro_el0"
    } else {
        "tpidr_el0"
    }
}

fn emit_tls(ctx: &mut LowerCtx, w: Width, reg: Gpr, idx: i64, load: bool) -> Result<(), String> {
    let off = idx
        .checked_mul(8)
        .ok_or_else(|| "aarch64: tls index overflow".to_string())?;
    let base = gpr(SCRATCH, Width::B64)?;

    let r = gpr(reg, view(w))?;
    ctx.emitter
        .puts(&format!("mrs {}, {}", base, tls_base_register(ctx)));
    let mnemonic = if load {
        load_mnemonic(w)
    } else {
        store_mnemonic(w)
    };

    let scale = w.bytes();
    let direct = off >= 0 && off % i64::from(scale) == 0 && off < 4096 * i64::from(scale);
    if direct {
        ctx.emitter
            .puts(&format!("{} {}, [{}, #{}]", mnemonic, r, base, off));
    } else {
        let t = gpr(SCRATCH2, Width::B64)?;
        mov_imm(ctx, &t, true, off)?;
        ctx.emitter.puts(&format!("add {}, {}, {}", t, base, t));
        ctx.emitter.puts(&format!("{} {}, [{}]", mnemonic, r, t));
    }
    Ok(())
}

fn emit_tls_lea(ctx: &mut LowerCtx, reg: Gpr, idx: i64) -> Result<(), String> {
    let off = idx
        .checked_mul(8)
        .ok_or_else(|| "aarch64: tls index overflow".to_string())?;
    let base = gpr(SCRATCH, Width::B64)?;
    let r = gpr(reg, Width::B64)?;
    ctx.emitter
        .puts(&format!("mrs {}, {}", base, tls_base_register(ctx)));
    if off == 0 {
        if r != base {
            ctx.emitter.puts(&format!("mov {}, {}", r, base));
        }
    } else if off > 0 && off < 4096 {
        ctx.emitter.puts(&format!("add {}, {}, #{}", r, base, off));
    } else if off < 0 && off > -4096 {
        ctx.emitter.puts(&format!("sub {}, {}, #{}", r, base, -off));
    } else {
        let t = gpr(SCRATCH2, Width::B64)?;
        mov_imm(ctx, &t, true, off)?;
        ctx.emitter.puts(&format!("add {}, {}, {}", r, base, t));
    }
    Ok(())
}

fn emit_rmw(ctx: &mut LowerCtx, op: AtomicOp, w: Width, a: &Op, b: &Op) -> Result<(), String> {
    let (mem, r) = match (a, b) {
        (Op::Mem(m), Op::Gpr(r)) | (Op::Gpr(r), Op::Mem(m)) => (m, gpr(*r, view(w))?),
        (Op::Mem(m), Op::Imm(_)) | (Op::Imm(_), Op::Mem(m)) => {
            let imm = if matches!(a, Op::Imm(_)) { a } else { b };
            let r = gpr(SCRATCH2, view(w))?;
            load_into(ctx, imm, &r, w)?;
            (m, r)
        }
        _ => {
            return Err(format!(
                "aarch64: atomic r/m needs one memory and one register or immediate operand, got {:?}/{:?}",
                a, b
            ))
        }
    };
    let addr = addr_base_only(ctx, mem)?;
    let mint = |stem: &str| match w {
        Width::B8 => format!("{}b", stem),
        Width::B16 => format!("{}h", stem),
        Width::B32 | Width::B64 => stem.to_string(),
    };
    let mnemonic = match op {
        AtomicOp::Add | AtomicOp::Sub => mint("ldaddal"),
        AtomicOp::Or => mint("ldsetal"),
        AtomicOp::Xor => mint("ldeoral"),
        AtomicOp::Xchg => mint("swpal"),
        AtomicOp::And => mint("ldclral"),
    };
    match op {
        AtomicOp::Sub => ctx.emitter.puts(&format!("neg {}, {}", r, r)),
        AtomicOp::And => ctx.emitter.puts(&format!("mvn {}, {}", r, r)),
        _ => {}
    }
    ctx.emitter
        .puts(&format!("{} {}, {}, {}", mnemonic, r, r, addr));
    Ok(())
}

fn emit_cas(
    ctx: &mut LowerCtx,
    w: Width,
    mem: &Mem,
    src: Gpr,
    branch: Option<&Lbl>,
) -> Result<(), String> {
    let vw = view(w);
    let lo = gpr(T0, vw)?;
    let des = gpr(src, vw)?;
    let saved = gpr(SCRATCH2, vw)?;
    let addr = addr_base_only(ctx, mem)?;
    // `CASAL` overwrites the value, save it
    ctx.emitter.puts(&format!("mov {}, {}", saved, lo));
    let mnemonic = match w {
        Width::B8 => "casalb",
        Width::B16 => "casalh",
        Width::B32 | Width::B64 => "casal",
    };
    ctx.emitter
        .puts(&format!("{} {}, {}, {}", mnemonic, lo, des, addr));
    if let Some(target) = branch {
        let label = text::label_text(ctx, *target)?;
        ctx.emitter.puts(&format!("cmp {}, {}", lo, saved));
        ctx.emitter.puts(&format!("b.ne {}", label));
    }
    Ok(())
}

fn emit_pair(
    ctx: &mut LowerCtx,
    w: PairW,
    first: &Op,
    second: &Op,
    mem: &Mem,
    load: bool,
) -> Result<(), String> {
    let mnemonic = if load { "ldp" } else { "stp" };
    let scale: i64 = match w {
        PairW::B32 => 4,
        PairW::B64 | PairW::F64 => 8,
        PairW::V128 => 16,
    };
    let addr = pair_addr_operand(ctx, mem, scale)?;
    let render = |op: &Op| -> Result<String, String> {
        match (w, op) {
            (PairW::B32, Op::Gpr(g)) => gpr(*g, Width::B32),
            (PairW::B64, Op::Gpr(g)) => gpr(*g, Width::B64),
            (PairW::F64, Op::Fpr(f)) => Ok(fpr(*f, FKind::F64)),
            (PairW::V128, Op::Fpr(f)) => Ok(qreg(*f)),
            _ => Err(format!(
                "aarch64: pair access operand {:?} does not match its width",
                op
            )),
        }
    };

    let aliased = load && op_eq(first, second);
    let first_text = if aliased {
        match w {
            PairW::B32 => gpr(SCRATCH, Width::B32)?,
            PairW::B64 => gpr(SCRATCH, Width::B64)?,
            PairW::F64 => fpr(FSCRATCH, FKind::F64),
            PairW::V128 => qreg(FSCRATCH),
        }
    } else {
        render(first)?
    };
    let second_text = render(second)?;
    ctx.emitter.puts(&format!(
        "{} {}, {}, {}",
        mnemonic, first_text, second_text, addr
    ));
    Ok(())
}

#[allow(clippy::too_many_lines)]
pub fn emit(ctx: &mut LowerCtx, inst: &Inst) -> Result<(), String> {
    match inst {
        Inst::Mov { w, dst, src, .. } => emit_mov(ctx, *w, dst, src),
        Inst::MovZero32 { dst, src } => emit_mov(ctx, Width::B32, dst, src),
        Inst::Bind(l) => {
            let text = text::label_text(ctx, *l)?;
            ctx.emitter.puts_local_label(&text);
            Ok(())
        }
        Inst::Bswap { w, dst, src } => {
            if !matches!(w, Width::B32 | Width::B64) {
                return Err("aarch64: bswap needs a 32/64-bit width".to_string());
            }
            let vw = view(*w);
            match (dst, src) {
                (Op::Gpr(d), src) => {
                    let d = gpr(*d, vw)?;
                    let s = op_to_reg(ctx, src, *w, SCRATCH)?;
                    ctx.emitter.puts(&format!("rev {}, {}", d, s));
                    Ok(())
                }
                (Op::Mem(m), Op::Gpr(s)) => {
                    let t = gpr(SCRATCH2, vw)?;
                    let s = gpr(*s, vw)?;
                    ctx.emitter.puts(&format!("rev {}, {}", t, s));
                    let addr = addr_operand(ctx, m, w.bytes())?;
                    ctx.emitter
                        .puts(&format!("{} {}, {}", store_mnemonic(*w), t, addr));
                    Ok(())
                }
                (dst, src) => Err(format!(
                    "aarch64: bswap needs a register destination, got {:?}/{:?}",
                    dst, src
                )),
            }
        }
        Inst::Load {
            w,
            sx,
            dst,
            addr,
            acquire,
        } => {
            if *acquire {
                let mnemonic = match w {
                    Width::B8 => "ldarb",
                    Width::B16 => "ldarh",
                    Width::B32 | Width::B64 => "ldar",
                };
                let reg = gpr(*dst, view(*w))?;
                let addr = addr_base_only(ctx, addr)?;
                ctx.emitter.puts(&format!("{} {}, {}", mnemonic, reg, addr));
                return Ok(());
            }
            let mnemonic = match (w, sx) {
                (Width::B8, Sx::Zero) => "ldrb",
                (Width::B8, Sx::Sign) => "ldrsb",
                (Width::B16, Sx::Zero) => "ldrh",
                (Width::B16, Sx::Sign) => "ldrsh",
                (Width::B32 | Width::B64, _) => "ldr",
            };
            let reg = if *sx == Sx::Sign && matches!(w, Width::B8 | Width::B16) {
                gpr(*dst, Width::B64)?
            } else {
                gpr(*dst, view(*w))?
            };
            let addr = addr_operand(ctx, addr, w.bytes())?;
            ctx.emitter.puts(&format!("{} {}, {}", mnemonic, reg, addr));
            Ok(())
        }
        Inst::Store { w, src, addr } => {
            let value = match src {
                Op::Gpr(_) | Op::Imm(_) | Op::Sym(_) => op_to_reg(ctx, src, *w, SCRATCH2)?,
                other => {
                    return Err(format!(
                        "aarch64: store needs a register or immediate source, got {:?}",
                        other
                    ))
                }
            };
            let addr = addr_operand(ctx, addr, w.bytes())?;
            ctx.emitter
                .puts(&format!("{} {}, {}", store_mnemonic(*w), value, addr));
            Ok(())
        }
        Inst::LoadF { k, dst, addr } => {
            let addr = addr_operand(ctx, addr, if *k == FKind::F32 { 4 } else { 8 })?;
            ctx.emitter
                .puts(&format!("ldr {}, {}", fpr(*dst, *k), addr));
            Ok(())
        }
        Inst::StoreF { k, src, addr } => {
            let addr = addr_operand(ctx, addr, if *k == FKind::F32 { 4 } else { 8 })?;
            ctx.emitter
                .puts(&format!("str {}, {}", fpr(*src, *k), addr));
            Ok(())
        }
        Inst::FMov { k, dst, src } => {
            if dst != src {
                ctx.emitter
                    .puts(&format!("fmov {}, {}", fpr(*dst, *k), fpr(*src, *k)));
            }
            Ok(())
        }
        Inst::LoadV { dst, addr } => {
            let addr = addr_operand(ctx, addr, 16)?;
            ctx.emitter.puts(&format!("ldr {}, {}", qreg(*dst), addr));
            Ok(())
        }
        Inst::StoreV { src, addr } => {
            let addr = addr_operand(ctx, addr, 16)?;
            ctx.emitter.puts(&format!("str {}, {}", qreg(*src), addr));
            Ok(())
        }
        Inst::VMov { dst, src } => {
            if dst != src {
                ctx.emitter
                    .puts(&format!("mov {}.16b, {}.16b", vreg(*dst), vreg(*src)));
            }
            Ok(())
        }
        Inst::Lea { w, dst, src } => emit_lea(ctx, *w, *dst, src),
        Inst::Push { op } => {
            // `push` itself goes through `stack_group`; a lone slot is 16
            // bytes, matching it.
            let r = op_to_reg(ctx, op, Width::B64, SCRATCH)?;
            ctx.emitter.puts(&format!("str {}, [sp, #-16]!", r));
            Ok(())
        }
        Inst::Pop { op } => match op {
            Op::Gpr(g) => {
                let r = gpr(*g, Width::B64)?;
                ctx.emitter.puts(&format!("ldr {}, [sp], #16", r));
                Ok(())
            }
            Op::Mem(m) => {
                let t = gpr(SCRATCH2, Width::B64)?;
                ctx.emitter.puts(&format!("ldr {}, [sp], #16", t));
                let addr = addr_operand(ctx, m, 8)?;
                ctx.emitter.puts(&format!("str {}, {}", t, addr));
                Ok(())
            }
            other => Err(format!(
                "aarch64: pop needs a register or memory operand, got {:?}",
                other
            )),
        },
        Inst::PushV { src } => {
            ctx.emitter
                .puts(&format!("str {}, [sp, #-16]!", qreg(*src)));
            Ok(())
        }
        Inst::PopV { dst } => {
            ctx.emitter.puts(&format!("ldr {}, [sp], #16", qreg(*dst)));
            Ok(())
        }
        Inst::Peek { disp, dst } => {
            let addr = stack_slot(ctx, *disp)?;
            ctx.emitter
                .puts(&format!("ldr {}, {}", gpr(*dst, Width::B64)?, addr));
            Ok(())
        }
        Inst::Poke { disp, src } => {
            let addr = stack_slot(ctx, *disp)?;
            ctx.emitter
                .puts(&format!("str {}, {}", gpr(*src, Width::B64)?, addr));
            Ok(())
        }
        Inst::Add { w, op } => alu(ctx, AluKind::Add, *w, op, false),
        Inst::Sub { w, op } => alu(ctx, AluKind::Sub, *w, op, false),
        Inst::Mul { w, op } => alu(ctx, AluKind::Mul, *w, op, false),
        Inst::And { w, op } => alu(ctx, AluKind::And, *w, op, false),
        Inst::Or { w, op } => alu(ctx, AluKind::Or, *w, op, false),
        Inst::Xor { w, op } => alu(ctx, AluKind::Xor, *w, op, false),
        Inst::Not { w, dst } => emit_not_neg(ctx, *w, dst, false),
        Inst::Neg { w, dst } => emit_not_neg(ctx, *w, dst, true),
        Inst::Shift { w, op, dst, cnt } => emit_shift(ctx, *w, *op, *dst, cnt),
        Inst::MulImm { w, dst, lhs, imm } => {
            let vw = view(*w);
            let t = gpr(SCRATCH2, vw)?;
            mov_imm(ctx, &t, vw == Width::B64, *imm)?;
            ctx.emitter.puts(&format!(
                "mul {}, {}, {}",
                gpr(*dst, vw)?,
                gpr(*lhs, vw)?,
                t
            ));
            Ok(())
        }
        Inst::AluS { op, w, alu: shape } => {
            let k = match op {
                AluOp::Add => AluKind::Add,
                AluOp::Sub => AluKind::Sub,
                AluOp::Or => AluKind::Or,
            };
            alu(ctx, k, *w, shape, true)
        }
        Inst::Adc { dst, src } => emit_adc(ctx, dst, src, false),
        Inst::Sbb { dst, src } => emit_adc(ctx, dst, src, true),
        Inst::MulWide {
            signed,
            dst,
            lhs,
            rhs,
        } => {
            let mnemonic = if *signed { "smull" } else { "umull" };
            ctx.emitter.puts(&format!(
                "{} {}, {}, {}",
                mnemonic,
                gpr(*dst, Width::B64)?,
                gpr(*lhs, Width::B32)?,
                gpr(*rhs, Width::B32)?
            ));
            Ok(())
        }
        Inst::MulHigh { signed, rhs } => {
            let r = op_to_reg(ctx, rhs, Width::B64, SCRATCH)?;
            let mnemonic = if *signed { "smulh" } else { "umulh" };
            ctx.emitter.puts(&format!(
                "{} {}, {}, {}",
                mnemonic,
                gpr(T2, Width::B64)?,
                gpr(T0, Width::B64)?,
                r
            ));
            ctx.emitter.puts(&format!(
                "mul {}, {}, {}",
                gpr(T0, Width::B64)?,
                gpr(T0, Width::B64)?,
                r
            ));
            Ok(())
        }
        Inst::DivMod1 { signed, w, divisor } => emit_divmod1(ctx, *signed, *w, divisor),
        Inst::Div3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        } => emit_div3(ctx, *signed, *w, *dst, dvd, dvs, false),
        Inst::Rem3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        } => emit_div3(ctx, *signed, *w, *dst, dvd, dvs, true),
        Inst::Extend {
            from,
            to,
            sx,
            dst,
            src,
        } => emit_extend(ctx, *from, *to, *sx, *dst, src),
        Inst::Ctz { w, dst, src } => {
            let vw = view(*w);
            let s = op_to_reg(ctx, src, *w, SCRATCH)?;
            let t = gpr(SCRATCH2, vw)?;
            ctx.emitter.puts(&format!("rbit {}, {}", t, s));
            ctx.emitter.puts(&format!("clz {}, {}", gpr(*dst, vw)?, t));
            Ok(())
        }
        Inst::Clz { w, dst, src } => {
            let s = op_to_reg(ctx, src, *w, SCRATCH)?;
            ctx.emitter
                .puts(&format!("clz {}, {}", gpr(*dst, view(*w))?, s));
            Ok(())
        }
        Inst::Popcnt { w, dst, src } => emit_popcnt(ctx, *w, *dst, src),
        Inst::Cqo { quad } => {
            let hi = gpr(T2, Width::B64)?;
            if *quad {
                ctx.emitter
                    .puts(&format!("asr {}, {}, #63", hi, gpr(T0, Width::B64)?));
            } else {
                ctx.emitter
                    .puts(&format!("sxtw {}, {}", hi, gpr(T0, Width::B32)?));
            }
            Ok(())
        }
        Inst::AddShifted {
            dst,
            lhs,
            rhs,
            amount,
        } => {
            ctx.emitter.puts(&format!(
                "add {}, {}, {}, lsl #{}",
                gpr(*dst, Width::B64)?,
                gpr(*lhs, Width::B64)?,
                gpr(*rhs, Width::B64)?,
                amount
            ));
            Ok(())
        }
        Inst::Cmov {
            w,
            zero,
            dst,
            src,
            test,
        } => {
            let vw = view(*w);
            let d = gpr(*dst, vw)?;
            let s = op_to_reg(ctx, src, *w, SCRATCH)?;
            ctx.emitter.puts(&format!("cmp {}, #0", gpr(*test, vw)?));
            ctx.emitter.puts(&format!(
                "csel {}, {}, {}, {}",
                d,
                s,
                d,
                if *zero { "eq" } else { "ne" }
            ));
            Ok(())
        }
        Inst::VecExtract { w, dst, src, lane } => {
            let (reg, suffix) = match w {
                Width::B8 => (gpr(*dst, Width::B32)?, 'b'),
                Width::B16 => (gpr(*dst, Width::B32)?, 'h'),
                Width::B32 => (gpr(*dst, Width::B32)?, 's'),
                Width::B64 => (gpr(*dst, Width::B64)?, 'd'),
            };
            ctx.emitter
                .puts(&format!("umov {}, v{}.{}[{}]", reg, src.0, suffix, lane));
            Ok(())
        }
        Inst::Branch {
            cc,
            w,
            lhs,
            rhs,
            target,
            ..
        } => emit_branch(ctx, *cc, *w, lhs, rhs, *target),
        Inst::TestBranch {
            w,
            value,
            mask,
            test,
            target,
            ..
        } => emit_test_branch(ctx, *w, value, mask.as_ref(), *test, *target),
        Inst::OpBranch {
            op,
            w,
            flag,
            args,
            target,
            ..
        } => op_branch(ctx, *op, *w, *flag, args.as_slice(), *target),
        Inst::FlagBranch { flag, target, .. } => {
            let label = text::label_text(ctx, *target)?;
            ctx.emitter.puts(&format!("b.{} {}", flag_cc(*flag), label));
            Ok(())
        }
        Inst::Jump { target, .. } => emit_jump(ctx, target, false),
        Inst::Call { target, .. } => emit_jump(ctx, target, true),
        Inst::Ret => {
            ctx.emitter.puts("ret");
            Ok(())
        }
        Inst::Break => {
            // Debugger trap. GAS spells the encoding `brk #0`.
            ctx.emitter.puts("brk #0");
            Ok(())
        }
        Inst::Nop => {
            ctx.emitter.puts("nop");
            Ok(())
        }
        Inst::IntSet {
            cc,
            w,
            dst,
            lhs,
            rhs,
        } => {
            let cc = emit_cmp(ctx, *w, *cc, lhs, rhs)?;
            emit_set(ctx, *w, dst, int_cc(cc))
        }
        Inst::TestSet {
            w,
            value,
            mask,
            test,
            dst,
        } => {
            test_flags(ctx, *w, value, mask.as_ref())?;
            let cond = match test {
                TestKind::Sign => "mi",
                TestKind::Zero => "eq",
                TestKind::NonZero => "ne",
            };
            emit_set(ctx, *w, dst, cond)
        }
        Inst::FArith { op, k, arith } => emit_farith(ctx, *op, *k, arith),
        Inst::Fma {
            op,
            k,
            a,
            b,
            c,
            dst,
        } => emit_fma(ctx, *op, *k, a, b, c, *dst),
        Inst::FSqrt { k, dst, src } => {
            let s = fp_src(ctx, *k, src)?;
            ctx.emitter.puts(&format!("fsqrt {}, {}", fpr(*dst, *k), s));
            Ok(())
        }
        Inst::FRound { k, mode, dst, src } => {
            let mnemonic = match mode {
                RoundMode::Nearest => "frintn",
                RoundMode::Down => "frintm",
                RoundMode::Up => "frintp",
                RoundMode::Trunc => "frintz",
            };
            let s = fp_src(ctx, *k, src)?;
            ctx.emitter
                .puts(&format!("{} {}, {}", mnemonic, fpr(*dst, *k), s));
            Ok(())
        }
        Inst::FAbs { k, dst, src } | Inst::FNeg { k, dst, src } => {
            let mnemonic = if matches!(inst, Inst::FAbs { .. }) {
                "fabs"
            } else {
                "fneg"
            };
            let s = fp_src(ctx, *k, src)?;
            ctx.emitter
                .puts(&format!("{} {}, {}", mnemonic, fpr(*dst, *k), s));
            Ok(())
        }
        Inst::FBit { or, k, dst, src } => {
            let s = fp_src_id(ctx, *k, src)?;
            let d = vreg(*dst);
            let mnemonic = if *or { "orr" } else { "and" };
            ctx.emitter.puts(&format!(
                "{} {}.16b, {}.16b, {}.16b",
                mnemonic,
                d,
                d,
                vreg(s)
            ));
            Ok(())
        }
        Inst::CvtFI { k, w, dst, src } => {
            let s = fp_src(ctx, *k, src)?;
            let d = gpr(*dst, view(*w))?;
            ctx.emitter.puts(&format!("fcvtzs {}, {}", d, s));
            let wide = view(*w) == Width::B64;
            let max = if wide { i64::MAX } else { i64::from(i32::MAX) };
            let sentinel = if wide { i64::MIN } else { i64::from(i32::MIN) };
            let t = gpr(SCRATCH, view(*w))?;
            mov_imm(ctx, &t, wide, max)?;
            ctx.emitter.puts(&format!("cmp {}, {}", d, t));
            let pos_ok = text::synth_name(ctx, "cvtfiPosOk", 0);
            ctx.emitter.puts(&format!("b.ne {}", pos_ok));
            mov_imm(ctx, &d, wide, sentinel)?;
            ctx.emitter.puts_local_label(&pos_ok);
            ctx.emitter.puts(&format!("fcmp {}, {}", s, s));
            let nan_ok = text::synth_name(ctx, "cvtfiNanOk", 0);
            ctx.emitter.puts(&format!("b.vc {}", nan_ok));
            mov_imm(ctx, &d, wide, sentinel)?;
            ctx.emitter.puts_local_label(&nan_ok);
            Ok(())
        }
        Inst::CvtIF {
            signed,
            from,
            k,
            dst,
            src,
        } => {
            let s = op_to_reg(ctx, src, *from, SCRATCH)?;
            ctx.emitter.puts(&format!(
                "{} {}, {}",
                if *signed { "scvtf" } else { "ucvtf" },
                fpr(*dst, *k),
                s
            ));
            Ok(())
        }
        Inst::CvtFF { from, to, dst, src } => {
            let s = fp_src(ctx, *from, src)?;
            ctx.emitter.puts(&format!("fcvt {}, {}", fpr(*dst, *to), s));
            Ok(())
        }
        Inst::Bitcast { dir, dst, src } => emit_bitcast(ctx, *dir, dst, src),
        Inst::BranchF {
            cc,
            k,
            lhs,
            rhs,
            target,
            ..
        } => emit_branch_f(ctx, *cc, *k, lhs, rhs, *target),
        Inst::FSet {
            cc,
            k,
            dst,
            lhs,
            rhs,
        } => emit_fset(ctx, *cc, *k, dst, lhs, rhs),
        Inst::Fence { full } => {
            ctx.emitter.puts(if *full { "dmb sy" } else { "dmb ish" });
            Ok(())
        }
        Inst::Pause => {
            ctx.emitter.puts("yield");
            Ok(())
        }
        Inst::TlsLoad { w, dst, idx } => emit_tls(ctx, *w, *dst, *idx, true),
        Inst::TlsStore { w, src, idx } => emit_tls(ctx, *w, *src, *idx, false),
        Inst::TlsLea { dst, idx } => emit_tls_lea(ctx, *dst, *idx),
        Inst::AtomicRmw { op, w, a, b } => emit_rmw(ctx, *op, *w, a, b),
        Inst::AtomicCas {
            w,
            mem,
            src,
            branch,
        } => emit_cas(ctx, *w, mem, *src, branch.as_ref()),
        Inst::LoadLinked { w, mem, dst } => {
            let mnemonic = match w {
                Width::B8 => "ldaxrb",
                Width::B16 => "ldaxrh",
                Width::B32 | Width::B64 => "ldaxr",
            };
            let addr = addr_base_only(ctx, mem)?;
            ctx.emitter
                .puts(&format!("{} {}, {}", mnemonic, gpr(*dst, view(*w))?, addr));
            Ok(())
        }
        Inst::StoreCond {
            w,
            status,
            src,
            mem,
        } => {
            let mnemonic = match w {
                Width::B8 => "stlxrb",
                Width::B16 => "stlxrh",
                Width::B32 | Width::B64 => "stlxr",
            };
            let aliased = status.0 == src.0
                || mem.base == Some(*status)
                || mem.index.map(|(r, _)| r) == Some(*status);
            if aliased {
                let addr = format!("[{}]", synth_addr(ctx, mem)?);
                ctx.emitter.puts(&format!(
                    "{} {}, {}, {}",
                    mnemonic,
                    gpr(SCRATCH2, Width::B32)?,
                    gpr(*src, view(*w))?,
                    addr
                ));
                ctx.emitter.puts(&format!(
                    "mov {}, {}",
                    gpr(*status, Width::B32)?,
                    gpr(SCRATCH2, Width::B32)?
                ));
            } else {
                let addr = addr_base_only(ctx, mem)?;
                ctx.emitter.puts(&format!(
                    "{} {}, {}, {}",
                    mnemonic,
                    // The status is always a 32-bit register, even in the
                    // 64-bit form (`STLXR Ws, Xt, [Xn]`).
                    gpr(*status, Width::B32)?,
                    gpr(*src, view(*w))?,
                    addr
                ));
            }
            Ok(())
        }
        Inst::PairLoad { w, dst1, dst2, mem } => emit_pair(ctx, *w, dst1, dst2, mem, true),
        Inst::PairStore { w, src1, src2, mem } => emit_pair(ctx, *w, src1, src2, mem, false),
    }
}

fn arm64e_register(
    node: &Node,
    ctx: &mut LowerCtx,
    flags: LabelFlags<'_>,
) -> Result<String, String> {
    match super::frontend::operand_to_op(node, ctx, flags, TextTarget::Aarch64)? {
        Op::Gpr(g) => gpr(g, Width::B64),
        Op::Fpr(f) => Ok(fpr(f, FKind::F64)),
        other => Err(format!(
            "arm64e: expected a register operand, got {:?}",
            other
        )),
    }
}

pub fn lower_arm64e(
    mnemonic: Mnemonic,
    operands: &[Node],
    ctx: &mut LowerCtx,
    flags: LabelFlags<'_>,
) -> Result<Option<()>, String> {
    match mnemonic {
        Mnemonic::Ret => {
            ctx.emitter.puts("retab");
            Ok(Some(()))
        }

        Mnemonic::Call | Mnemonic::Jmp => {
            if operands.len() < 2 || !operands[0].is_register_node() {
                return Ok(None);
            }
            let target = arm64e_register(&operands[0], ctx, flags)?;
            if mnemonic == Mnemonic::Call && operands[1].immediate_value() == Some(2) {
                ctx.emitter.puts(&format!("blraaz {}", target));
                return Ok(Some(()));
            }
            if !operands[1].is_register_node() {
                return Ok(None);
            }
            let modifier = arm64e_register(&operands[1], ctx, flags)?;
            ctx.emitter.puts(&format!(
                "{} {}, {}",
                if mnemonic == Mnemonic::Call {
                    "blrab"
                } else {
                    "brab"
                },
                target,
                modifier
            ));
            Ok(Some(()))
        }
        Mnemonic::TagCodePtr => {
            if operands.len() != 2
                || !operands[0].is_register_node()
                || !operands[1].is_register_node()
            {
                return Ok(None);
            }
            let dst = arm64e_register(&operands[0], ctx, flags)?;
            let src = arm64e_register(&operands[1], ctx, flags)?;
            ctx.emitter.puts(&format!("pacib {}, {}", dst, src));
            Ok(Some(()))
        }
        Mnemonic::TagReturnAddress | Mnemonic::UntagReturnAddress => {
            if operands.is_empty() || !operands[0].is_register_node() {
                return Ok(None);
            }
            let signed = mnemonic == Mnemonic::TagReturnAddress;
            let instruction = if signed { "pacib" } else { "autib" };
            let resolved =
                super::frontend::operand_to_op(&operands[0], ctx, flags, TextTarget::Aarch64)?;
            if matches!(resolved, Op::Gpr(g) if g == SP) {
                ctx.emitter.puts(if signed { "pacibsp" } else { "autibsp" });
            } else {
                let reg = match resolved {
                    Op::Gpr(g) => gpr(g, Width::B64)?,
                    Op::Fpr(f) => fpr(f, FKind::F64),
                    other => {
                        return Err(format!(
                            "arm64e: expected a register operand, got {:?}",
                            other
                        ))
                    }
                };
                ctx.emitter.puts(&format!("{} lr, {}", instruction, reg));
            }
            Ok(Some(()))
        }
        Mnemonic::RemoveCodePtrTag => {
            if operands.is_empty() || !operands[0].is_register_node() {
                return Ok(None);
            }
            let reg = arm64e_register(&operands[0], ctx, flags)?;
            ctx.emitter.puts(&format!("xpaci {}", reg));
            Ok(Some(()))
        }
        Mnemonic::UntagArrayPtr => {
            if operands.len() != 2
                || !operands[0].is_register_node()
                || !operands[1].is_register_node()
            {
                return Ok(None);
            }
            let dst = arm64e_register(&operands[0], ctx, flags)?;
            let src = arm64e_register(&operands[1], ctx, flags)?;
            ctx.emitter.puts(&format!("autdb {}, {}", dst, src));
            Ok(Some(()))
        }
        Mnemonic::RemoveArrayPtrTag => {
            if operands.is_empty() || !operands[0].is_register_node() {
                return Ok(None);
            }
            let reg = arm64e_register(&operands[0], ctx, flags)?;
            ctx.emitter.puts(&format!("xpacd {}", reg));
            Ok(Some(()))
        }
        _ => Ok(None),
    }
}
