//! AArch64 lowering.

use crate::ir::{
    expand, Alu3, AluOp, AtomicOp, BitcastDir, FAlu, FArith3, FCc, FKind, FlagAlu, FmaOp, Fpr,
};
use crate::ir::{Disp, PatchHandle, PredFlag, RoundMode, Scratch, ShiftCnt, Sx, TestKind};
use crate::ir::{Extern, Reach};
use crate::ir::{
    Gpr, Inst, IntCc, LabelResolver, Lbl, LeaSrc, LowerError, Mem, Mnemonic, Op, PairW,
};
use crate::ir::{ShiftOp, Target as IrTarget, Width};
use asmkit::aarch64::Mem as AMem;
use asmkit::aarch64::*;
use asmkit::{
    imm, CondCode, Label, Operand, OperandCast, PatchableJump, RegType, Reloc, RelocTarget, Sym,
};

/// The `t0` accumulator role (`x0`): dividend/quotient, CAS expected value.
const T0: Gpr = Gpr(0);
/// The `t2` accumulator role (`x2`): multiply high half.
const T2: Gpr = Gpr(2);
/// Address and immediate synthesis scratch (`x16`).
const SCRATCH: Gpr = Gpr(16);
/// Second synthesis scratch (`x17`).
const SCRATCH2: Gpr = Gpr(17);
/// Float/vector synthesis scratch (`v31`).
const FSCRATCH: Fpr = Fpr(31);
/// The stack pointer.
const SP: Gpr = Gpr(31);
/// The zero register.
pub const ZR: Gpr = Gpr(63);

fn x(g: Gpr) -> Gp {
    if g == ZR {
        return regs::zr;
    }
    assert!(g.0 <= 31, "onlineasm: aarch64 GPR id {} out of range", g.0);
    Gp::make_x(u32::from(g.0))
}

fn wv(g: Gpr) -> Gp {
    if g == ZR {
        return regs::wzr;
    }
    assert!(g.0 <= 31, "onlineasm: aarch64 GPR id {} out of range", g.0);
    Gp::make_w(u32::from(g.0))
}

fn gpr(g: Gpr, w: Width) -> Gp {
    if w == Width::B64 {
        x(g)
    } else {
        wv(g)
    }
}

fn view(w: Width) -> Width {
    if w == Width::B64 {
        Width::B64
    } else {
        Width::B32
    }
}

fn is_wide(r: Gp) -> bool {
    r.is_gp64()
}

fn id_of(r: Gp) -> Gpr {
    Gpr(r.id() as u8)
}

fn fpr(f: Fpr, k: FKind) -> Vec {
    match k {
        FKind::F32 => Vec::make_v32(u32::from(f.0)),
        FKind::F64 => Vec::make_v64(u32::from(f.0)),
    }
}

fn qreg(f: Fpr) -> Vec {
    Vec::make_v128(u32::from(f.0))
}

fn hreg(f: Fpr) -> Vec {
    Vec::make_v16(u32::from(f.0))
}

pub fn gpr_id(g: Gp) -> Gpr {
    Gpr(g.id() as u8)
}

pub fn fpr_id(v: Vec) -> Fpr {
    Fpr(v.id() as u8)
}

fn bad(mn: Mnemonic, msg: impl Into<String>) -> LowerError {
    LowerError::BadOperand {
        mnemonic: mn.to_string(),
        msg: msg.into(),
    }
}

fn go(r: Gp) -> Operand {
    *r.as_operand()
}

fn vo(v: Vec) -> Operand {
    *v.as_operand()
}

fn mo(m: AMem) -> Operand {
    *m.as_operand()
}

fn io(v: i64) -> Operand {
    *imm(v).as_operand()
}

fn lsl_by(n: u32) -> Operand {
    io(i64::from(n))
}

fn e(asm: &mut Assembler, id: InstId, ops: &[Operand]) {
    // `emit_n` takes `&[&Operand]`. Almost every instruction has a handful
    // of operands, so build that slice on the stack and keep the hot path
    // off the heap. Six is asmkit's operand limit.
    //
    // Lowering only ever builds operands it has already checked, so release
    // builds skip asmkit's per-operand validation. Debug builds keep it.
    let id = id as u32;
    #[cfg(debug_assertions)]
    let emit = |asm: &mut Assembler, ops: &[&Operand]| asm.emit_n(id, ops);
    #[cfg(not(debug_assertions))]
    let emit = |asm: &mut Assembler, ops: &[&Operand]| asm.emit_n_unchecked(id, ops);
    match ops {
        [a] => emit(asm, &[a]),
        [a, b] => emit(asm, &[a, b]),
        [a, b, c] => emit(asm, &[a, b, c]),
        [a, b, c, d] => emit(asm, &[a, b, c, d]),
        _ => {
            let refs: smallvec::SmallVec<[&Operand; 6]> = ops.iter().collect();
            emit(asm, &refs);
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Cc {
    Eq,
    Ne,
    Hi,
    Hs,
    Lo,
    Ls,
    Gt,
    Ge,
    Lt,
    Le,
    Mi,
    Pl,
    Vs,
    Vc,
}

impl Cc {
    fn code(self) -> CondCode {
        match self {
            Cc::Eq => CondCode::EQ,
            Cc::Ne => CondCode::NE,
            Cc::Hi => CondCode::HI,
            Cc::Hs => CondCode::CS,
            Cc::Lo => CondCode::CC,
            Cc::Ls => CondCode::LS,
            Cc::Gt => CondCode::GT,
            Cc::Ge => CondCode::GE,
            Cc::Lt => CondCode::LT,
            Cc::Le => CondCode::LE,
            Cc::Mi => CondCode::MI,
            Cc::Pl => CondCode::PL,
            Cc::Vs => CondCode::VS,
            Cc::Vc => CondCode::VC,
        }
    }

    fn operand(self) -> Operand {
        io(self.code() as i64)
    }

    fn invert(self) -> Cc {
        match self {
            Cc::Eq => Cc::Ne,
            Cc::Ne => Cc::Eq,
            Cc::Hi => Cc::Ls,
            Cc::Hs => Cc::Lo,
            Cc::Lo => Cc::Hs,
            Cc::Ls => Cc::Hi,
            Cc::Gt => Cc::Le,
            Cc::Ge => Cc::Lt,
            Cc::Lt => Cc::Ge,
            Cc::Le => Cc::Gt,
            Cc::Mi => Cc::Pl,
            Cc::Pl => Cc::Mi,
            Cc::Vs => Cc::Vc,
            Cc::Vc => Cc::Vs,
        }
    }
}

fn int_cc(cc: IntCc) -> Cc {
    match cc {
        IntCc::Eq => Cc::Eq,
        IntCc::Ne => Cc::Ne,
        IntCc::Hi => Cc::Hi,
        IntCc::Hs => Cc::Hs,
        IntCc::Lo => Cc::Lo,
        IntCc::Ls => Cc::Ls,
        IntCc::Gt => Cc::Gt,
        IntCc::Ge => Cc::Ge,
        IntCc::Lt => Cc::Lt,
        IntCc::Le => Cc::Le,
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

fn flag_cc(flag: PredFlag) -> Cc {
    match flag {
        PredFlag::O => Cc::Vs,
        PredFlag::S => Cc::Mi,
        PredFlag::Z => Cc::Eq,
        PredFlag::Nz => Cc::Ne,
    }
}

fn test_cc(test: TestKind) -> Cc {
    match test {
        TestKind::Sign => Cc::Mi,
        TestKind::Zero => Cc::Eq,
        TestKind::NonZero => Cc::Ne,
    }
}

fn b_cond(asm: &mut Assembler, cc: Cc, target: Label) {
    match cc {
        Cc::Eq => asm.b_eq(target),
        Cc::Ne => asm.b_ne(target),
        Cc::Hi => asm.b_hi(target),
        Cc::Hs => asm.b_hs(target),
        Cc::Lo => asm.b_lo(target),
        Cc::Ls => asm.b_ls(target),
        Cc::Gt => asm.b_gt(target),
        Cc::Ge => asm.b_ge(target),
        Cc::Lt => asm.b_lt(target),
        Cc::Le => asm.b_le(target),
        Cc::Mi => asm.b_mi(target),
        Cc::Pl => asm.b_pl(target),
        Cc::Vs => asm.b_vs(target),
        Cc::Vc => asm.b_vc(target),
    }
}

#[derive(Clone, Copy)]
enum Br {
    Cond(Cc),
    Cbz(Gp),
    Cbnz(Gp),
    Tbnz(Gp, u32),
}

impl Br {
    fn emit(self, asm: &mut Assembler, target: Label) {
        match self {
            Br::Cond(cc) => b_cond(asm, cc, target),
            Br::Cbz(r) => asm.cbz(r, target),
            Br::Cbnz(r) => asm.cbnz(r, target),
            Br::Tbnz(r, bit) => asm.tbnz(r, imm(i64::from(bit)), target),
        }
    }

    fn invert(self, asm: &mut Assembler, target: Label) {
        match self {
            Br::Cond(cc) => b_cond(asm, cc.invert(), target),
            Br::Cbz(r) => asm.cbnz(r, target),
            Br::Cbnz(r) => asm.cbz(r, target),
            Br::Tbnz(r, bit) => asm.tbz(r, imm(i64::from(bit)), target),
        }
    }
}

impl crate::IntoOperand for Gp {
    fn into_operand<const BACKWARD: bool>(self, _asm: &crate::Assembler<BACKWARD>) -> Op {
        Op::Gpr(gpr_id(self))
    }
}

impl crate::IntoOperand for Vec {
    fn into_operand<const BACKWARD: bool>(self, _asm: &crate::Assembler<BACKWARD>) -> Op {
        Op::Fpr(fpr_id(self))
    }
}

use crate::TargetInfo;
use asmkit::CodeBuffer;

pub(crate) fn lower(
    buf: &mut CodeBuffer,
    ctx: &Scratch,
    labels: &[asmkit::Label],
    label_base: u32,
    mnemonic: Mnemonic,
    ops: &[Op],
    abi: crate::Abi,
) -> Result<(), LowerError> {
    let mut asm = asmkit::aarch64::Assembler::new(buf);
    let mut res = LabelResolver::new(labels, label_base);
    lower_ops(&mut asm, ctx, mnemonic, ops, &mut res, abi)
}

pub(crate) fn lower_patched(
    buf: &mut CodeBuffer,
    ctx: &Scratch,
    labels: &[asmkit::Label],
    label_base: u32,
    mnemonic: Mnemonic,
    ops: &[Op],
    abi: crate::Abi,
) -> Result<PatchHandle, LowerError> {
    let mut asm = asmkit::aarch64::Assembler::new(buf);
    let mut res = LabelResolver::new(labels, label_base);
    lower_ops_patched(&mut asm, ctx, mnemonic, ops, &mut res, abi)
}

pub(crate) static INFO: TargetInfo = {
    let t = offlineasm_ir::regs::AARCH64;
    TargetInfo {
        scratch: t.scratch,
        registers: t.registers,
        vreg_gpr: t.vreg_gpr,
        vreg_fpr: t.vreg_fpr,
        lower,
        lower_patched,
    }
};

pub fn lower_ops(
    asm: &mut Assembler,
    ctx: &Scratch,
    mnemonic: Mnemonic,
    ops: &[Op],
    res: &mut LabelResolver,
    abi: crate::Abi,
) -> Result<(), LowerError> {
    crate::ir::check_callee_saved(mnemonic, ops, &[19, 20, 21, 22, 23, 24, 25, 26, 27, 28])?;
    if matches!(
        mnemonic,
        Mnemonic::Push | Mnemonic::Pop | Mnemonic::PushCalleeSaves | Mnemonic::PopCalleeSaves
    ) {
        let mut l = Lx {
            asm,
            mn: mnemonic,
            res,
            abi,
            err: None,
        };
        let r = l.stack_group(ops);
        return match l.err.take() {
            Some(e) => Err(e),
            None => r,
        };
    }
    if try_fast_emit(asm, res, mnemonic, ops) {
        return Ok(());
    }
    let insts = expand(mnemonic, ops, ctx, false)?;
    for inst in &insts {
        let handle = emit_inst(asm, mnemonic, inst, res, abi)?;
        debug_assert!(handle.is_none(), "unpatched lowering emitted a patch site");
    }
    Ok(())
}

/// Emits through asmkit, skipping validation in release builds (lowering
/// only produces operands it has already checked).
#[inline]
fn emit_fast(asm: &mut Assembler, id: u32, ops: &[&Operand]) {
    #[cfg(debug_assertions)]
    asm.emit_n(id, ops);
    #[cfg(not(debug_assertions))]
    asm.emit_n_unchecked(id, ops);
}

/// Lowers the simplest mnemonic forms without materialising the IR
/// expansion, calling asmkit directly instead.
///
/// Every arm matches only shapes that lower to the same instruction
/// sequence as the generic path; anything else falls through to `expand`,
/// which also produces the diagnostics for invalid operand shapes.
fn try_fast_emit(asm: &mut Assembler, res: &LabelResolver, mn: Mnemonic, ops: &[Op]) -> bool {
    match mn {
        Mnemonic::Nop if ops.is_empty() => {
            emit_fast(asm, InstId::Nop as u32, &[]);
            true
        }
        Mnemonic::Ret if ops.is_empty() => {
            let operand = go(x(Gpr(30)));
            emit_fast(asm, InstId::Ret as u32, &[&operand]);
            true
        }
        Mnemonic::Add(w) => fast_alu(asm, w, AluKind::Add, ops),
        Mnemonic::Sub(w) => fast_alu(asm, w, AluKind::Sub, ops),
        Mnemonic::Mul(w) => fast_alu(asm, w, AluKind::Mul, ops),
        Mnemonic::And(w) => fast_alu(asm, w, AluKind::And, ops),
        Mnemonic::Or(w) => fast_alu(asm, w, AluKind::Or, ops),
        Mnemonic::Xor(w) => fast_alu(asm, w, AluKind::Xor, ops),
        Mnemonic::Move => fast_move(asm, ops),
        Mnemonic::Load(w) => fast_load_store(asm, w, ops, false),
        Mnemonic::Store(w) => fast_load_store(asm, w, ops, true),
        Mnemonic::Jmp => fast_jump(asm, res, ops, false),
        Mnemonic::Call => fast_jump(asm, res, ops, true),
        Mnemonic::FlagBranch(flag) => fast_flag_branch(asm, res, flag, ops),
        Mnemonic::IntBranch { w, cc } => fast_int_branch(asm, res, w, cc, ops),
        Mnemonic::OpBranch { op, w, flag } => fast_op_branch(asm, res, op, w, flag, ops),
        _ => false,
    }
}

/// Resolves the backend label of a branch target, when it is a label that
/// already exists in this image.
#[inline]
fn branch_label(res: &LabelResolver, op: &Op) -> Option<Label> {
    match op {
        Op::Label(Lbl::Bound(h)) => res.get(*h),
        _ => None,
    }
}

fn fast_jump(asm: &mut Assembler, res: &LabelResolver, ops: &[Op], call: bool) -> bool {
    let [Op::Label(_)] = ops else {
        return false;
    };
    let Some(target) = branch_label(res, &ops[0]) else {
        return false;
    };
    let id = if call { InstId::Bl } else { InstId::B };
    emit_fast(asm, id as u32, &[target.as_operand()]);
    true
}

fn fast_flag_branch(asm: &mut Assembler, res: &LabelResolver, flag: PredFlag, ops: &[Op]) -> bool {
    let [Op::Label(_)] = ops else {
        return false;
    };
    let Some(target) = branch_label(res, &ops[0]) else {
        return false;
    };
    let id = InstId::B.with_cc(flag_cc(flag).code());
    emit_fast(asm, id, &[target.as_operand()]);
    true
}

fn fast_int_branch(
    asm: &mut Assembler,
    res: &LabelResolver,
    w: Width,
    cc: IntCc,
    ops: &[Op],
) -> bool {
    if !matches!(w, Width::B32 | Width::B64) {
        return false;
    }
    let [Op::Gpr(lhs), Op::Gpr(rhs), target] = ops else {
        return false;
    };
    let Some(target) = branch_label(res, target) else {
        return false;
    };
    if lhs.0 > 30 || rhs.0 > 30 {
        return false;
    }
    let vw = view(w);
    let operands = [go(gpr(*lhs, vw)), go(gpr(*rhs, vw))];
    emit_fast(asm, InstId::Cmp as u32, &[&operands[0], &operands[1]]);
    let id = InstId::B.with_cc(int_cc(cc).code());
    emit_fast(asm, id, &[target.as_operand()]);
    true
}

fn fast_op_branch(
    asm: &mut Assembler,
    res: &LabelResolver,
    op: FlagAlu,
    w: Width,
    flag: PredFlag,
    ops: &[Op],
) -> bool {
    if !matches!(w, Width::B32 | Width::B64) {
        return false;
    }
    let Some((target, leading)) = ops.split_last() else {
        return false;
    };
    let k = match op {
        FlagAlu::Add => AluKind::Add,
        FlagAlu::Sub => AluKind::Sub,
        _ => return false,
    };
    let (d, l, r) = match leading {
        [Op::Gpr(d), Op::Gpr(r)] => (*d, *d, *r),
        [Op::Gpr(d), Op::Gpr(l), Op::Gpr(r)] => (*d, *l, *r),
        _ => return false,
    };
    let Some(target) = branch_label(res, target) else {
        return false;
    };
    if d.0 > 30 || l.0 > 30 || r.0 > 30 {
        return false;
    }
    let vw = view(w);
    let operands = [go(gpr(d, vw)), go(gpr(l, vw)), go(gpr(r, vw))];
    emit_fast(
        asm,
        k.id(true) as u32,
        &[&operands[0], &operands[1], &operands[2]],
    );
    let id = InstId::B.with_cc(flag_cc(flag).code());
    emit_fast(asm, id, &[target.as_operand()]);
    true
}

fn fast_alu(asm: &mut Assembler, w: Width, k: AluKind, ops: &[Op]) -> bool {
    if !matches!(w, Width::B32 | Width::B64) {
        return false;
    }
    let (d, l, r) = match ops {
        [Op::Gpr(d), Op::Gpr(r)] => (*d, *d, *r),
        [Op::Gpr(d), Op::Gpr(l), Op::Gpr(r)] => (*d, *l, *r),
        _ => return false,
    };
    if d.0 > 30 || l.0 > 30 || r.0 > 30 {
        return false;
    }

    let vw = view(w);
    let operands = [go(gpr(d, vw)), go(gpr(l, vw)), go(gpr(r, vw))];
    emit_fast(
        asm,
        k.id(false) as u32,
        &[&operands[0], &operands[1], &operands[2]],
    );
    true
}

fn fast_move(asm: &mut Assembler, ops: &[Op]) -> bool {
    match ops {
        [Op::Gpr(d), Op::Gpr(s)] => {
            if d.0 > 30 || s.0 > 30 {
                return false;
            }
            let operands = [go(x(*d)), go(x(*s))];
            emit_fast(asm, InstId::Mov as u32, &[&operands[0], &operands[1]]);
            true
        }
        [Op::Gpr(d), Op::Imm(v)] => {
            if d.0 > 30 {
                return false;
            }
            emit_mov_imm(asm, x(*d), *v);
            true
        }
        _ => false,
    }
}

/// `movz`/`movn`/`movk` sequence materializing `v` in `reg`.
fn emit_mov_imm(asm: &mut Assembler, reg: Gp, v: i64) {
    let wide = is_wide(reg);
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
        let (id, value) = if first {
            first = false;
            if fill_ones {
                (InstId::Movn, (!chunk) & 0xffff)
            } else {
                (InstId::Movz, chunk)
            }
        } else {
            (InstId::Movk, chunk)
        };
        let operands = [
            go(reg),
            uimm(value),
            if shift == 0 { uimm(0) } else { lsl_by(shift) },
        ];
        let refs = [&operands[0], &operands[1], &operands[2]];
        let len = if shift == 0 { 2 } else { 3 };
        emit_fast(asm, id as u32, &refs[..len]);
    }
}

fn fast_load_store(asm: &mut Assembler, w: Width, ops: &[Op], store: bool) -> bool {
    // `load dst, [base + imm]`; `store [base + imm], src`.
    let (rt, m) = match (store, ops) {
        (false, [Op::Gpr(rt), Op::Mem(m)]) | (true, [Op::Mem(m), Op::Gpr(rt)]) => (*rt, m),
        _ => return false,
    };
    let Some(base) = m.base.filter(|g| g.0 <= 30) else {
        return false;
    };
    if rt.0 > 30 || m.index.is_some() {
        return false;
    }
    let Disp::Const(disp) = m.disp else {
        return false;
    };
    // Only the unsigned-offset form. Any other displacement falls back to
    // the generic lowering, which can synthesize an address.
    let scale = match w {
        Width::B8 => 1,
        Width::B16 => 2,
        Width::B32 => 4,
        Width::B64 => 8,
    };
    if disp < 0 || disp % scale != 0 || disp / scale > 0xFFF {
        return false;
    }
    let id = if store { store_id(w) } else { load_id(w) };
    let operands = [go(gpr(rt, view(w))), mo(ptr(x(base), disp))];
    emit_fast(asm, id as u32, &[&operands[0], &operands[1]]);
    true
}

pub fn lower_ops_patched(
    asm: &mut Assembler,
    ctx: &Scratch,
    mnemonic: Mnemonic,
    ops: &[Op],
    res: &mut LabelResolver,
    abi: crate::Abi,
) -> Result<PatchHandle, LowerError> {
    let insts = expand(mnemonic, ops, ctx, true)?;
    let mut handle = None;
    for inst in &insts {
        if let Some(h) = emit_inst(asm, mnemonic, inst, res, abi)? {
            if handle.is_some() {
                return Err(bad(mnemonic, "expansion emitted several patch sites"));
            }
            handle = Some(h);
        }
    }
    handle.ok_or_else(|| bad(mnemonic, "no patch site in this expansion"))
}

/// Whether `v` is encodable as an AArch64 logical immediate
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

fn logical_imm(v: i64, wide: bool) -> Operand {
    if wide {
        io(v)
    } else {
        io(i64::from(v as u32))
    }
}

fn uimm(v: u64) -> Operand {
    io(v as i64)
}

fn fk_bytes(k: FKind) -> u32 {
    match k {
        FKind::F32 => 4,
        FKind::F64 => 8,
    }
}

fn load_id(w: Width) -> InstId {
    match w {
        Width::B8 => InstId::Ldrb,
        Width::B16 => InstId::Ldrh,
        Width::B32 | Width::B64 => InstId::Ldr,
    }
}

fn store_id(w: Width) -> InstId {
    match w {
        Width::B8 => InstId::Strb,
        Width::B16 => InstId::Strh,
        Width::B32 | Width::B64 => InstId::Str,
    }
}

fn is_sp(op: &Operand) -> bool {
    op.is_reg() && op.is_gp() && op.id() == 31
}

fn sp_allowed(id: InstId, pos: usize, ops: &[Operand]) -> bool {
    match id {
        InstId::Mov => true,
        InstId::Add | InstId::Sub => pos <= 1,
        InstId::Adds | InstId::Subs => pos == 1,
        InstId::Cmp | InstId::Cmn => pos == 0,
        InstId::And | InstId::Orr | InstId::Eor => {
            pos == 0 && ops.get(2).is_some_and(Operand::is_imm)
        }
        _ => false,
    }
}

fn unscaled(id: InstId, ops: &[Operand]) -> InstId {
    let (Some(reg), Some(m)) = (ops.first(), ops.last()) else {
        return id;
    };
    if !m.is_mem() {
        return id;
    }
    let m: AMem = m.as_();
    if m.has_index() || !m.is_fixed_offset() {
        return id;
    }
    let (size, alt) = match id {
        InstId::Ldrb => (1, InstId::Ldurb),
        InstId::Ldrsb => (1, InstId::Ldursb),
        InstId::Strb => (1, InstId::Sturb),
        InstId::Ldrh => (2, InstId::Ldurh),
        InstId::Ldrsh => (2, InstId::Ldursh),
        InstId::Strh => (2, InstId::Sturh),
        InstId::Ldr | InstId::Str => {
            let size = if reg.is_gp64() { 8 } else { 4 };
            (
                size,
                if id == InstId::Ldr {
                    InstId::Ldur
                } else {
                    InstId::Stur
                },
            )
        }
        InstId::Ldr_v | InstId::Str_v => {
            let v: Vec = reg.as_();
            let size = match v.reg_type() {
                RegType::Vec8 => 1,
                RegType::Vec16 => 2,
                RegType::Vec32 => 4,
                RegType::Vec64 => 8,
                _ => 16,
            };
            (
                size,
                if id == InstId::Ldr_v {
                    InstId::Ldur_v
                } else {
                    InstId::Stur_v
                },
            )
        }
        _ => return id,
    };
    let off = m.offset();
    if off >= 0 && off % size == 0 && off < 4096 * size {
        id
    } else {
        alt
    }
}

#[allow(clippy::too_many_lines)]
fn emit_inst(
    asm: &mut Assembler,
    mn: Mnemonic,
    inst: &Inst,
    res: &mut LabelResolver,
    abi: crate::Abi,
) -> Result<Option<PatchHandle>, LowerError> {
    let mut l = Lx {
        asm,
        mn,
        res,
        abi,
        err: None,
    };
    let r = emit_node(&mut l, inst);
    match l.err.take() {
        Some(e) => Err(e),
        None => r,
    }
}

#[allow(clippy::too_many_lines)]
fn emit_node(l: &mut Lx, inst: &Inst) -> Result<Option<PatchHandle>, LowerError> {
    let mn = l.mn;
    let none = Ok(None);
    match inst {
        Inst::Mov { w, dst, src, patch } => {
            if *patch {
                return match (dst, src) {
                    (Op::Gpr(d), Op::Imm(v)) => Ok(Some(PatchHandle::Data(
                        l.asm.patchable_mov(x(*d), *v as u64),
                    ))),
                    _ => Err(LowerError::NotPatchable(mn.to_string())),
                };
            }
            l.emit_mov(*w, dst, src)?;
            none
        }
        Inst::MovZero32 { dst, src } => {
            l.emit_mov(Width::B32, dst, src)?;
            none
        }
        Inst::Bind(lbl) => {
            let t = l.label(*lbl);
            l.asm.bind_label(t);
            none
        }
        Inst::Bswap { w, dst, src } => {
            if !matches!(w, Width::B32 | Width::B64) {
                return Err(bad(mn, "bswap needs a 32/64-bit width"));
            }
            let vw = view(*w);
            match (dst, src) {
                (Op::Gpr(d), src) => {
                    let s = l.op_to_reg(src, *w, SCRATCH)?;
                    l.x(InstId::Rev, &[go(gpr(*d, vw)), go(s)]);
                }
                (Op::Mem(m), Op::Gpr(s)) => {
                    let t = gpr(SCRATCH2, vw);
                    l.x(InstId::Rev, &[go(t), go(gpr(*s, vw))]);
                    let a = l.addr_operand(m, w.bytes())?;
                    l.x(store_id(*w), &[go(t), mo(a)]);
                }
                _ => return Err(bad(mn, "bswap needs a register destination")),
            }
            none
        }
        Inst::Load {
            w,
            sx,
            dst,
            addr,
            acquire,
        } => {
            if *acquire {
                let id = match w {
                    Width::B8 => InstId::Ldarb,
                    Width::B16 => InstId::Ldarh,
                    Width::B32 | Width::B64 => InstId::Ldar,
                };
                let reg = gpr(*dst, view(*w));
                let a = l.addr_base_only(addr)?;
                l.x(id, &[go(reg), mo(a)]);
                return none;
            }
            if !*acquire && addr.base.is_none() && addr.index.is_none() {
                let literal = match (*w, *sx) {
                    (Width::B64, Sx::Zero) => Some((InstId::Ldr, x(*dst))),
                    (Width::B32, Sx::Zero) => Some((InstId::Ldr, gpr(*dst, view(Width::B32)))),
                    (Width::B32, Sx::Sign) => Some((InstId::Ldrsw, x(*dst))),
                    _ => None,
                };
                if let Some((id, reg)) = literal {
                    match addr.disp {
                        Disp::Label(label) => {
                            let t = l.bound_label(label)?;
                            l.x(id, &[go(reg), mo(label_ptr(t, 0))]);
                            return none;
                        }
                        Disp::LabelFar(label) => {
                            l.label_far_load(id, reg, label)?;
                            return none;
                        }
                        _ => {}
                    }
                }
            }
            let id = match (w, sx) {
                (Width::B8, Sx::Zero) => InstId::Ldrb,
                (Width::B8, Sx::Sign) => InstId::Ldrsb,
                (Width::B16, Sx::Zero) => InstId::Ldrh,
                (Width::B16, Sx::Sign) => InstId::Ldrsh,
                (Width::B32 | Width::B64, _) => InstId::Ldr,
            };
            let reg = if *sx == Sx::Sign && matches!(w, Width::B8 | Width::B16) {
                x(*dst)
            } else {
                gpr(*dst, view(*w))
            };
            let a = l.addr_operand(addr, w.bytes())?;
            l.x(id, &[go(reg), mo(a)]);
            none
        }
        Inst::Store { w, src, addr } => {
            let value = match src {
                Op::Gpr(_) | Op::Imm(_) => l.op_to_reg(src, *w, SCRATCH2)?,
                _ => return Err(bad(mn, "store needs a register or immediate source")),
            };
            let a = l.addr_operand(addr, w.bytes())?;
            l.x(store_id(*w), &[go(value), mo(a)]);
            none
        }
        Inst::LoadF { k, dst, addr } => {
            let a = l.addr_operand(addr, fk_bytes(*k))?;
            l.x(InstId::Ldr_v, &[vo(fpr(*dst, *k)), mo(a)]);
            none
        }
        Inst::StoreF { k, src, addr } => {
            let a = l.addr_operand(addr, fk_bytes(*k))?;
            l.x(InstId::Str_v, &[vo(fpr(*src, *k)), mo(a)]);
            none
        }
        Inst::FMov { k, dst, src } => {
            if dst != src {
                l.x(InstId::Fmov_v, &[vo(fpr(*dst, *k)), vo(fpr(*src, *k))]);
            }
            none
        }
        Inst::LoadV { dst, addr } => {
            let a = l.addr_operand(addr, 16)?;
            l.x(InstId::Ldr_v, &[vo(qreg(*dst)), mo(a)]);
            none
        }
        Inst::StoreV { src, addr } => {
            let a = l.addr_operand(addr, 16)?;
            l.x(InstId::Str_v, &[vo(qreg(*src)), mo(a)]);
            none
        }
        Inst::VMov { dst, src } => {
            if dst != src {
                l.x(InstId::Mov_v, &[vo(qreg(*dst).b16()), vo(qreg(*src).b16())]);
            }
            none
        }
        Inst::Lea { w, dst, src } => {
            l.emit_lea(*w, *dst, src)?;
            none
        }
        Inst::Push { op } => {
            let r = l.op_to_reg(op, Width::B64, SCRATCH)?;
            l.x(InstId::Str, &[go(r), mo(ptr_pre(x(SP), -16))]);
            none
        }
        Inst::Pop { op } => {
            match op {
                Op::Gpr(g) => l.x(InstId::Ldr, &[go(x(*g)), mo(ptr_post(x(SP), 16))]),
                Op::Mem(m) => {
                    let t = x(SCRATCH2);
                    l.x(InstId::Ldr, &[go(t), mo(ptr_post(x(SP), 16))]);
                    let a = l.addr_operand(m, 8)?;
                    l.x(InstId::Str, &[go(t), mo(a)]);
                }
                _ => return Err(bad(mn, "pop needs a register or memory operand")),
            }
            none
        }
        Inst::PushV { src } => {
            l.x(InstId::Str_v, &[vo(qreg(*src)), mo(ptr_pre(x(SP), -16))]);
            none
        }
        Inst::PopV { dst } => {
            l.x(InstId::Ldr_v, &[vo(qreg(*dst)), mo(ptr_post(x(SP), 16))]);
            none
        }
        Inst::Peek { disp, dst } => {
            let a = l.stack_slot(*disp);
            l.x(InstId::Ldr, &[go(x(*dst)), mo(a)]);
            none
        }
        Inst::Poke { disp, src } => {
            let a = l.stack_slot(*disp);
            l.x(InstId::Str, &[go(x(*src)), mo(a)]);
            none
        }
        Inst::Add { w, op } => {
            l.alu(AluKind::Add, *w, op, false)?;
            none
        }
        Inst::Sub { w, op } => {
            l.alu(AluKind::Sub, *w, op, false)?;
            none
        }
        Inst::Mul { w, op } => {
            l.alu(AluKind::Mul, *w, op, false)?;
            none
        }
        Inst::And { w, op } => {
            l.alu(AluKind::And, *w, op, false)?;
            none
        }
        Inst::Or { w, op } => {
            l.alu(AluKind::Or, *w, op, false)?;
            none
        }
        Inst::Xor { w, op } => {
            l.alu(AluKind::Xor, *w, op, false)?;
            none
        }
        Inst::Not { w, dst } => {
            l.emit_not_neg(*w, dst, false)?;
            none
        }
        Inst::Neg { w, dst } => {
            l.emit_not_neg(*w, dst, true)?;
            none
        }
        Inst::Shift { w, op, dst, cnt } => {
            l.emit_shift(*w, *op, *dst, cnt);
            none
        }
        Inst::MulImm { w, dst, lhs, imm } => {
            let vw = view(*w);
            let t = gpr(SCRATCH2, vw);
            l.mov_imm(t, *imm);
            l.x(InstId::Mul, &[go(gpr(*dst, vw)), go(gpr(*lhs, vw)), go(t)]);
            none
        }
        Inst::AluS { op, w, alu } => {
            let k = match op {
                AluOp::Add => AluKind::Add,
                AluOp::Sub => AluKind::Sub,
                AluOp::Or => AluKind::Or,
            };
            l.alu(k, *w, alu, true)?;
            none
        }
        Inst::Adc { dst, src } => {
            l.emit_adc(dst, src, false)?;
            none
        }
        Inst::Sbb { dst, src } => {
            l.emit_adc(dst, src, true)?;
            none
        }
        Inst::MulWide {
            signed,
            dst,
            lhs,
            rhs,
        } => {
            let id = if *signed {
                InstId::Smull
            } else {
                InstId::Umull
            };
            l.x(id, &[go(x(*dst)), go(wv(*lhs)), go(wv(*rhs))]);
            none
        }
        Inst::MulHigh { signed, rhs } => {
            let r = l.op_to_reg(rhs, Width::B64, SCRATCH)?;
            let id = if *signed {
                InstId::Smulh
            } else {
                InstId::Umulh
            };
            l.x(id, &[go(x(T2)), go(x(T0)), go(r)]);
            l.x(InstId::Mul, &[go(x(T0)), go(x(T0)), go(r)]);
            none
        }
        Inst::DivMod1 { signed, w, divisor } => {
            l.emit_divmod1(*signed, *w, divisor)?;
            none
        }
        Inst::Div3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        } => {
            l.emit_div3(*signed, *w, *dst, dvd, dvs, false)?;
            none
        }
        Inst::Rem3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        } => {
            l.emit_div3(*signed, *w, *dst, dvd, dvs, true)?;
            none
        }
        Inst::Extend {
            from,
            to,
            sx,
            dst,
            src,
        } => {
            l.emit_extend(*from, *to, *sx, *dst, src)?;
            none
        }
        Inst::Ctz { w, dst, src } => {
            let vw = view(*w);
            let s = l.op_to_reg(src, *w, SCRATCH)?;
            let t = gpr(SCRATCH2, vw);
            l.x(InstId::Rbit, &[go(t), go(s)]);
            l.x(InstId::Clz, &[go(gpr(*dst, vw)), go(t)]);
            none
        }
        Inst::Clz { w, dst, src } => {
            let s = l.op_to_reg(src, *w, SCRATCH)?;
            l.x(InstId::Clz, &[go(gpr(*dst, view(*w))), go(s)]);
            none
        }
        Inst::Popcnt { w, dst, src } => {
            // Population count through the NEON byte count (`cnt` + widening
            // `uaddlv`), since the base ISA has no GPR popcount.
            l.force_reg(src, *w, SCRATCH)?;
            let dv = qreg(FSCRATCH);
            l.x(
                InstId::Fmov_v,
                &[vo(fpr(FSCRATCH, FKind::F64)), go(x(SCRATCH))],
            );
            l.x(InstId::Cnt_v, &[vo(dv.b8()), vo(dv.b8())]);
            l.x(InstId::Uaddlv_v, &[vo(hreg(FSCRATCH)), vo(dv.b8())]);
            l.x(InstId::Umov_v, &[go(wv(*dst)), vo(dv.h_at(0))]);
            none
        }
        Inst::Cqo { quad } => {
            if *quad {
                l.x(InstId::Asr, &[go(x(T2)), go(x(T0)), uimm(63)]);
            } else {
                l.x(InstId::Sxtw, &[go(x(T2)), go(wv(T0))]);
            }
            none
        }
        Inst::AddShifted {
            dst,
            lhs,
            rhs,
            amount,
        } => {
            l.x(
                InstId::Add,
                &[
                    go(x(*dst)),
                    go(x(*lhs)),
                    go(x(*rhs)),
                    lsl_by(u32::from(*amount)),
                ],
            );
            none
        }
        Inst::Cmov {
            w,
            zero,
            dst,
            src,
            test,
        } => {
            let vw = view(*w);
            let d = gpr(*dst, vw);
            let s = l.op_to_reg(src, *w, SCRATCH)?;
            l.x(InstId::Cmp, &[go(gpr(*test, vw)), io(0)]);
            let cc = if *zero { Cc::Eq } else { Cc::Ne };
            l.x(InstId::Csel, &[go(d), go(s), go(d), cc.operand()]);
            none
        }
        Inst::VecExtract { w, dst, src, lane } => {
            let v = qreg(*src);
            let lane = u32::from(*lane);
            if lane >= 16 / w.bytes() {
                return Err(bad(mn, "vector lane is out of range"));
            }
            let (reg, elem) = match w {
                Width::B8 => (wv(*dst), v.b_at(lane)),
                Width::B16 => (wv(*dst), v.h_at(lane)),
                Width::B32 => (wv(*dst), v.s_at(lane)),
                Width::B64 => (x(*dst), v.d_at(lane)),
            };
            l.x(InstId::Umov_v, &[go(reg), vo(elem)]);
            none
        }
        Inst::Branch {
            cc,
            w,
            lhs,
            rhs,
            target,
            patch,
        } => l.emit_branch(*cc, *w, lhs, rhs, *target, *patch),
        Inst::TestBranch {
            w,
            value,
            mask,
            test,
            target,
            patch,
        } => l.emit_test_branch(*w, value, mask.as_ref(), *test, *target, *patch),
        Inst::OpBranch {
            op,
            w,
            flag,
            args,
            target,
            patch,
        } => l.op_branch(*op, *w, *flag, args.as_slice(), *target, *patch),
        Inst::FlagBranch {
            flag,
            target,
            patch,
        } => Ok(l.branch(Br::Cond(flag_cc(*flag)), *target, *patch)),
        Inst::Jump { target, patch } => l.emit_jump(target, *patch, false),
        Inst::Call { target, patch } => l.emit_jump(target, *patch, true),
        Inst::Ret => {
            l.x(InstId::Ret, &[go(x(Gpr(30)))]);
            none
        }
        Inst::Break => {
            l.x(InstId::Brk, &[io(0)]);
            none
        }
        Inst::Nop => {
            l.x(InstId::Nop, &[]);
            none
        }
        Inst::IntSet {
            cc,
            w,
            dst,
            lhs,
            rhs,
        } => {
            let cc = l.emit_cmp(*w, *cc, lhs, rhs)?;
            l.emit_set(*w, dst, int_cc(cc))?;
            none
        }
        Inst::TestSet {
            w,
            value,
            mask,
            test,
            dst,
        } => {
            l.test_flags(*w, value, mask.as_ref())?;
            l.emit_set(*w, dst, test_cc(*test))?;
            none
        }
        Inst::FArith { op, k, arith } => {
            l.emit_farith(*op, *k, arith)?;
            none
        }
        Inst::Fma {
            op,
            k,
            a,
            b,
            c,
            dst,
        } => {
            l.emit_fma(*op, *k, a, b, c, *dst)?;
            none
        }
        Inst::FSqrt { k, dst, src } => {
            let s = l.fp_src(*k, src)?;
            l.x(InstId::Fsqrt_v, &[vo(fpr(*dst, *k)), vo(s)]);
            none
        }
        Inst::FRound { k, mode, dst, src } => {
            let id = match mode {
                RoundMode::Nearest => InstId::Frintn_v,
                RoundMode::Down => InstId::Frintm_v,
                RoundMode::Up => InstId::Frintp_v,
                RoundMode::Trunc => InstId::Frintz_v,
            };
            let s = l.fp_src(*k, src)?;
            l.x(id, &[vo(fpr(*dst, *k)), vo(s)]);
            none
        }
        Inst::FAbs { k, dst, src } => {
            let s = l.fp_src(*k, src)?;
            l.x(InstId::Fabs_v, &[vo(fpr(*dst, *k)), vo(s)]);
            none
        }
        Inst::FNeg { k, dst, src } => {
            let s = l.fp_src(*k, src)?;
            l.x(InstId::Fneg_v, &[vo(fpr(*dst, *k)), vo(s)]);
            none
        }
        Inst::FBit { or, k, dst, src } => {
            let s = l.fp_src_id(*k, src)?;
            let d = qreg(*dst).b16();
            let id = if *or { InstId::Orr_v } else { InstId::And_v };
            l.x(id, &[vo(d), vo(d), vo(qreg(s).b16())]);
            none
        }
        Inst::CvtFI { k, w, dst, src } => {
            l.emit_cvtfi(*k, *w, *dst, src)?;
            none
        }
        Inst::CvtIF {
            signed,
            from,
            k,
            dst,
            src,
        } => {
            let s = l.op_to_reg(src, *from, SCRATCH)?;
            let id = if *signed {
                InstId::Scvtf_v
            } else {
                InstId::Ucvtf_v
            };
            l.x(id, &[vo(fpr(*dst, *k)), go(s)]);
            none
        }
        Inst::CvtFF { from, to, dst, src } => {
            let s = l.fp_src(*from, src)?;
            l.x(InstId::Fcvt_v, &[vo(fpr(*dst, *to)), vo(s)]);
            none
        }
        Inst::Bitcast { dir, dst, src } => {
            let ops = match (dir, dst, src) {
                (BitcastDir::Q2D, Op::Fpr(d), Op::Gpr(s)) => [vo(fpr(*d, FKind::F64)), go(x(*s))],
                (BitcastDir::D2Q, Op::Gpr(d), Op::Fpr(s)) => [go(x(*d)), vo(fpr(*s, FKind::F64))],
                (BitcastDir::I2F, Op::Fpr(d), Op::Gpr(s)) => [vo(fpr(*d, FKind::F32)), go(wv(*s))],
                (BitcastDir::F2I, Op::Gpr(d), Op::Fpr(s)) => [go(wv(*d)), vo(fpr(*s, FKind::F32))],
                _ => return Err(bad(mn, format!("unsupported bit-cast {dir:?}"))),
            };
            l.x(InstId::Fmov_v, &ops);
            none
        }
        Inst::BranchF {
            cc,
            k,
            lhs,
            rhs,
            target,
            patch,
        } => l.emit_branch_f(*cc, *k, lhs, rhs, *target, *patch),
        Inst::FSet {
            cc,
            k,
            dst,
            lhs,
            rhs,
        } => {
            l.emit_fset(*cc, *k, dst, lhs, rhs)?;
            none
        }
        Inst::Fence { full } => {
            // `dmb sy` / `dmb ish`.
            l.x(InstId::Dmb, &[io(if *full { 0xF } else { 0xB })]);
            none
        }
        Inst::Pause => {
            l.x(InstId::Yield, &[]);
            none
        }
        Inst::TlsLoad { w, dst, idx } => {
            l.emit_tls(*w, *dst, *idx, true)?;
            none
        }
        Inst::TlsStore { w, src, idx } => {
            l.emit_tls(*w, *src, *idx, false)?;
            none
        }
        Inst::TlsLea { dst, idx } => {
            l.emit_tls_lea(*dst, *idx)?;
            none
        }
        Inst::AtomicRmw { op, w, a, b } => {
            l.emit_rmw(*op, *w, a, b)?;
            none
        }
        Inst::AtomicCas {
            w,
            mem,
            src,
            branch,
        } => {
            l.emit_cas(*w, mem, *src, *branch)?;
            none
        }
        Inst::LoadLinked { w, mem, dst } => {
            let id = match w {
                Width::B8 => InstId::Ldaxrb,
                Width::B16 => InstId::Ldaxrh,
                Width::B32 | Width::B64 => InstId::Ldaxr,
            };
            let a = l.addr_base_only(mem)?;
            l.x(id, &[go(gpr(*dst, view(*w))), mo(a)]);
            none
        }
        Inst::StoreCond {
            w,
            status,
            src,
            mem,
        } => {
            l.emit_store_cond(*w, *status, *src, mem)?;
            none
        }
        Inst::PairLoad { w, dst1, dst2, mem } => {
            l.emit_pair(*w, dst1, dst2, mem, true)?;
            none
        }
        Inst::PairStore { w, src1, src2, mem } => {
            l.emit_pair(*w, src1, src2, mem, false)?;
            none
        }
    }
}

/// The integer ALU operations the shared IR prints directly.
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
    fn base(self) -> InstId {
        match self {
            AluKind::Add => InstId::Add,
            AluKind::Sub => InstId::Sub,
            AluKind::Mul => InstId::Mul,
            AluKind::And => InstId::And,
            AluKind::Or => InstId::Orr,
            AluKind::Xor => InstId::Eor,
        }
    }

    fn id(self, sf: bool) -> InstId {
        match (self, sf) {
            (AluKind::Add, true) => InstId::Adds,
            (AluKind::Sub, true) => InstId::Subs,
            _ => self.base(),
        }
    }

    fn commutative(self) -> bool {
        self != AluKind::Sub
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

fn three_op_direct(k: AluKind, w: Width, left: &Op, right: &Op) -> Option<(Operand, Operand)> {
    let vw = view(w);
    let wide = vw == Width::B64;
    let reg = |op: &Op| match op {
        Op::Gpr(g) => Some(gpr(*g, vw)),
        _ => None,
    };
    if let (Some(l), Some(r)) = (reg(left), reg(right)) {
        if matches!(k, AluKind::Add | AluKind::Sub) && matches!(right, Op::Gpr(g) if *g == SP) {
            return match k {
                AluKind::Add => Some((go(r), go(l))),
                _ => None,
            };
        }
        return Some((go(l), go(r)));
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
            Some((go(reg(other)?), io(imm)))
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
            Some((go(reg(other)?), logical_imm(imm, wide)))
        }
        AluKind::Mul => None,
    }
}

struct Lx<'a, 'b, 'c> {
    asm: &'a mut Assembler<'b>,
    mn: Mnemonic,
    res: &'a mut LabelResolver<'c>,
    abi: crate::Abi,
    err: Option<LowerError>,
}

impl Lx<'_, '_, '_> {
    fn x(&mut self, id: InstId, ops: &[Operand]) {
        for (pos, op) in ops.iter().enumerate() {
            if is_sp(op) && !sp_allowed(id, pos, ops) {
                self.reject("`sp` is not encodable in this operand position");
                return;
            }
        }
        e(self.asm, unscaled(id, ops), ops);
    }

    fn reject(&mut self, msg: &str) {
        if self.err.is_none() {
            self.err = Some(bad(self.mn, msg));
        }
    }

    fn bad(&self, msg: impl Into<String>) -> LowerError {
        bad(self.mn, msg)
    }

    fn label(&mut self, l: Lbl) -> Label {
        self.res.resolve(l, || self.asm.get_label())
    }

    /// Returns the backend label for a frontend handle that already exists in
    /// this assembler's label table.
    fn bound_label(&self, l: offlineasm_ir::Label) -> Result<Label, LowerError> {
        self.res
            .get(l)
            .ok_or_else(|| self.bad("label handle does not belong to this assembler"))
    }

    /// Materializes the address of `l` into `xd` as `adrp` + `add :lo12:`.
    ///
    /// Both instructions carry load-time relocations with a label target, so
    /// the result is correct even when this buffer is linked at a non-page
    /// offset (unlike the `A64AddAbsLo12` fixup used by [`Self::label`]).
    fn label_address_relocs(&mut self, xd: Gp, l: offlineasm_ir::Label) -> Result<(), LowerError> {
        let t = self.bound_label(l)?;
        let sym = RelocTarget::Label(t);
        let rd = xd.id();
        let buf = self.asm.buffer_mut();
        buf.add_reloc(Reloc::Aarch64AdrPrelPgHi21, sym.clone(), 0);
        buf.put4(0x9000_0000 | rd);
        buf.add_reloc(Reloc::Aarch64AddAbsLo12Nc, sym, 0);
        buf.put4(0x9100_0000 | rd << 5 | rd);
        Ok(())
    }

    /// Emits `adrp scratch, l; ldr rt, [scratch, #:lo12:l]` for the long-range
    /// label form. The load is patched at load time with
    /// [`Reloc::Aarch64Ld64AbsLo12Nc`].
    fn label_far_load(
        &mut self,
        id: InstId,
        rt: Gp,
        l: offlineasm_ir::Label,
    ) -> Result<(), LowerError> {
        let t = self.bound_label(l)?;
        let sym = RelocTarget::Label(t);
        let scratch = u32::from(SCRATCH.0);
        let buf = self.asm.buffer_mut();
        buf.add_reloc(Reloc::Aarch64AdrPrelPgHi21, sym.clone(), 0);
        buf.put4(0x9000_0000 | scratch);
        buf.add_reloc(Reloc::Aarch64Ld64AbsLo12Nc, sym, 0);
        self.x(id, &[go(rt), mo(ptr(x(SCRATCH), 0))]);
        Ok(())
    }

    fn branch(&mut self, br: Br, target: Lbl, patch: bool) -> Option<PatchHandle> {
        if let Br::Cbz(r) | Br::Cbnz(r) | Br::Tbnz(r, _) = br {
            if is_sp(&go(r)) {
                self.reject("`sp` is not encodable in this operand position");
                return None;
            }
        }
        let t = self.label(target);
        if !patch {
            br.emit(self.asm, t);
            return None;
        }
        let skip = self.asm.get_label();
        br.invert(self.asm, skip);
        let site = self.asm.patchable_b(t);
        self.asm.bind_label(skip);
        Some(PatchHandle::Jump(site))
    }

    fn mov_imm(&mut self, reg: Gp, v: i64) {
        emit_mov_imm(self.asm, reg, v);
    }

    /// Fold a whole address (`base + index * scale + disp`) into
    /// [`SCRATCH`], returning the scratch register.
    fn synth_addr(&mut self, m: &Mem) -> Result<Gp, LowerError> {
        let t = x(SCRATCH);
        if let Some(label) = m.disp.label() {
            if m.base.is_some() || m.index.is_some() {
                return Err(self.bad("a label-addressed operand has no base or index"));
            }
            self.label_address_relocs(t, label)?;
            return Ok(t);
        }
        let disp = match m.disp {
            Disp::Const(d) => d,
            Disp::Sym(_) => return Err(self.bad("symbolic displacements are offlineasm-only")),
            Disp::Label(_) | Disp::LabelFar(_) => unreachable!("handled above"),
        };
        let Some(base) = m.base else {
            self.mov_imm(t, i64::from(disp));
            self.add_index(t, m)?;
            return Ok(t);
        };
        let b = x(base);
        let magnitude = u64::from(disp.unsigned_abs());
        if magnitude == 0 {
            if b != t {
                self.x(InstId::Mov, &[go(t), go(b)]);
            }
        } else if magnitude <= 4095 {
            let id = if disp >= 0 { InstId::Add } else { InstId::Sub };
            self.x(id, &[go(t), go(b), uimm(magnitude)]);
        } else {
            self.mov_imm(t, i64::from(disp));
            self.x(InstId::Add, &[go(t), go(b), go(t)]);
        }
        self.add_index(t, m)?;
        Ok(t)
    }

    /// Add `index * scale` (if any) to `t`.
    fn add_index(&mut self, t: Gp, m: &Mem) -> Result<(), LowerError> {
        if let Some((index, scale)) = m.index {
            let shift = match scale {
                1 => 0,
                2 => 1,
                4 => 2,
                8 => 3,
                other => return Err(self.bad(format!("bad address scale {other}"))),
            };
            let i = x(index);
            if shift == 0 {
                self.x(InstId::Add, &[go(t), go(t), go(i)]);
            } else {
                self.x(InstId::Add, &[go(t), go(t), go(i), lsl_by(shift)]);
            }
        }
        Ok(())
    }

    fn addr_operand(&mut self, m: &Mem, size: u32) -> Result<AMem, LowerError> {
        let Some(base) = m.base else {
            let t = self.synth_addr(m)?;
            return Ok(ptr(t, 0));
        };
        let b = x(base);
        match (m.index, m.disp) {
            (None, Disp::Const(0)) => Ok(ptr(b, 0)),
            (None, Disp::Const(disp)) => {
                let size = size as i32;
                let scaled = disp >= 0 && size != 0 && disp % size == 0 && disp < 4096 * size;
                if scaled || (-256..=255).contains(&disp) {
                    Ok(ptr(b, disp))
                } else {
                    let t = self.synth_addr(m)?;
                    Ok(ptr(t, 0))
                }
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
                    Some(0) => Ok(ptr_reg(b, x(index))),
                    Some(s) => Ok(ptr_shift(b, x(index), lsl(s))),
                    None => {
                        let t = self.synth_addr(m)?;
                        Ok(ptr(t, 0))
                    }
                }
            }
            (_, Disp::Sym(_)) => Err(self.bad("symbolic displacements are offlineasm-only")),
            (_, Disp::Label(_) | Disp::LabelFar(_)) => {
                Err(self.bad("a label-addressed operand has no base or index"))
            }
            (Some(_), _) => {
                let t = self.synth_addr(m)?;
                Ok(ptr(t, 0))
            }
        }
    }

    fn addr_base_only(&mut self, m: &Mem) -> Result<AMem, LowerError> {
        if m.index.is_none() && matches!(m.disp, Disp::Const(0)) {
            if let Some(base) = m.base {
                return Ok(ptr(x(base), 0));
            }
        }
        let t = self.synth_addr(m)?;
        Ok(ptr(t, 0))
    }

    fn pair_addr_operand(&mut self, m: &Mem, scale: i64) -> Result<AMem, LowerError> {
        if let (Some(base), None, Disp::Const(disp)) = (m.base, m.index, m.disp) {
            let disp = i64::from(disp);
            if disp % scale == 0 && (-64 * scale..64 * scale).contains(&disp) {
                return Ok(ptr(x(base), disp as i32));
            }
        }
        let t = self.synth_addr(m)?;
        Ok(ptr(t, 0))
    }

    fn op_to_reg(&mut self, op: &Op, w: Width, scratch: Gpr) -> Result<Gp, LowerError> {
        let vw = view(w);
        match op {
            Op::Gpr(g) => Ok(gpr(*g, vw)),
            Op::Imm(v) => {
                let r = gpr(scratch, vw);
                self.mov_imm(r, *v);
                Ok(r)
            }
            Op::Mem(m) => {
                let r = gpr(scratch, vw);
                let a = self.addr_operand(m, w.bytes())?;
                self.x(load_id(w), &[go(r), mo(a)]);
                Ok(r)
            }
            Op::Sym(_) => Err(self.bad("symbolic immediates are offlineasm-only")),
            _ => Err(self.bad("operand cannot be loaded into a register")),
        }
    }

    fn force_reg(&mut self, op: &Op, w: Width, scratch: Gpr) -> Result<Gp, LowerError> {
        let r = gpr(scratch, view(w));
        self.load_into(op, r, w)?;
        Ok(r)
    }

    fn load_into(&mut self, op: &Op, dst: Gp, w: Width) -> Result<(), LowerError> {
        let vw = view(w);
        match op {
            Op::Gpr(g) => {
                let s = gpr(*g, vw);
                if s != dst {
                    self.x(InstId::Mov, &[go(dst), go(s)]);
                }
                Ok(())
            }
            Op::Imm(v) => {
                self.mov_imm(dst, *v);
                Ok(())
            }
            Op::Mem(m) => {
                if m.base.is_none() && m.index.is_none() {
                    match m.disp {
                        Disp::Label(label) => {
                            if matches!(w, Width::B32 | Width::B64) {
                                let t = self.bound_label(label)?;
                                self.x(load_id(w), &[go(dst), mo(label_ptr(t, 0))]);
                                return Ok(());
                            }
                        }
                        Disp::LabelFar(label) => {
                            if matches!(w, Width::B32 | Width::B64) {
                                let id = load_id(w);
                                self.label_far_load(id, dst, label)?;
                                return Ok(());
                            }
                        }
                        _ => {}
                    }
                }
                let a = self.addr_operand(m, w.bytes())?;
                self.x(load_id(w), &[go(dst), mo(a)]);
                Ok(())
            }
            Op::Sym(_) => Err(self.bad("symbolic immediates are offlineasm-only")),
            _ => Err(self.bad("operand cannot be loaded into a register")),
        }
    }

    fn fp_src_id(&mut self, k: FKind, op: &Op) -> Result<Fpr, LowerError> {
        match op {
            Op::Fpr(f) => Ok(*f),
            Op::Mem(m) => {
                let a = self.addr_operand(m, fk_bytes(k))?;
                self.x(InstId::Ldr_v, &[vo(fpr(FSCRATCH, k)), mo(a)]);
                Ok(FSCRATCH)
            }
            Op::Imm(v) => {
                let t = gpr(
                    SCRATCH,
                    if k == FKind::F32 {
                        Width::B32
                    } else {
                        Width::B64
                    },
                );
                self.mov_imm(t, *v);
                self.x(InstId::Fmov_v, &[vo(fpr(FSCRATCH, k)), go(t)]);
                Ok(FSCRATCH)
            }
            _ => Err(self.bad("operand cannot be loaded into a float register")),
        }
    }

    fn fp_src(&mut self, k: FKind, op: &Op) -> Result<Vec, LowerError> {
        self.fp_src_id(k, op).map(|f| fpr(f, k))
    }

    fn alu_reg_sp_rhs(&mut self, k: AluKind, w: Width, dst: Gp, tmp: Gpr, sf: bool) {
        let vw = view(w);
        let spr = gpr(SP, vw);
        match k {
            AluKind::Add => self.x(k.id(sf), &[go(dst), go(spr), go(dst)]),
            AluKind::Sub => {
                let t = gpr(tmp, vw);
                self.x(InstId::Mov, &[go(t), go(spr)]);
                self.x(k.id(sf), &[go(dst), go(dst), go(t)]);
            }
            _ => unreachable!("alu_reg_sp_rhs only handles Add/Sub"),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn alu_reg(
        &mut self,
        k: AluKind,
        w: Width,
        dst: Gp,
        rhs: &Op,
        tmp: Gpr,
        sf: bool,
    ) -> Result<(), LowerError> {
        let vw = view(w);
        let id = k.id(sf);
        match rhs {
            Op::Gpr(g) if *g == SP && matches!(k, AluKind::Add | AluKind::Sub) => {
                self.alu_reg_sp_rhs(k, w, dst, tmp, sf);
                Ok(())
            }
            Op::Gpr(g) => {
                self.x(id, &[go(dst), go(dst), go(gpr(*g, vw))]);
                Ok(())
            }
            Op::Imm(v) => {
                match k {
                    AluKind::Add | AluKind::Sub => {
                        let use_sub = if k == AluKind::Add { *v < 0 } else { *v >= 0 };
                        let magnitude = v.unsigned_abs();
                        if magnitude <= 4095 {
                            let id = match (use_sub, sf) {
                                (true, false) => InstId::Sub,
                                (true, true) => InstId::Subs,
                                (false, false) => InstId::Add,
                                (false, true) => InstId::Adds,
                            };
                            self.x(id, &[go(dst), go(dst), uimm(magnitude)]);
                            return Ok(());
                        }
                    }
                    AluKind::And | AluKind::Or | AluKind::Xor => {
                        let wide = vw == Width::B64;
                        if fits_logical_imm(*v, wide) {
                            self.x(id, &[go(dst), go(dst), logical_imm(*v, wide)]);
                            return Ok(());
                        }
                    }
                    AluKind::Mul => {}
                }
                let s = self.op_to_reg(rhs, w, tmp)?;
                self.x(id, &[go(dst), go(dst), go(s)]);
                Ok(())
            }
            Op::Mem(_) => {
                let s = self.op_to_reg(rhs, w, tmp)?;
                self.x(id, &[go(dst), go(dst), go(s)]);
                Ok(())
            }
            Op::Sym(_) => Err(self.bad("symbolic immediates are offlineasm-only")),
            _ => Err(self.bad("ALU operand is not usable")),
        }
    }

    fn alu(&mut self, k: AluKind, w: Width, shape: &Alu3, sf: bool) -> Result<(), LowerError> {
        match &shape.dst {
            Op::Gpr(dst) => {
                let d = gpr(*dst, view(w));
                if crate::ir::op_eq(&shape.lhs, &shape.dst) {
                    return self.alu_reg(k, w, d, &shape.rhs, SCRATCH2, sf);
                }
                if crate::ir::op_eq(&shape.rhs, &shape.dst) {
                    if k.commutative() {
                        return self.alu_reg(k, w, d, &shape.lhs, SCRATCH2, sf);
                    }

                    let t = gpr(SCRATCH2, view(w));
                    self.x(InstId::Mov, &[go(t), go(d)]);
                    self.load_into(&shape.lhs, d, w)?;
                    return self.alu_reg(k, w, d, &Op::Gpr(SCRATCH2), SCRATCH, sf);
                }
                if let Some((l, r)) = three_op_direct(k, w, &shape.lhs, &shape.rhs) {
                    self.x(k.id(sf), &[go(d), l, r]);
                    return Ok(());
                }
                self.load_into(&shape.lhs, d, w)?;
                self.alu_reg(k, w, d, &shape.rhs, SCRATCH2, sf)
            }
            Op::Mem(m) => {
                let v = gpr(SCRATCH2, view(w));
                self.load_into(&shape.lhs, v, w)?;
                self.alu_reg(k, w, v, &shape.rhs, SCRATCH, sf)?;
                let a = self.addr_operand(m, w.bytes())?;
                self.x(store_id(w), &[go(v), mo(a)]);
                Ok(())
            }
            _ => Err(self.bad("ALU destination is not usable")),
        }
    }

    fn cmp_side(
        &mut self,
        w: Width,
        sign_extend: bool,
        op: &Op,
        scratch: Gpr,
    ) -> Result<Gp, LowerError> {
        let wide = sign_extend || w == Width::B64;
        let vw = if wide { Width::B64 } else { Width::B32 };
        match op {
            Op::Gpr(g) => {
                if sign_extend {
                    let t = x(scratch);
                    let id = if w == Width::B8 {
                        InstId::Sxtb
                    } else {
                        InstId::Sxth
                    };
                    self.x(id, &[go(t), go(wv(*g))]);
                    Ok(t)
                } else {
                    Ok(gpr(*g, vw))
                }
            }
            Op::Mem(m) => {
                let t = gpr(scratch, vw);
                let a = self.addr_operand(m, w.bytes())?;
                let id = match (w, sign_extend) {
                    (Width::B8, true) => InstId::Ldrsb,
                    (Width::B16, true) => InstId::Ldrsh,
                    _ => load_id(w),
                };
                self.x(id, &[go(t), mo(a)]);
                Ok(t)
            }
            Op::Imm(v) => {
                let t = gpr(scratch, vw);
                self.mov_imm(t, *v);
                Ok(t)
            }
            Op::Sym(_) => Err(self.bad("symbolic immediates are offlineasm-only")),
            _ => Err(self.bad("comparison operand is not usable")),
        }
    }

    fn emit_cmp(&mut self, w: Width, cc: IntCc, lhs: &Op, rhs: &Op) -> Result<IntCc, LowerError> {
        let (cc, lhs, rhs) = match (lhs, rhs) {
            (Op::Imm(_), Op::Gpr(_) | Op::Mem(_)) => (flip_cc(cc), rhs, lhs),
            _ => (cc, lhs, rhs),
        };
        let signed_narrow = matches!(w, Width::B8 | Width::B16)
            && matches!(cc, IntCc::Gt | IntCc::Ge | IntCc::Lt | IntCc::Le);
        let left = self.cmp_side(w, signed_narrow, lhs, SCRATCH)?;
        match rhs {
            Op::Imm(v) if !signed_narrow && (0..=4095).contains(v) => {
                self.x(InstId::Cmp, &[go(left), io(*v)]);
            }
            Op::Imm(v) if !signed_narrow && *v < 0 && v.unsigned_abs() <= 4095 => {
                self.x(InstId::Cmn, &[go(left), uimm(v.unsigned_abs())]);
            }
            _ => {
                let right = self.cmp_side(w, signed_narrow, rhs, SCRATCH2)?;
                self.x(InstId::Cmp, &[go(left), go(right)]);
            }
        }
        Ok(cc)
    }

    fn test_flags(&mut self, w: Width, value: &Op, mask: Option<&Op>) -> Result<(), LowerError> {
        let v = self.op_to_reg(value, w, SCRATCH)?;
        let Some(m) = mask else {
            match w {
                Width::B8 | Width::B16 => {
                    let id = if w == Width::B8 {
                        InstId::Sxtb
                    } else {
                        InstId::Sxth
                    };
                    let t = wv(SCRATCH2);
                    self.x(id, &[go(t), go(v)]);
                    self.x(InstId::Tst, &[go(t), go(t)]);
                }
                _ => self.x(InstId::Tst, &[go(v), go(v)]),
            }
            return Ok(());
        };
        let mv = self.op_to_reg(m, w, SCRATCH2)?;
        match w {
            // `tst` has no byte/halfword form, so mask into the second
            // scratch, then sign-extend and test that. `value` is never
            // written: callers rely on it surviving a masked test.
            Width::B8 | Width::B16 => {
                let t = wv(SCRATCH2);
                self.x(InstId::And, &[go(t), go(v), go(mv)]);
                let id = if w == Width::B8 {
                    InstId::Sxtb
                } else {
                    InstId::Sxth
                };
                self.x(id, &[go(t), go(t)]);
                self.x(InstId::Tst, &[go(t), go(t)]);
            }
            // `tst Xn, Xm` is `ands XZR, Xn, Xm`: one instruction, no
            // clobber, and it accepts a register mask.
            _ => self.x(InstId::Tst, &[go(v), go(mv)]),
        }
        Ok(())
    }

    fn dst_reg(&mut self, w: Width, dst: &Op) -> Result<Gp, LowerError> {
        match dst {
            Op::Gpr(g) => Ok(gpr(*g, view(w))),
            Op::Mem(m) => {
                let r = gpr(SCRATCH, view(w));
                let a = self.addr_operand(m, w.bytes())?;
                self.x(load_id(w), &[go(r), mo(a)]);
                Ok(r)
            }
            _ => Err(self.bad("op-branch destination is not usable")),
        }
    }

    fn flags_from_dst(&mut self, w: Width, dst: &Op, flag: PredFlag) -> Result<(), LowerError> {
        let r = self.dst_reg(w, dst)?;
        match w {
            Width::B8 | Width::B16 => {
                let id = if w == Width::B8 {
                    InstId::Sxtb
                } else {
                    InstId::Sxth
                };
                let mask = if w == Width::B8 { 0xff } else { 0xffff };
                match flag {
                    PredFlag::O | PredFlag::S => {
                        let t = wv(SCRATCH2);
                        self.x(id, &[go(t), go(r)]);
                        if flag == PredFlag::O {
                            self.x(InstId::Cmp, &[go(r), go(t)]);
                        } else {
                            self.x(InstId::Tst, &[go(t), go(t)]);
                        }
                    }
                    PredFlag::Z | PredFlag::Nz => {
                        self.x(InstId::Ands, &[go(regs::wzr), go(r), io(mask)]);
                    }
                }
            }
            _ => self.x(InstId::Tst, &[go(r), go(r)]),
        }
        Ok(())
    }

    fn factor_reg(&mut self, op: &Op, w: Width, scratch: Gpr) -> Result<Gp, LowerError> {
        match op {
            Op::Gpr(g) => Ok(gpr(*g, view(w))),
            _ => self.force_reg(op, w, scratch),
        }
    }

    fn mul_overflow(&mut self, w: Width, lhs: &Op, rhs: &Op) -> Result<(), LowerError> {
        if !matches!(w, Width::B32 | Width::B64) {
            return Err(self.bad("mul-overflow branch is defined for 32/64-bit widths"));
        }

        let r = self.factor_reg(rhs, w, SCRATCH2)?;
        let l = self.factor_reg(lhs, w, SCRATCH)?;
        let (lo_x, hi_x) = (x(SCRATCH), x(SCRATCH2));
        if w == Width::B64 {
            if l == lo_x && r == hi_x {
                let spr = x(SP);
                self.x(InstId::Str, &[go(lo_x), mo(ptr_pre(spr, -16))]);
                self.x(InstId::Smulh, &[go(lo_x), go(lo_x), go(hi_x)]);
                self.x(InstId::Str, &[go(lo_x), mo(ptr(spr, 8))]);
                self.x(InstId::Ldr, &[go(lo_x), mo(ptr(spr, 0))]);
                self.x(InstId::Mul, &[go(lo_x), go(lo_x), go(hi_x)]);
                self.x(InstId::Asr, &[go(lo_x), go(lo_x), uimm(63)]);
                self.x(InstId::Ldr, &[go(hi_x), mo(ptr(spr, 8))]);
                self.x(InstId::Add, &[go(spr), go(spr), uimm(16)]);
                self.x(InstId::Cmp, &[go(hi_x), go(lo_x)]);
                return Ok(());
            }
            let (hi, lo) = if r == hi_x {
                (lo_x, hi_x)
            } else {
                (hi_x, lo_x)
            };
            self.x(InstId::Smulh, &[go(hi), go(l), go(r)]);
            self.x(InstId::Mul, &[go(lo), go(l), go(r)]);
            self.x(InstId::Asr, &[go(lo), go(lo), uimm(63)]);
            self.x(InstId::Cmp, &[go(hi), go(lo)]);
        } else {
            self.x(InstId::Smull, &[go(lo_x), go(l), go(r)]);
            self.x(InstId::Sxtw, &[go(hi_x), go(wv(SCRATCH))]);
            self.x(InstId::Cmp, &[go(lo_x), go(hi_x)]);
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn op_branch(
        &mut self,
        op: FlagAlu,
        w: Width,
        flag: PredFlag,
        args: &[Op],
        target: Lbl,
        patch: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        let shape = alu3_from_args(args)
            .ok_or_else(|| self.bad("op-branch takes 2 or 3 leading operands"))?;
        let k = match op {
            FlagAlu::Add => AluKind::Add,
            FlagAlu::Sub => AluKind::Sub,
            FlagAlu::Mul => AluKind::Mul,
            FlagAlu::Or => AluKind::Or,
        };
        let narrow = matches!(w, Width::B8 | Width::B16);

        if k == AluKind::Or && flag == PredFlag::O {
            if patch {
                return Err(LowerError::NotPatchable(self.mn.to_string()));
            }
            self.alu(k, w, &shape, false)?;
            return Ok(None);
        }
        if k == AluKind::Mul && flag == PredFlag::O {
            self.mul_overflow(w, &shape.lhs, &shape.rhs)?;
            self.alu(k, w, &shape, false)?;
            return Ok(self.branch(Br::Cond(Cc::Ne), target, patch));
        }

        if !narrow && matches!(k, AluKind::Add | AluKind::Sub) {
            self.alu(k, w, &shape, true)?;
            return Ok(self.branch(Br::Cond(flag_cc(flag)), target, patch));
        }
        self.alu(k, w, &shape, false)?;
        self.flags_from_dst(w, &shape.dst, flag)?;
        let cc = if flag == PredFlag::O {
            Cc::Ne
        } else {
            flag_cc(flag)
        };
        Ok(self.branch(Br::Cond(cc), target, patch))
    }

    fn stack_slot(&mut self, disp: i32) -> AMem {
        if disp >= 0 && disp % 8 == 0 && disp < 4096 * 8 {
            return ptr(x(SP), disp);
        }
        let t = x(SCRATCH);
        let magnitude = u64::from(disp.unsigned_abs());
        if magnitude <= 4095 {
            let id = if disp >= 0 { InstId::Add } else { InstId::Sub };
            self.x(id, &[go(t), go(x(SP)), uimm(magnitude)]);
        } else {
            self.mov_imm(t, i64::from(disp));
            self.x(InstId::Add, &[go(t), go(x(SP)), go(t)]);
        }
        ptr(t, 0)
    }

    /// PC-relative address of `label` into `xd` (`adrp` + `add :lo12:`).
    fn label_address(&mut self, xd: Gp, l: Lbl) {
        let t = self.label(l);
        self.asm.load_constant(xd, t);
    }

    /// Address of extern `e` into `xd`: `adrp` + `add :lo12:` for a near
    /// extern, `adrp` + `ldr` of its GOT entry for a far one.
    fn extern_address(&mut self, xd: Gpr, e: Extern) {
        let rd = u32::from(xd.0);
        let sym = RelocTarget::Sym(Sym::from_id(e.id.0));
        let (page, low, low_word) = match e.reach {
            // `add xd, xd, #0`
            Reach::Near => (
                Reloc::Aarch64AdrPrelPgHi21,
                Reloc::Aarch64AddAbsLo12Nc,
                0x9100_0000,
            ),
            // `ldr xd, [xd, #0]`
            Reach::Far => (
                Reloc::Aarch64AdrGotPage21,
                Reloc::Aarch64Ld64GotLo12Nc,
                0xf940_0000,
            ),
        };
        let buf = self.asm.buffer_mut();
        buf.add_reloc(page, sym.clone(), 0);
        buf.put4(0x9000_0000 | rd); // `adrp xd, #0`
        buf.add_reloc(low, sym, 0);
        buf.put4(low_word | rd << 5 | rd);
    }

    fn emit_mov(&mut self, w: Width, dst: &Op, src: &Op) -> Result<(), LowerError> {
        match (dst, src) {
            (Op::Gpr(g), Op::Label(l)) => {
                self.label_address(x(*g), *l);
                if w != Width::B64 {
                    self.x(InstId::Mov, &[go(wv(*g)), go(wv(*g))]);
                }
                Ok(())
            }
            (Op::Gpr(g), src) => self.load_into(src, gpr(*g, view(w)), w),
            (Op::Mem(m), src) => {
                if matches!(src, Op::Label(_)) {
                    return Err(self.bad("cannot store a label address"));
                }
                let value = self.op_to_reg(src, w, SCRATCH2)?;
                let a = self.addr_operand(m, w.bytes())?;
                self.x(store_id(w), &[go(value), mo(a)]);
                Ok(())
            }
            (Op::Fpr(_), _) => {
                Err(self.bad("move needs a GPR or memory destination (use moved/movev for floats)"))
            }
            _ => Err(self.bad("move destination is not usable")),
        }
    }

    /// `leai`/`leap`/`pcrtoaddr`/`globaladdr`/`la`.
    fn emit_lea(&mut self, w: Width, dst: Gpr, src: &LeaSrc) -> Result<(), LowerError> {
        let xd = x(dst);
        match src {
            LeaSrc::Label(l) => self.label_address(xd, *l),
            LeaSrc::Extern(e) => self.extern_address(dst, *e),
            LeaSrc::Mem(m) => {
                let from = if m.index.is_none() && matches!(m.disp, Disp::Const(0)) {
                    x(m.base_reg())
                } else {
                    self.synth_addr(m)?
                };
                if from != xd {
                    self.x(InstId::Mov, &[go(xd), go(from)]);
                }
            }
        }
        if w != Width::B64 {
            // Truncating address computation (`leai`).
            self.x(InstId::Mov, &[go(wv(dst)), go(wv(dst))]);
        }
        Ok(())
    }

    fn emit_not_neg(&mut self, w: Width, dst: &Op, neg: bool) -> Result<(), LowerError> {
        let vw = view(w);
        let id = if neg { InstId::Neg } else { InstId::Mvn };
        match dst {
            Op::Gpr(d) => {
                let d = gpr(*d, vw);
                self.x(id, &[go(d), go(d)]);
                Ok(())
            }
            Op::Mem(m) => {
                let t = gpr(SCRATCH2, vw);
                self.load_into(&Op::Mem(*m), t, w)?;
                self.x(id, &[go(t), go(t)]);
                let a = self.addr_operand(m, w.bytes())?;
                self.x(store_id(w), &[go(t), mo(a)]);
                Ok(())
            }
            _ => Err(self.bad("not/neg destination is not usable")),
        }
    }

    fn emit_shift(&mut self, w: Width, op: ShiftOp, dst: Gpr, cnt: &ShiftCnt) {
        let vw = view(w);
        let width: u64 = if vw == Width::B64 { 64 } else { 32 };
        let d = gpr(dst, vw);
        match cnt {
            ShiftCnt::Imm(v) => {
                let count = (*v as u64) & (width - 1);
                let (id, amount) = match op {
                    ShiftOp::Shl => (InstId::Lsl, count),
                    ShiftOp::ShrSar => (InstId::Asr, count),
                    ShiftOp::Shr => (InstId::Lsr, count),
                    ShiftOp::Rotr => (InstId::Ror, count),
                    ShiftOp::Rotl => (InstId::Ror, (width - count) % width),
                };
                self.x(id, &[go(d), go(d), uimm(amount)]);
            }
            ShiftCnt::Reg(g) => {
                let s = gpr(*g, vw);
                let id = match op {
                    ShiftOp::Shl => InstId::Lsl,
                    ShiftOp::ShrSar => InstId::Asr,
                    ShiftOp::Shr => InstId::Lsr,
                    ShiftOp::Rotr => InstId::Ror,
                    ShiftOp::Rotl => {
                        // Rotate-left by `n` is rotate-right by `-n`.
                        let t = gpr(SCRATCH2, vw);
                        self.x(InstId::Neg, &[go(t), go(s)]);
                        self.x(InstId::Ror, &[go(d), go(d), go(t)]);
                        return;
                    }
                };
                self.x(id, &[go(d), go(d), go(s)]);
            }
        }
    }

    fn emit_adc(&mut self, dst: &Op, src: &Op, borrow: bool) -> Result<(), LowerError> {
        let id = if borrow { InstId::Sbcs } else { InstId::Adcs };
        match dst {
            Op::Gpr(d) => {
                let d = x(*d);
                let s = self.op_to_reg(src, Width::B64, SCRATCH)?;
                self.x(id, &[go(d), go(d), go(s)]);
                Ok(())
            }
            Op::Mem(m) => {
                let t = x(SCRATCH2);
                self.load_into(&Op::Mem(*m), t, Width::B64)?;
                let s = self.op_to_reg(src, Width::B64, SCRATCH)?;
                self.x(id, &[go(t), go(t), go(s)]);
                let a = self.addr_operand(m, 8)?;
                self.x(InstId::Str, &[go(t), mo(a)]);
                Ok(())
            }
            _ => Err(self.bad("adc/sbb destination is not usable")),
        }
    }

    fn emit_divmod1(&mut self, signed: bool, w: Width, divisor: &Op) -> Result<(), LowerError> {
        let vw = view(w);
        let lo = gpr(T0, vw);
        let hi = gpr(T2, vw);
        let dvs = self.force_reg(divisor, w, SCRATCH2)?;
        let trap = self.asm.get_label();
        let done = self.asm.get_label();
        self.asm.cbz(dvs, trap);
        if signed {
            let ok = self.asm.get_label();
            let t = gpr(SCRATCH, vw);
            let bound = if vw == Width::B64 {
                i64::MIN
            } else {
                i64::from(i32::MIN)
            };
            self.mov_imm(t, bound);
            self.x(InstId::Cmp, &[go(lo), go(t)]);
            b_cond(self.asm, Cc::Ne, ok);
            self.x(InstId::Cmn, &[go(dvs), io(1)]);
            b_cond(self.asm, Cc::Ne, ok);
            self.asm.b(trap);
            self.asm.bind_label(ok);
        }

        let save = gpr(SCRATCH, vw);
        self.x(InstId::Mov, &[go(save), go(lo)]);
        let id = if signed { InstId::Sdiv } else { InstId::Udiv };
        self.x(id, &[go(lo), go(lo), go(dvs)]);
        self.x(InstId::Msub, &[go(hi), go(lo), go(dvs), go(save)]);
        self.asm.b(done);
        self.asm.bind_label(trap);
        self.x(InstId::Brk, &[io(0)]);
        self.asm.bind_label(done);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_div3(
        &mut self,
        signed: bool,
        w: Width,
        dst: Gpr,
        dvd: &Op,
        dvs: &Op,
        is_rem: bool,
    ) -> Result<(), LowerError> {
        let d = gpr(dst, view(w));
        let id = if signed { InstId::Sdiv } else { InstId::Udiv };
        if !is_rem {
            self.load_into(dvd, d, w)?;
            let r = self.op_to_reg(dvs, w, SCRATCH)?;
            self.x(id, &[go(d), go(d), go(r)]);
            return Ok(());
        }
        // The remainder needs the dividend, the quotient, and the divisor
        // live at once, so the dividend waits in the second scratch register.
        let saved = self.force_reg(dvd, w, SCRATCH2)?;
        let r = self.op_to_reg(dvs, w, SCRATCH)?;
        self.x(id, &[go(d), go(saved), go(r)]);
        self.x(InstId::Msub, &[go(d), go(d), go(r), go(saved)]);
        Ok(())
    }

    fn emit_extend(
        &mut self,
        from: Width,
        to: Width,
        sx: Sx,
        dst: Gpr,
        src: &Op,
    ) -> Result<(), LowerError> {
        let s = self.op_to_reg(src, from, SCRATCH)?;
        let d = gpr(dst, view(to));
        match (from, to, sx) {
            (Width::B64, _, _) | (Width::B32, Width::B8 | Width::B16 | Width::B32, _) => {
                if s != d {
                    self.x(InstId::Mov, &[go(d), go(s)]);
                }
            }
            (Width::B32, Width::B64, Sx::Zero) => {
                self.x(InstId::Ubfx, &[go(d), go(x(id_of(s))), io(0), io(32)]);
            }
            (Width::B32, Width::B64, Sx::Sign) => self.x(InstId::Sxtw, &[go(d), go(s)]),
            (Width::B8 | Width::B16, _, Sx::Sign) => {
                let id = if from == Width::B8 {
                    InstId::Sxtb
                } else {
                    InstId::Sxth
                };
                self.x(id, &[go(d), go(s)]);
            }
            (Width::B8 | Width::B16, _, Sx::Zero) => {
                let id = if from == Width::B8 {
                    InstId::Uxtb
                } else {
                    InstId::Uxth
                };
                self.x(id, &[go(wv(dst)), go(s)]);
            }
        }
        Ok(())
    }

    fn emit_farith(&mut self, op: FAlu, k: FKind, arith: &FArith3) -> Result<(), LowerError> {
        let id = match op {
            FAlu::Add => InstId::Fadd_v,
            FAlu::Sub => InstId::Fsub_v,
            FAlu::Mul => InstId::Fmul_v,
            FAlu::Div => InstId::Fdiv_v,
            FAlu::Min => InstId::Fmin_v,
            FAlu::Max => InstId::Fmax_v,
        };
        let d = fpr(arith.dst, k);
        match &arith.rhs {
            Some(rhs) => {
                let r = match rhs {
                    Op::Fpr(f) if *f != arith.dst => fpr(*f, k),
                    Op::Fpr(_) => {
                        self.x(InstId::Fmov_v, &[vo(fpr(FSCRATCH, k)), vo(d)]);
                        fpr(FSCRATCH, k)
                    }
                    _ => self.fp_src(k, rhs)?,
                };
                let l = match &arith.lhs {
                    Op::Fpr(f) => fpr(*f, k),
                    Op::Mem(m) => {
                        let a = self.addr_operand(m, fk_bytes(k))?;
                        self.x(InstId::Ldr_v, &[vo(d), mo(a)]);
                        d
                    }
                    Op::Imm(v) => {
                        let t = gpr(
                            SCRATCH,
                            if k == FKind::F32 {
                                Width::B32
                            } else {
                                Width::B64
                            },
                        );
                        self.mov_imm(t, *v);
                        self.x(InstId::Fmov_v, &[vo(d), go(t)]);
                        d
                    }
                    _ => return Err(self.bad("fp arithmetic operand is not usable")),
                };
                self.x(id, &[vo(d), vo(l), vo(r)]);
            }
            None => {
                let l = self.fp_src(k, &arith.lhs)?;
                self.x(id, &[vo(d), vo(d), vo(l)]);
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_fma(
        &mut self,
        op: FmaOp,
        k: FKind,
        a: &Op,
        b: &Op,
        c: &Op,
        dst: Fpr,
    ) -> Result<(), LowerError> {
        let id = match op {
            FmaOp::Add => InstId::Fmadd_v,
            FmaOp::Sub => InstId::Fnmsub_v,
            FmaOp::NegAdd => InstId::Fmsub_v,
            FmaOp::NegSub => InstId::Fnmadd_v,
        };
        let spilled = [a, b, c]
            .iter()
            .filter(|op| !matches!(op, Op::Fpr(_)))
            .count();
        if spilled > 1 {
            return Err(self.bad("fma needs at most one spilled operand"));
        }
        let ra = self.fp_src(k, a)?;
        let rb = self.fp_src(k, b)?;
        let rc = self.fp_src(k, c)?;
        self.x(id, &[vo(fpr(dst, k)), vo(ra), vo(rb), vo(rc)]);
        Ok(())
    }

    fn emit_cvtfi(&mut self, k: FKind, w: Width, dst: Gpr, src: &Op) -> Result<(), LowerError> {
        let s = self.fp_src(k, src)?;
        let d = gpr(dst, view(w));
        self.x(InstId::Fcvtzs_v, &[go(d), vo(s)]);
        let wide = view(w) == Width::B64;
        let max = if wide { i64::MAX } else { i64::from(i32::MAX) };
        let sentinel = if wide { i64::MIN } else { i64::from(i32::MIN) };
        let t = gpr(SCRATCH, view(w));
        self.mov_imm(t, max);
        self.x(InstId::Cmp, &[go(d), go(t)]);
        let pos_ok = self.asm.get_label();
        b_cond(self.asm, Cc::Ne, pos_ok);
        self.mov_imm(d, sentinel);
        self.asm.bind_label(pos_ok);
        self.x(InstId::Fcmp_v, &[vo(s), vo(s)]);
        let nan_ok = self.asm.get_label();
        b_cond(self.asm, Cc::Vc, nan_ok);
        self.mov_imm(d, sentinel);
        self.asm.bind_label(nan_ok);
        Ok(())
    }

    fn emit_set(&mut self, w: Width, dst: &Op, cc: Cc) -> Result<(), LowerError> {
        match dst {
            Op::Gpr(d) => {
                self.x(InstId::Cset, &[go(wv(*d)), cc.operand()]);
                Ok(())
            }
            Op::Mem(m) => {
                let t = gpr(SCRATCH2, view(w));
                self.x(InstId::Cset, &[go(t), cc.operand()]);
                let a = self.addr_operand(m, w.bytes())?;
                self.x(store_id(w), &[go(t), mo(a)]);
                Ok(())
            }
            _ => Err(self.bad("set destination is not usable")),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_branch(
        &mut self,
        cc: IntCc,
        w: Width,
        lhs: &Op,
        rhs: &Op,
        target: Lbl,
        patch: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        let zero_cmp = match (cc, lhs, rhs) {
            (IntCc::Eq, Op::Gpr(g), Op::Imm(0)) | (IntCc::Eq, Op::Imm(0), Op::Gpr(g)) => {
                Some(Br::Cbz(gpr(*g, view(w))))
            }
            (IntCc::Ne, Op::Gpr(g), Op::Imm(0)) | (IntCc::Ne, Op::Imm(0), Op::Gpr(g)) => {
                Some(Br::Cbnz(gpr(*g, view(w))))
            }
            _ => None,
        };
        if let Some(br) = zero_cmp {
            return Ok(self.branch(br, target, patch));
        }
        let cc = self.emit_cmp(w, cc, lhs, rhs)?;
        Ok(self.branch(Br::Cond(int_cc(cc)), target, patch))
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_test_branch(
        &mut self,
        w: Width,
        value: &Op,
        mask: Option<&Op>,
        test: TestKind,
        target: Lbl,
        patch: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        if mask.is_none() {
            if let Op::Gpr(g) = value {
                let r = gpr(*g, view(w));
                let br = match test {
                    TestKind::Zero => Br::Cbz(r),
                    TestKind::NonZero => Br::Cbnz(r),
                    TestKind::Sign => Br::Tbnz(r, w.bytes() * 8 - 1),
                };
                return Ok(self.branch(br, target, patch));
            }
        }
        self.test_flags(w, value, mask)?;
        Ok(self.branch(Br::Cond(test_cc(test)), target, patch))
    }

    fn emit_jump(
        &mut self,
        target: &IrTarget,
        patch: bool,
        call: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        if patch && !matches!(target, IrTarget::Label(_)) {
            return Err(LowerError::NotPatchable(self.mn.to_string()));
        }
        let indirect = if call { InstId::Blr } else { InstId::Br };
        match target {
            IrTarget::Label(l) => {
                let t = self.label(*l);
                if patch {
                    let h: PatchableJump = if call {
                        self.asm.patchable_bl(t)
                    } else {
                        self.asm.patchable_b(t)
                    };
                    return Ok(Some(PatchHandle::Jump(h)));
                }
                if call {
                    self.asm.bl(t);
                } else {
                    self.asm.b(t);
                }
            }
            IrTarget::Reg(g) => self.x(indirect, &[go(x(*g))]),
            IrTarget::Mem(m) => {
                let t = x(SCRATCH);
                let a = self.addr_operand(m, 8)?;
                self.x(InstId::Ldr, &[go(t), mo(a)]);
                self.x(indirect, &[go(t)]);
            }
            IrTarget::Abs(v) => {
                let t = x(SCRATCH);
                self.mov_imm(t, *v);
                self.x(indirect, &[go(t)]);
            }
            IrTarget::Extern(e) if e.reach == Reach::Near => {
                let buf = self.asm.buffer_mut();
                buf.add_reloc(Reloc::Arm64Call, RelocTarget::Sym(Sym::from_id(e.id.0)), 0);
                buf.put4(if call { 0x9400_0000 } else { 0x1400_0000 });
            }
            IrTarget::Extern(e) => {
                self.extern_address(SCRATCH, *e);
                self.x(indirect, &[go(x(SCRATCH))]);
            }
        }
        Ok(None)
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_branch_f(
        &mut self,
        cc: FCc,
        k: FKind,
        lhs: &Op,
        rhs: &Op,
        target: Lbl,
        patch: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        if !matches!(lhs, Op::Fpr(_)) && !matches!(rhs, Op::Fpr(_)) {
            return Err(self.bad("float compare needs two live registers"));
        }
        let (first, second) = match cc {
            FCc::Lt | FCc::Le => (rhs, lhs),
            _ => (lhs, rhs),
        };
        let single = match cc {
            FCc::Eq => Some(Cc::Eq),
            FCc::NeUn => Some(Cc::Ne),
            FCc::Gt | FCc::Lt => Some(Cc::Gt),
            FCc::Ge | FCc::Le => Some(Cc::Ge),
            _ => None,
        };
        if patch && single.is_none() {
            return Err(LowerError::NotPatchable(self.mn.to_string()));
        }
        let l = self.fp_src(k, first)?;
        let r = self.fp_src(k, second)?;
        self.x(InstId::Fcmp_v, &[vo(l), vo(r)]);
        if let Some(c) = single {
            return Ok(self.branch(Br::Cond(c), target, patch));
        }
        let t = self.label(target);
        match cc {
            FCc::Ne => {
                let skip = self.asm.get_label();
                b_cond(self.asm, Cc::Vs, skip);
                b_cond(self.asm, Cc::Ne, t);
                self.asm.bind_label(skip);
            }
            FCc::GtUn | FCc::LtUn => {
                b_cond(self.asm, Cc::Lo, t);
                b_cond(self.asm, Cc::Vs, t);
            }
            FCc::GeUn | FCc::LeUn => {
                b_cond(self.asm, Cc::Ls, t);
                b_cond(self.asm, Cc::Vs, t);
            }
            FCc::EqUn => {
                b_cond(self.asm, Cc::Eq, t);
                b_cond(self.asm, Cc::Vs, t);
            }
            _ => unreachable!("single-branch conditions returned above"),
        }
        Ok(None)
    }

    fn emit_fset(
        &mut self,
        cc: FCc,
        k: FKind,
        dst: &Op,
        lhs: &Op,
        rhs: &Op,
    ) -> Result<(), LowerError> {
        let (swap, cond, unordered_and) = match cc {
            FCc::Eq => (false, Cc::Eq, true),
            FCc::Ne => (false, Cc::Ne, true),
            FCc::NeUn => (false, Cc::Ne, false),
            FCc::Gt => (false, Cc::Gt, false),
            FCc::Ge => (false, Cc::Ge, false),
            FCc::Lt => (true, Cc::Gt, false),
            FCc::Le => (true, Cc::Ge, false),
            _ => return Err(self.bad("unordered float set is only defined for eq/ne")),
        };
        if !matches!(lhs, Op::Fpr(_)) && !matches!(rhs, Op::Fpr(_)) {
            return Err(self.bad("float compare needs two live registers"));
        }
        let (first, second) = if swap { (rhs, lhs) } else { (lhs, rhs) };
        let l = self.fp_src(k, first)?;
        let r = self.fp_src(k, second)?;
        let t = match dst {
            Op::Gpr(d) => wv(*d),
            Op::Mem(_) => wv(SCRATCH2),
            _ => return Err(self.bad("float set destination is not usable")),
        };
        self.x(InstId::Fcmp_v, &[vo(l), vo(r)]);
        self.x(InstId::Cset, &[go(t), cond.operand()]);
        if unordered_and {
            self.x(
                InstId::Csel,
                &[go(t), go(t), go(regs::wzr), Cc::Vc.operand()],
            );
        }
        if let Op::Mem(m) = dst {
            let a = self.addr_operand(m, 4)?;
            self.x(InstId::Str, &[go(t), mo(a)]);
        }
        Ok(())
    }

    fn tls_base(&self) -> Operand {
        io(match self.abi {
            crate::Abi::Darwin => 0xDE83,
            crate::Abi::SysV | crate::Abi::Windows => 0xDE82,
        })
    }

    fn emit_tls(&mut self, w: Width, reg: Gpr, idx: i64, load: bool) -> Result<(), LowerError> {
        let off = idx
            .checked_mul(8)
            .ok_or_else(|| self.bad("tls index overflow"))?;
        let base = x(SCRATCH);
        let r = gpr(reg, view(w));
        let sysreg = self.tls_base();
        self.x(InstId::Mrs, &[go(base), sysreg]);
        let id = if load { load_id(w) } else { store_id(w) };
        let scale = i64::from(w.bytes());
        if off >= 0 && off % scale == 0 && off < 4096 * scale {
            self.x(id, &[go(r), mo(ptr(base, off as i32))]);
        } else {
            let t = x(SCRATCH2);
            self.mov_imm(t, off);
            self.x(InstId::Add, &[go(t), go(base), go(t)]);
            self.x(id, &[go(r), mo(ptr(t, 0))]);
        }
        Ok(())
    }

    fn emit_tls_lea(&mut self, reg: Gpr, idx: i64) -> Result<(), LowerError> {
        let off = idx
            .checked_mul(8)
            .ok_or_else(|| self.bad("tls index overflow"))?;
        let base = x(SCRATCH);
        let r = x(reg);
        let sysreg = self.tls_base();
        self.x(InstId::Mrs, &[go(base), sysreg]);
        if off == 0 {
            if r != base {
                self.x(InstId::Mov, &[go(r), go(base)]);
            }
        } else if off > 0 && off < 4096 {
            self.x(InstId::Add, &[go(r), go(base), io(off)]);
        } else if off < 0 && off > -4096 {
            self.x(InstId::Sub, &[go(r), go(base), io(-off)]);
        } else {
            let t = x(SCRATCH2);
            self.mov_imm(t, off);
            self.x(InstId::Add, &[go(r), go(base), go(t)]);
        }
        Ok(())
    }

    fn emit_rmw(&mut self, op: AtomicOp, w: Width, a: &Op, b: &Op) -> Result<(), LowerError> {
        let (mem, r) = match (a, b) {
            (Op::Mem(m), Op::Gpr(r)) | (Op::Gpr(r), Op::Mem(m)) => (m, gpr(*r, view(w))),
            (Op::Mem(m), Op::Imm(_)) | (Op::Imm(_), Op::Mem(m)) => {
                let v = if matches!(a, Op::Imm(_)) { a } else { b };
                let r = gpr(SCRATCH2, view(w));
                self.load_into(v, r, w)?;
                (m, r)
            }
            _ => {
                return Err(
                    self.bad("atomic r/m needs one memory and one register or immediate operand")
                )
            }
        };
        let addr = self.addr_base_only(mem)?;
        let id = match (op, w) {
            (AtomicOp::Add | AtomicOp::Sub, Width::B8) => InstId::Ldaddalb,
            (AtomicOp::Add | AtomicOp::Sub, Width::B16) => InstId::Ldaddalh,
            (AtomicOp::Add | AtomicOp::Sub, _) => InstId::Ldaddal,
            (AtomicOp::Or, Width::B8) => InstId::Ldsetalb,
            (AtomicOp::Or, Width::B16) => InstId::Ldsetalh,
            (AtomicOp::Or, _) => InstId::Ldsetal,
            (AtomicOp::Xor, Width::B8) => InstId::Ldeoralb,
            (AtomicOp::Xor, Width::B16) => InstId::Ldeoralh,
            (AtomicOp::Xor, _) => InstId::Ldeoral,
            (AtomicOp::Xchg, Width::B8) => InstId::Swpalb,
            (AtomicOp::Xchg, Width::B16) => InstId::Swpalh,
            (AtomicOp::Xchg, _) => InstId::Swpal,
            (AtomicOp::And, Width::B8) => InstId::Ldclralb,
            (AtomicOp::And, Width::B16) => InstId::Ldclralh,
            (AtomicOp::And, _) => InstId::Ldclral,
        };
        match op {
            AtomicOp::Sub => self.x(InstId::Neg, &[go(r), go(r)]),
            AtomicOp::And => self.x(InstId::Mvn, &[go(r), go(r)]),
            _ => {}
        }
        self.x(id, &[go(r), go(r), mo(addr)]);
        Ok(())
    }

    fn emit_cas(
        &mut self,
        w: Width,
        mem: &Mem,
        src: Gpr,
        branch: Option<Lbl>,
    ) -> Result<(), LowerError> {
        let vw = view(w);
        let lo = gpr(T0, vw);
        let des = gpr(src, vw);
        let saved = gpr(SCRATCH2, vw);
        let addr = self.addr_base_only(mem)?;
        // `CASAL` overwrites the value, save it.
        self.x(InstId::Mov, &[go(saved), go(lo)]);
        let id = match w {
            Width::B8 => InstId::Casalb,
            Width::B16 => InstId::Casalh,
            Width::B32 | Width::B64 => InstId::Casal,
        };
        self.x(id, &[go(lo), go(des), mo(addr)]);
        if let Some(target) = branch {
            self.x(InstId::Cmp, &[go(lo), go(saved)]);
            let t = self.label(target);
            b_cond(self.asm, Cc::Ne, t);
        }
        Ok(())
    }

    fn emit_store_cond(
        &mut self,
        w: Width,
        status: Gpr,
        src: Gpr,
        mem: &Mem,
    ) -> Result<(), LowerError> {
        let id = match w {
            Width::B8 => InstId::Stlxrb,
            Width::B16 => InstId::Stlxrh,
            Width::B32 | Width::B64 => InstId::Stlxr,
        };
        let aliased =
            status == src || mem.base == Some(status) || mem.index.map(|(r, _)| r) == Some(status);
        if aliased {
            let t = self.synth_addr(mem)?;
            self.x(
                id,
                &[go(wv(SCRATCH2)), go(gpr(src, view(w))), mo(ptr(t, 0))],
            );
            self.x(InstId::Mov, &[go(wv(status)), go(wv(SCRATCH2))]);
        } else {
            let a = self.addr_base_only(mem)?;
            self.x(id, &[go(wv(status)), go(gpr(src, view(w))), mo(a)]);
        }
        Ok(())
    }

    fn emit_pair(
        &mut self,
        w: PairW,
        first: &Op,
        second: &Op,
        mem: &Mem,
        load: bool,
    ) -> Result<(), LowerError> {
        let scale: i64 = match w {
            PairW::B32 => 4,
            PairW::B64 | PairW::F64 => 8,
            PairW::V128 => 16,
        };
        let addr = self.pair_addr_operand(mem, scale)?;
        let render = |op: &Op| -> Option<Operand> {
            match (w, op) {
                (PairW::B32, Op::Gpr(g)) => Some(go(wv(*g))),
                (PairW::B64, Op::Gpr(g)) => Some(go(x(*g))),
                (PairW::F64, Op::Fpr(f)) => Some(vo(fpr(*f, FKind::F64))),
                (PairW::V128, Op::Fpr(f)) => Some(vo(qreg(*f))),
                _ => None,
            }
        };
        let mismatch = || bad(self.mn, "pair access operand does not match its width");
        let aliased = load && crate::ir::op_eq(first, second);
        let first_op = if aliased {
            match w {
                PairW::B32 => go(wv(SCRATCH)),
                PairW::B64 => go(x(SCRATCH)),
                PairW::F64 => vo(fpr(FSCRATCH, FKind::F64)),
                PairW::V128 => vo(qreg(FSCRATCH)),
            }
        } else {
            render(first).ok_or_else(mismatch)?
        };
        let second_op = render(second).ok_or_else(mismatch)?;
        let id = match (w, load) {
            (PairW::B32 | PairW::B64, true) => InstId::Ldp,
            (PairW::B32 | PairW::B64, false) => InstId::Stp,
            (_, true) => InstId::Ldp_v,
            (_, false) => InstId::Stp_v,
        };
        self.x(id, &[first_op, second_op, mo(addr)]);
        Ok(())
    }

    fn stack_group(&mut self, ops: &[Op]) -> Result<(), LowerError> {
        let push = matches!(self.mn, Mnemonic::Push | Mnemonic::PushCalleeSaves);
        let n = ops.len();
        if n == 0 {
            return Err(self.bad("needs at least one operand"));
        }
        let bytes = crate::ir::aligned_push_bytes(n);
        if bytes > 512 {
            return Err(self.bad("too many operands for one aarch64 stack block"));
        }
        for op in ops {
            match op {
                Op::Gpr(SP) => return Err(self.bad("aarch64 cannot push or pop `sp`")),
                Op::Gpr(_) => {}
                Op::Imm(_) if push => {}
                Op::Mem(m) if m.base == Some(SP) || m.index.is_some_and(|(i, _)| i == SP) => {
                    return Err(
                        self.bad("`sp`-relative memory operands are not supported on aarch64")
                    )
                }
                Op::Mem(_) => {}
                _ => return Err(self.bad("unsupported push/pop operand")),
            }
        }
        let off = |i: usize| crate::ir::aligned_push_offset(n, i) as i32;
        let bytes = bytes as i32;
        let spr = x(SP);
        // Units from the bottom of the block up: `(lower operand, upper
        // operand)`. Computed on demand instead of collected, so a push/pop
        // group does not allocate.
        let unit = |k: usize| {
            let lo = n - 1 - 2 * k;
            (lo, (lo >= 1).then(|| lo - 1))
        };
        let units = n.div_ceil(2);

        if push {
            for k in 0..units {
                let (lo, hi) = unit(k);
                let r_hi = match hi {
                    Some(h) => Some(self.op_to_reg(&ops[h], Width::B64, SCRATCH2)?),
                    None => None,
                };
                let r_lo = self.op_to_reg(&ops[lo], Width::B64, SCRATCH)?;
                let addr = if k == 0 {
                    ptr_pre(spr, -bytes)
                } else {
                    ptr(spr, off(lo))
                };
                match r_hi {
                    Some(r_hi) => self.x(InstId::Stp, &[go(r_lo), go(r_hi), mo(addr)]),
                    None => self.x(InstId::Str, &[go(r_lo), mo(addr)]),
                }
            }
            return Ok(());
        }

        for k in (0..units).rev() {
            let (lo, hi) = unit(k);
            let last = k == 0;
            let pair = hi.and_then(|h| match (&ops[lo], &ops[h]) {
                (Op::Gpr(a), Op::Gpr(b)) if a != b => Some((*a, *b)),
                _ => None,
            });
            if let Some((a, b)) = pair {
                let addr = if last {
                    ptr_post(spr, bytes)
                } else {
                    ptr(spr, off(lo))
                };
                self.x(InstId::Ldp, &[go(x(a)), go(x(b)), mo(addr)]);
                continue;
            }
            if let (None, Op::Gpr(g), true) = (hi, &ops[lo], last) {
                self.x(InstId::Ldr, &[go(x(*g)), mo(ptr_post(spr, bytes))]);
                continue;
            }

            for idx in hi.into_iter().chain(std::iter::once(lo)) {
                let slot = ptr(spr, off(idx));
                match &ops[idx] {
                    Op::Gpr(g) => self.x(InstId::Ldr, &[go(x(*g)), mo(slot)]),
                    Op::Mem(m) => {
                        let t = x(SCRATCH2);
                        self.x(InstId::Ldr, &[go(t), mo(slot)]);
                        let a = self.addr_operand(m, 8)?;
                        self.x(InstId::Str, &[go(t), mo(a)]);
                    }
                    _ => unreachable!("operands were checked above"),
                }
            }
            if last {
                self.x(InstId::Add, &[go(spr), go(spr), io(i64::from(bytes))]);
            }
        }
        Ok(())
    }
}
