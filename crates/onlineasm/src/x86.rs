//! x86-64 lowering.

use crate::ir::expand;
use crate::ir::{
    Alu3, AluOp, AtomicOp, BitcastDir, FAlu, FArith3, FCc, FKind, FlagAlu, FmaOp, Fpr, IntCc,
};
use crate::ir::{
    Extern, Gpr, Inst, LabelResolver, Lbl, LowerError, Mem, Mnemonic, Op, PatchHandle, Reach,
    Scratch,
};
use crate::ir::{
    LeaSrc, PairW, PredFlag, RoundMode, ShiftCnt, ShiftOp, Sx, Target as IrTarget, TestKind, Width,
};
use asmkit::x86::CondCode;
use asmkit::x86::*;
use asmkit::{imm, Label, Operand, OperandCast, PatchableJump, Sym};

type AMem = asmkit::x86::Mem;

/// An extern in an operand slot `expand` does not route one to.
const EXTERN_MISUSE: &str = "an external symbol is only a `jmp`/`call` target or an address source";
type W = Width;

/// The expansion scratch GPR (`r11`).
const SCRATCH: Gpr = Gpr(11);
/// The expansion scratch FPR (`xmm7`).
const FSCRATCH: Fpr = Fpr(7);
const RAX: Gpr = Gpr(0);
const RCX: Gpr = Gpr(1);
const RDX: Gpr = Gpr(2);
const RSP: Gpr = Gpr(4);

#[allow(clippy::panic)]
fn gx(g: Gpr) -> Gp {
    assert!(g.0 < 16, "onlineasm: bad x86 GPR id {}", g.0);
    *Gpq::from_id(u32::from(g.0))
}

pub fn gpr_id(g: Gp) -> Gpr {
    Gpr(g.id() as u8)
}

pub fn fpr_id(x: Xmm) -> Fpr {
    Fpr(x.id() as u8)
}

#[allow(clippy::panic)]
fn vx(x: Fpr) -> Xmm {
    assert!(x.0 < 16, "onlineasm: bad x86 XMM id {}", x.0);
    Xmm::from_id(u32::from(x.0))
}

fn bad(mn: Mnemonic, msg: impl Into<String>) -> LowerError {
    LowerError::BadOperand {
        mnemonic: mn.to_string(),
        msg: msg.into(),
    }
}

fn r8(g: Gpr) -> GpbLo {
    GpbLo::from_id(u32::from(g.0))
}
fn r16(g: Gpr) -> Gpw {
    Gpw::from_id(u32::from(g.0))
}
fn r32(g: Gpr) -> Gpd {
    Gpd::from_id(u32::from(g.0))
}
fn r64(g: Gpr) -> Gpq {
    Gpq::from_id(u32::from(g.0))
}

// Operands.

/// `g` at width `w`.
fn gw(g: Gpr, w: W) -> Operand {
    match w {
        W::B8 => *r8(g).as_operand(),
        W::B16 => *r16(g).as_operand(),
        W::B32 => *r32(g).as_operand(),
        W::B64 => *r64(g).as_operand(),
    }
}

fn xo(x: Fpr) -> Operand {
    *vx(x).as_operand()
}

fn io(v: i64) -> Operand {
    *imm(v).as_operand()
}

/// `[base + index << shift + disp]`
fn sib(base: Gpr, index: Gpr, shift: u32, disp: i32, size: u32) -> AMem {
    let (base, index) = if index == RSP && shift == 0 {
        (index, base)
    } else {
        (base, index)
    };
    ptr_index(&gx(base), &gx(index), shift, disp, size)
}

fn amem(a: &Mem, size: u32, extra: i64, res: &LabelResolver) -> AMem {
    if let Some(label) = a.disp.label() {
        assert!(
            a.base.is_none() && a.index.is_none(),
            "onlineasm: a label-addressed memory operand has no base or index"
        );
        let t = res
            .get(label)
            .unwrap_or_else(|| panic!("onlineasm: label handle does not belong to this assembler"));
        return label_ptr(t, extra as i32, size);
    }
    let disp = i64::from(a.disp.const_or_zero()).wrapping_add(extra);
    match (a.base, a.index) {
        (Some(b), Some((i, scale))) => sib(b, i, scale.trailing_zeros(), disp as i32, size),
        (Some(b), None) => ptr(&gx(b), disp as i32, size),
        (None, Some((i, scale))) => {
            u64_ptr_index_abs(disp as u64, &gx(i), scale.trailing_zeros(), size)
        }
        (None, None) => u64_ptr_abs(disp as u64, size),
    }
}

fn mo(a: &Mem, w: W, res: &LabelResolver) -> Operand {
    *amem(a, w.bytes(), 0, res).as_operand()
}

fn mo_at(a: &Mem, size: u32, extra: i64, res: &LabelResolver) -> Operand {
    *amem(a, size, extra, res).as_operand()
}

/// `[rsp + disp]`.
fn rsp_mem(disp: i32, size: u32) -> Operand {
    *ptr(&gx(RSP), disp, size).as_operand()
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

fn e_lock(asm: &mut Assembler, id: InstId, ops: &[Operand]) {
    asm.lock();
    e(asm, id, ops);
}

/// `[rip + label]`
fn ext_sym(e: Extern) -> Sym {
    Sym::from_id(e.id.0)
}

fn label_mem(asm: &mut Assembler, res: &mut LabelResolver, l: Lbl) -> Operand {
    let t = res.resolve(l, || asm.get_label());
    *label_ptr(t, 0, 0).as_operand()
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Cond {
    O,
    B,
    NB,
    Z,
    NZ,
    BE,
    A,
    S,
    P,
    NP,
    L,
    GE,
    LE,
    G,
}

impl Cond {
    fn x86(self) -> CondCode {
        match self {
            Cond::O => CondCode::O,
            Cond::B => CondCode::C,
            Cond::NB => CondCode::NC,
            Cond::Z => CondCode::Z,
            Cond::NZ => CondCode::NZ,
            Cond::BE => CondCode::BE,
            Cond::A => CondCode::A,
            Cond::S => CondCode::S,
            Cond::P => CondCode::P,
            Cond::NP => CondCode::NP,
            Cond::L => CondCode::L,
            Cond::GE => CondCode::GE,
            Cond::LE => CondCode::LE,
            Cond::G => CondCode::G,
        }
    }

    fn jcc(self) -> InstId {
        match self {
            Cond::O => InstId::Jo,
            Cond::B => InstId::Jb,
            Cond::NB => InstId::Jnb,
            Cond::Z => InstId::Jz,
            Cond::NZ => InstId::Jnz,
            Cond::BE => InstId::Jbe,
            Cond::A => InstId::Jnbe,
            Cond::S => InstId::Js,
            Cond::P => InstId::Jp,
            Cond::NP => InstId::Jnp,
            Cond::L => InstId::Jl,
            Cond::GE => InstId::Jnl,
            Cond::LE => InstId::Jle,
            Cond::G => InstId::Jnle,
        }
    }

    fn setcc(self) -> InstId {
        match self {
            Cond::O => InstId::Seto,
            Cond::B => InstId::Setb,
            Cond::NB => InstId::Setnb,
            Cond::Z => InstId::Setz,
            Cond::NZ => InstId::Setnz,
            Cond::BE => InstId::Setbe,
            Cond::A => InstId::Setnbe,
            Cond::S => InstId::Sets,
            Cond::P => InstId::Setp,
            Cond::NP => InstId::Setnp,
            Cond::L => InstId::Setl,
            Cond::GE => InstId::Setnl,
            Cond::LE => InstId::Setle,
            Cond::G => InstId::Setnle,
        }
    }
}

impl From<IntCc> for Cond {
    fn from(cc: IntCc) -> Self {
        match cc {
            IntCc::Eq => Cond::Z,
            IntCc::Ne => Cond::NZ,
            IntCc::Hi => Cond::A,
            IntCc::Hs => Cond::NB,
            IntCc::Lo => Cond::B,
            IntCc::Ls => Cond::BE,
            IntCc::Gt => Cond::G,
            IntCc::Ge => Cond::GE,
            IntCc::Lt => Cond::L,
            IntCc::Le => Cond::LE,
        }
    }
}

impl From<PredFlag> for Cond {
    fn from(flag: PredFlag) -> Self {
        match flag {
            PredFlag::O => Cond::O,
            PredFlag::S => Cond::S,
            PredFlag::Z => Cond::Z,
            PredFlag::Nz => Cond::NZ,
        }
    }
}

impl From<TestKind> for Cond {
    fn from(test: TestKind) -> Self {
        match test {
            TestKind::Sign => Cond::S,
            TestKind::Zero => Cond::Z,
            TestKind::NonZero => Cond::NZ,
        }
    }
}

fn jcc(asm: &mut Assembler, cc: Cond, target: Label) {
    let refs = [target.as_operand()];
    asm.emit_n(cc.jcc() as u32, &refs);
}

fn branch_to(
    asm: &mut Assembler,
    res: &mut LabelResolver,
    cc: Cond,
    target: Lbl,
    patch: bool,
) -> Option<PatchHandle> {
    let t = res.resolve(target, || asm.get_label());
    if patch {
        return Some(PatchHandle::Jump(asm.patchable_jcc(cc.x86(), t)));
    }
    jcc(asm, cc, t);
    None
}

impl crate::IntoOperand for Gp {
    fn into_operand<const BACKWARD: bool>(self, _asm: &crate::Assembler<BACKWARD>) -> Op {
        Op::Gpr(gpr_id(self))
    }
}

impl crate::IntoOperand for Gpq {
    fn into_operand<const BACKWARD: bool>(self, _asm: &crate::Assembler<BACKWARD>) -> Op {
        Op::Gpr(gpr_id(self.0))
    }
}

impl crate::IntoOperand for Gpd {
    fn into_operand<const BACKWARD: bool>(self, _asm: &crate::Assembler<BACKWARD>) -> Op {
        Op::Gpr(gpr_id(self.0))
    }
}

impl crate::IntoOperand for Xmm {
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
    let mut asm = asmkit::x86::Assembler::new(buf);
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
    let mut asm = asmkit::x86::Assembler::new(buf);
    let mut res = LabelResolver::new(labels, label_base);
    lower_ops_patched(&mut asm, ctx, mnemonic, ops, &mut res, abi)
}

pub(crate) static INFO: TargetInfo = {
    let t = offlineasm_ir::regs::X86;
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
    let saved: &[u8] = match abi {
        // rbx, r12-r15
        crate::Abi::SysV | crate::Abi::Darwin => &[3, 12, 13, 14, 15],
        // rbx, rsi, rdi, r12-r15
        crate::Abi::Windows => &[3, 6, 7, 12, 13, 14, 15],
    };
    crate::ir::check_callee_saved(mnemonic, ops, saved)?;
    let insts = expand(mnemonic, ops, ctx, false)?;
    for inst in &insts {
        let handle = emit_inst(asm, mnemonic, inst, res, abi)?;
        debug_assert!(handle.is_none(), "unpatched lowering emitted a patch site");
    }
    Ok(())
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

#[allow(clippy::too_many_lines)]
fn emit_inst(
    asm: &mut Assembler,
    mn: Mnemonic,
    inst: &Inst,
    res: &mut LabelResolver,
    abi: crate::Abi,
) -> Result<Option<PatchHandle>, LowerError> {
    let mut l = Lx { asm, mn, res };
    let none = Ok(None);
    match inst {
        Inst::Mov { w, dst, src, patch } => {
            if *patch {
                return match (dst, src) {
                    (Op::Gpr(d), Op::Imm(v)) => Ok(Some(PatchHandle::Data(
                        l.asm.patchable_mov(r64(*d), imm(*v)),
                    ))),
                    _ => Err(LowerError::NotPatchable(mn.to_string())),
                };
            }
            l.mov(*w, dst, src)?;
            none
        }
        Inst::MovZero32 { dst, src } => {
            l.mov(W::B32, dst, src)?;
            none
        }
        Inst::Bind(lbl) => {
            let t = l.res.resolve(*lbl, || l.asm.get_label());
            l.asm.bind_label(t);
            none
        }
        Inst::Bswap { w, dst, src } => {
            l.bswap(*w, dst, src)?;
            none
        }
        Inst::Load {
            w,
            sx,
            dst,
            addr,
            // x64 loads are already acquire, no need to handle
            acquire: _,
        } => {
            l.load(*w, *sx, *dst, addr);
            none
        }
        Inst::Store { w, src, addr } => {
            l.store(*w, src, addr)?;
            none
        }
        Inst::LoadF { k, dst, addr } => {
            l.x(fk_mov(*k), &[xo(*dst), l.mo(addr, fk_width(*k))]);
            none
        }
        Inst::StoreF { k, src, addr } => {
            l.x(fk_mov(*k), &[l.mo(addr, fk_width(*k)), xo(*src)]);
            none
        }
        Inst::FMov { k, dst, src } => {
            l.x(fk_mov(*k), &[xo(*dst), xo(*src)]);
            none
        }
        Inst::LoadV { dst, addr } => {
            l.x(InstId::Movdqu, &[xo(*dst), l.mo_at(addr, 16, 0)]);
            none
        }
        Inst::StoreV { src, addr } => {
            l.x(InstId::Movups, &[l.mo_at(addr, 16, 0), xo(*src)]);
            none
        }
        Inst::VMov { dst, src } => {
            l.x(InstId::Movdqu, &[xo(*dst), xo(*src)]);
            none
        }
        Inst::Lea { w, dst, src } => {
            l.lea(*w, *dst, src)?;
            none
        }
        Inst::Push { op } => {
            l.push(op)?;
            none
        }
        Inst::Pop { op } => {
            l.pop(op)?;
            none
        }
        Inst::PushV { src } => {
            l.x(InstId::Sub, &[gw(RSP, W::B64), io(16)]);
            l.x(InstId::Movdqu, &[rsp_mem(0, 16), xo(*src)]);
            none
        }
        Inst::PopV { dst } => {
            l.x(InstId::Movdqu, &[xo(*dst), rsp_mem(0, 16)]);
            l.x(InstId::Add, &[gw(RSP, W::B64), io(16)]);
            none
        }
        Inst::Peek { disp, dst } => {
            l.x(InstId::Mov, &[gw(*dst, W::B64), rsp_mem(*disp, 8)]);
            none
        }
        Inst::Poke { disp, src } => {
            l.x(InstId::Mov, &[rsp_mem(*disp, 8), gw(*src, W::B64)]);
            none
        }
        Inst::Add { w, op } => {
            l.add3(*w, op)?;
            none
        }
        Inst::Sub { w, op } => {
            l.bin3(Bin::Sub, *w, op)?;
            none
        }
        Inst::Mul { w, op } => {
            l.mul3(*w, op)?;
            none
        }
        Inst::And { w, op } => {
            l.bin3(Bin::And, *w, op)?;
            none
        }
        Inst::Or { w, op } => {
            l.bin3(Bin::Or, *w, op)?;
            none
        }
        Inst::Xor { w, op } => {
            l.bin3(Bin::Xor, *w, op)?;
            none
        }
        Inst::Not { w, dst } => {
            l.unop(InstId::Not, *w, dst)?;
            none
        }
        Inst::Neg { w, dst } => {
            l.unop(InstId::Neg, *w, dst)?;
            none
        }
        Inst::Shift { w, op, dst, cnt } => {
            l.shift(*w, *op, *dst, cnt)?;
            none
        }
        Inst::MulImm { w, dst, lhs, imm } => {
            l.mul_imm(*w, *dst, *lhs, *imm);
            none
        }
        Inst::AluS { op, w, alu } => {
            let op = match op {
                AluOp::Add => Bin::Add,
                AluOp::Sub => Bin::Sub,
                AluOp::Or => Bin::Or,
            };
            l.flag_bin3(op, *w, alu)?;
            none
        }
        Inst::Adc { dst, src } => {
            l.bin2(InstId::Adc, W::B64, dst, src)?;
            none
        }
        Inst::Sbb { dst, src } => {
            l.bin2(InstId::Sbb, W::B64, dst, src)?;
            none
        }
        Inst::MulWide {
            signed,
            dst,
            lhs,
            rhs,
        } => {
            l.mul_wide(*signed, *dst, *lhs, *rhs);
            none
        }
        Inst::MulHigh { signed, rhs } => {
            l.mul_high(*signed, rhs)?;
            none
        }
        Inst::DivMod1 { signed, w, divisor } => {
            l.div_mod1(*signed, *w, divisor)?;
            none
        }
        Inst::Div3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        } => {
            l.div3(*signed, *w, *dst, dvd, dvs, false)?;
            none
        }
        Inst::Rem3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        } => {
            l.div3(*signed, *w, *dst, dvd, dvs, true)?;
            none
        }
        Inst::Extend {
            from,
            to,
            sx,
            dst,
            src,
        } => {
            l.extend(*from, *to, *sx, *dst, src)?;
            none
        }
        Inst::Ctz { w, dst, src } => {
            l.count_zeros(*w, *dst, src, true)?;
            none
        }
        Inst::Clz { w, dst, src } => {
            l.count_zeros(*w, *dst, src, false)?;
            none
        }
        Inst::Popcnt { w, dst, src } => {
            let s = l.rm(*w, src, "`popcnt` needs a register or memory source")?;
            l.x(InstId::Popcnt, &[gw(*dst, *w), s]);
            none
        }
        Inst::Cqo { quad } => {
            l.x(if *quad { InstId::Cqo } else { InstId::Cdq }, &[]);
            none
        }
        Inst::AddShifted {
            dst,
            lhs,
            rhs,
            amount,
        } => {
            l.add_shifted(*dst, *lhs, *rhs, *amount);
            none
        }
        Inst::Cmov {
            w,
            zero,
            dst,
            src,
            test,
        } => {
            l.cmov(*w, *zero, *dst, src, *test)?;
            none
        }
        Inst::VecExtract { w, dst, src, lane } => {
            let (id, to) = match w {
                W::B8 => (InstId::Pextrb, W::B32),
                W::B16 => (InstId::Pextrw, W::B32),
                W::B32 => (InstId::Pextrd, W::B32),
                W::B64 => (InstId::Pextrq, W::B64),
            };
            l.x(id, &[gw(*dst, to), xo(*src), io(i64::from(*lane))]);
            none
        }

        // Branches, sets, control flow.
        Inst::Branch {
            cc,
            w,
            lhs,
            rhs,
            target,
            patch,
        } => {
            l.int_compare(*cc, *w, lhs, rhs)?;
            Ok(branch_to(l.asm, l.res, Cond::from(*cc), *target, *patch))
        }
        Inst::TestBranch {
            w,
            value,
            mask,
            test,
            target,
            patch,
        } => {
            l.test_flags(*w, value, mask.as_ref())?;
            Ok(branch_to(l.asm, l.res, Cond::from(*test), *target, *patch))
        }
        Inst::OpBranch {
            op,
            w,
            flag,
            args,
            target,
            patch,
        } => {
            l.op_branch(*op, *w, *flag, args.as_slice())?;
            Ok(branch_to(l.asm, l.res, Cond::from(*flag), *target, *patch))
        }
        Inst::FlagBranch {
            flag,
            target,
            patch,
        } => Ok(branch_to(l.asm, l.res, Cond::from(*flag), *target, *patch)),
        Inst::Jump { target, patch } => l.jump(target, *patch, false),
        Inst::Call { target, patch } => l.jump(target, *patch, true),
        Inst::Ret => {
            l.x(InstId::Ret, &[]);
            none
        }
        Inst::Break => {
            l.x(InstId::Int3, &[]);
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
            l.int_compare(*cc, *w, lhs, rhs)?;
            l.set_zx(Cond::from(*cc), dst)?;
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
            l.set_zx(Cond::from(*test), dst)?;
            none
        }

        // Float.
        Inst::FArith { op, k, arith } => {
            l.farith(*op, *k, arith)?;
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
            l.fma(*op, *k, a, b, c, *dst)?;
            none
        }
        Inst::FSqrt { k, dst, src } => {
            let s = l.fp_src(*k, src)?;
            let id = match k {
                FKind::F32 => InstId::Sqrtss,
                FKind::F64 => InstId::Sqrtsd,
            };
            l.x(id, &[xo(*dst), s]);
            none
        }
        Inst::FRound { k, mode, dst, src } => {
            let s = l.fp_src(*k, src)?;
            let id = match k {
                FKind::F32 => InstId::Roundss,
                FKind::F64 => InstId::Roundsd,
            };
            l.x(id, &[xo(*dst), s, io(round_imm(*mode))]);
            none
        }
        Inst::FAbs { k, dst, src } => {
            l.fp_sign(*k, *dst, src, false)?;
            none
        }
        Inst::FNeg { k, dst, src } => {
            l.fp_sign(*k, *dst, src, true)?;
            none
        }
        Inst::FBit { or, k, dst, src } => {
            let s = l.fp_src(*k, src)?;
            let id = match (*or, *k) {
                (false, FKind::F32) => InstId::Andps,
                (false, FKind::F64) => InstId::Andpd,
                (true, FKind::F32) => InstId::Orps,
                (true, FKind::F64) => InstId::Orpd,
            };
            l.x(id, &[xo(*dst), s]);
            none
        }
        Inst::CvtFI { k, w, dst, src } => {
            let s = l.fp_src(*k, src)?;
            let id = match k {
                FKind::F32 => InstId::Cvttss2si,
                FKind::F64 => InstId::Cvttsd2si,
            };
            l.x(id, &[gw(*dst, *w), s]);
            none
        }
        Inst::CvtIF {
            signed,
            from,
            k,
            dst,
            src,
        } => {
            if !*signed {
                return Err(bad(mn, "unsigned int-to-float uses the shared slow path"));
            }
            let s = match src {
                Op::Gpr(g) => gw(*g, *from),
                Op::Mem(m) => l.mo(m, *from),
                _ => return Err(bad(mn, "int-to-float needs a register or memory source")),
            };
            let id = match k {
                FKind::F32 => InstId::Cvtsi2ss,
                FKind::F64 => InstId::Cvtsi2sd,
            };
            l.x(id, &[xo(*dst), s]);
            none
        }
        Inst::CvtFF { from, to, dst, src } => {
            let s = l.fp_src(*from, src)?;
            #[allow(clippy::match_same_arms)]
            let id = match (from, to) {
                (FKind::F32, FKind::F64) => InstId::Cvtss2sd,
                (FKind::F64, FKind::F32) => InstId::Cvtsd2ss,
                _ => return Err(bad(mn, "float conversion needs two different kinds")),
            };
            l.x(id, &[xo(*dst), s]);
            none
        }
        Inst::Bitcast { dir, dst, src } => {
            l.bitcast(*dir, dst, src)?;
            none
        }
        Inst::BranchF {
            cc,
            k,
            lhs,
            rhs,
            target,
            patch,
        } => l.branch_f(*cc, *k, lhs, rhs, *target, *patch),
        Inst::FSet {
            cc,
            k,
            dst,
            lhs,
            rhs,
        } => {
            l.fset(*cc, *k, dst, lhs, rhs)?;
            none
        }

        // Misc.
        Inst::Fence { full: _ } => {
            e_lock(l.asm, InstId::Or, &[rsp_mem(0, 4), io(0)]);
            none
        }
        Inst::Pause => {
            l.x(InstId::Pause, &[]);
            none
        }
        Inst::TlsLoad { w, dst, idx } => {
            l.tls(*w, *dst, *idx, true, abi)?;
            none
        }
        Inst::TlsStore { w, src, idx } => {
            l.tls(*w, *src, *idx, false, abi)?;
            none
        }
        Inst::TlsLea { dst, idx } => {
            let off = tls_offset(mn, *idx)?;
            let m = tls_mem(off, 0, abi);
            l.x(InstId::Lea, &[gw(*dst, W::B64), m]);
            none
        }
        Inst::AtomicRmw { op, w, a, b } => {
            l.atomic_rmw(*op, *w, a, b)?;
            none
        }
        Inst::AtomicCas {
            w,
            mem,
            src,
            branch,
        } => {
            e_lock(l.asm, InstId::Cmpxchg, &[l.mo(mem, *w), gw(*src, *w)]);
            if let Some(target) = branch {
                branch_to(l.asm, l.res, Cond::NZ, *target, false);
            }
            none
        }
        Inst::LoadLinked { w, mem, dst } => {
            l.x(InstId::Mov, &[gw(*dst, *w), l.mo(mem, *w)]);
            l.zero_extend_result(*dst, *w);
            none
        }
        Inst::StoreCond {
            w,
            status,
            src,
            mem,
        } => {
            e_lock(l.asm, InstId::Cmpxchg, &[l.mo(mem, *w), gw(*src, *w)]);
            l.set_zx(Cond::NZ, &Op::Gpr(*status))?;
            none
        }
        Inst::PairLoad { w, dst1, dst2, mem } => {
            l.pair(*w, dst1, dst2, mem, true)?;
            none
        }
        Inst::PairStore { w, src1, src2, mem } => {
            l.pair(*w, src1, src2, mem, false)?;
            none
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Bin {
    Add,
    Sub,
    And,
    Or,
    Xor,
}

impl Bin {
    fn id(self) -> InstId {
        match self {
            Bin::Add => InstId::Add,
            Bin::Sub => InstId::Sub,
            Bin::And => InstId::And,
            Bin::Or => InstId::Or,
            Bin::Xor => InstId::Xor,
        }
    }

    /// Whether swapping the two sources leaves the result unchanged.
    fn commutative(self) -> bool {
        self != Bin::Sub
    }
}

fn imm_encodable(w: W, v: i64) -> bool {
    match w {
        W::B8 => (-128..=255).contains(&v),
        W::B16 => (-32768..=65535).contains(&v),
        W::B32 => (i64::from(i32::MIN)..=i64::from(u32::MAX)).contains(&v),
        W::B64 => W::B32.fits(v),
    }
}

fn fk_width(k: FKind) -> W {
    match k {
        FKind::F32 => W::B32,
        FKind::F64 => W::B64,
    }
}

/// The float move (`movss` / `movsd`).
fn fk_mov(k: FKind) -> InstId {
    match k {
        FKind::F32 => InstId::Movss,
        FKind::F64 => InstId::Movsd,
    }
}

fn round_imm(mode: RoundMode) -> i64 {
    match mode {
        RoundMode::Nearest => 0,
        RoundMode::Down => 1,
        RoundMode::Up => 2,
        RoundMode::Trunc => 3,
    }
}

fn truncate(v: i64, w: W) -> i64 {
    match w {
        W::B8 => i64::from(v as i8),
        W::B16 => i64::from(v as i16),
        W::B32 => i64::from(v as i32),
        W::B64 => v,
    }
}

fn tls_offset(mn: Mnemonic, idx: i64) -> Result<i64, LowerError> {
    idx.checked_mul(8)
        .filter(|off| W::B32.fits(*off))
        .ok_or_else(|| bad(mn, format!("tls index {idx} is out of range")))
}

fn tls_mem(off: i64, size: u32, abi: crate::Abi) -> Operand {
    let seg = match abi {
        crate::Abi::Windows | crate::Abi::Darwin => SReg::GS,
        crate::Abi::SysV => SReg::FS,
    };
    let mut m = u64_ptr_abs(off as u64, size);
    m.set_segment(SReg::from_id(seg));
    *m.as_operand()
}

struct Lx<'a, 'b, 'c> {
    asm: &'a mut Assembler<'b>,
    mn: Mnemonic,
    res: &'a mut LabelResolver<'c>,
}

impl Lx<'_, '_, '_> {
    fn x(&mut self, id: InstId, ops: &[Operand]) {
        e(self.asm, id, ops);
    }

    fn bad(&self, msg: impl Into<String>) -> LowerError {
        bad(self.mn, msg)
    }

    /// A `[mem]` operand at width `w`, resolving a label displacement through
    /// this assembler's labels.
    fn mo(&self, a: &Mem, w: W) -> Operand {
        mo(a, w, self.res)
    }

    /// Like [`Lx::mo`], with an explicit access size and trailing offset.
    fn mo_at(&self, a: &Mem, size: u32, extra: i64) -> Operand {
        mo_at(a, size, extra, self.res)
    }

    fn new_label(&mut self) -> Label {
        self.asm.get_label()
    }

    fn bind(&mut self, l: Label) {
        self.asm.bind_label(l);
    }

    fn jmp_label(&mut self, l: Label) {
        self.x(InstId::Jmp, &[*l.as_operand()]);
    }

    fn load_scratch_imm(&mut self, v: i64) {
        if W::B32.fits(v) {
            self.x(InstId::Mov, &[gw(SCRATCH, W::B64), io(v)]);
        } else {
            self.x(InstId::Movabs, &[gw(SCRATCH, W::B64), io(v)]);
        }
    }

    fn rm(&self, w: W, op: &Op, msg: &str) -> Result<Operand, LowerError> {
        match op {
            Op::Gpr(g) => Ok(gw(*g, w)),
            Op::Mem(m) => Ok(self.mo(m, w)),
            _ => Err(self.bad(msg)),
        }
    }

    fn op_at(&self, op: &Op, w: W) -> Result<Operand, LowerError> {
        match op {
            Op::Imm(v) => Ok(io(*v)),
            Op::Gpr(g) => Ok(gw(*g, w)),
            Op::Fpr(x) => Ok(xo(*x)),
            Op::Mem(m) => Ok(self.mo(m, w)),
            Op::Sym(_) => Err(self.bad("symbolic immediates are offlineasm-only")),
            Op::Label(_) => {
                Err(self.bad("a label is only valid as a branch target or address source"))
            }
            Op::Extern(_) => Err(self.bad(EXTERN_MISUSE)),
        }
    }

    fn fp_src(&self, k: FKind, op: &Op) -> Result<Operand, LowerError> {
        match op {
            Op::Fpr(x) => Ok(xo(*x)),
            Op::Mem(m) => Ok(self.mo(m, fk_width(k))),
            _ => Err(self.bad("float operation needs a register or memory operand")),
        }
    }

    fn mov(&mut self, w: W, dst: &Op, src: &Op) -> Result<(), LowerError> {
        match (dst, src) {
            (Op::Gpr(d), Op::Gpr(s)) => {
                if d == s && w != W::B32 {
                    return Ok(());
                }
                self.x(InstId::Mov, &[gw(*d, w), gw(*s, w)]);
                Ok(())
            }
            (Op::Gpr(d), Op::Imm(v)) => {
                self.mov_imm(*d, w, *v);
                Ok(())
            }
            (Op::Gpr(d), Op::Mem(m)) => {
                self.x(InstId::Mov, &[gw(*d, w), self.mo(m, w)]);
                Ok(())
            }
            (Op::Gpr(d), Op::Label(l)) => {
                let m = label_mem(self.asm, self.res, *l);
                self.x(InstId::Lea, &[gw(*d, w), m]);
                Ok(())
            }
            (Op::Mem(m), _) => self.store(w, src, m),
            (Op::Gpr(_), Op::Fpr(_)) | (Op::Fpr(_), _) => Err(self.bad(
                "register-class moves use the bit-cast mnemonics (`fq2d`/`fd2q`/`fi2f`/`ff2i`)",
            )),
            _ => Err(self.bad("unsupported `mov` operand pair")),
        }
    }

    fn mov_imm(&mut self, d: Gpr, w: W, v: i64) {
        if w == W::B64 && !W::B32.fits(v) {
            self.x(InstId::Movabs, &[gw(d, w), io(v)]);
        } else {
            self.x(InstId::Mov, &[gw(d, w), io(truncate(v, w))]);
        }
    }

    fn store(&mut self, w: W, src: &Op, m: &Mem) -> Result<(), LowerError> {
        let addr = self.mo(m, w);
        match src {
            Op::Gpr(s) => self.x(InstId::Mov, &[addr, gw(*s, w)]),
            Op::Imm(v) if imm_encodable(w, *v) => self.x(InstId::Mov, &[addr, io(*v)]),
            Op::Imm(v) => {
                self.load_scratch_imm(*v);
                self.x(InstId::Mov, &[addr, gw(SCRATCH, w)]);
            }
            Op::Label(l) => {
                let lm = label_mem(self.asm, self.res, *l);
                self.x(InstId::Lea, &[gw(SCRATCH, W::B64), lm]);
                self.x(InstId::Mov, &[addr, gw(SCRATCH, w)]);
            }
            Op::Mem(s) => {
                self.x(InstId::Mov, &[gw(SCRATCH, w), self.mo(s, w)]);
                self.x(InstId::Mov, &[addr, gw(SCRATCH, w)]);
            }
            Op::Sym(_) => return Err(self.bad("symbolic immediates are offlineasm-only")),
            Op::Extern(_) => return Err(self.bad(EXTERN_MISUSE)),
            Op::Fpr(_) => return Err(self.bad("cannot store a float register as an integer")),
        }
        Ok(())
    }

    fn bswap(&mut self, w: W, dst: &Op, src: &Op) -> Result<(), LowerError> {
        let (Op::Gpr(d), Op::Gpr(s)) = (dst, src) else {
            return Err(self.bad("`bswap` needs general-purpose registers"));
        };
        if w != W::B32 && w != W::B64 {
            return Err(self.bad("`bswap` needs a 32- or 64-bit width"));
        }
        if d != s {
            self.x(InstId::Mov, &[gw(*d, w), gw(*s, w)]);
        }
        self.x(InstId::Bswap, &[gw(*d, w)]);
        Ok(())
    }

    fn load(&mut self, w: W, sx: Sx, dst: Gpr, addr: &Mem) {
        let extending = match (w, sx) {
            (W::B64, _) | (W::B32, Sx::Zero) => None,
            (W::B32, Sx::Sign) => Some((InstId::Movsxd, W::B64)),
            (W::B16, Sx::Zero) => Some((InstId::Movzx, W::B32)),
            (W::B16, Sx::Sign) => Some((InstId::Movsx, W::B64)),
            (W::B8, Sx::Zero) => Some((InstId::Movzx, W::B32)),
            (W::B8, Sx::Sign) => Some((InstId::Movsx, W::B64)),
        };
        let a = self.mo(addr, w);
        match extending {
            Some((id, to)) => self.x(id, &[gw(dst, to), a]),
            None => self.x(InstId::Mov, &[gw(dst, w), a]),
        }
    }

    fn lea(&mut self, w: W, dst: Gpr, src: &LeaSrc) -> Result<(), LowerError> {
        if w != W::B32 && w != W::B64 {
            return Err(self.bad("`lea` needs a 32- or 64-bit width"));
        }
        let m = match src {
            LeaSrc::Mem(m) => self.mo_at(m, 0, 0),
            LeaSrc::Label(l) => label_mem(self.asm, self.res, *l),
            // `lea d, [rip + sym]`.
            LeaSrc::Extern(e) if e.reach == Reach::Near => *sym_ptr(ext_sym(*e), 0, 0).as_operand(),
            // `mov d, qword ptr [rip + sym@GOTPCREL]`.
            LeaSrc::Extern(e) => {
                let slot = *sym_ptr(ext_sym(*e), 0, 8).as_operand();
                self.x(InstId::Mov, &[gw(dst, w), slot]);
                return Ok(());
            }
        };
        self.x(InstId::Lea, &[gw(dst, w), m]);
        Ok(())
    }

    fn push(&mut self, op: &Op) -> Result<(), LowerError> {
        match op {
            Op::Gpr(g) => self.x(InstId::Push, &[gw(*g, W::B64)]),
            Op::Mem(m) => self.x(InstId::Push, &[self.mo(m, W::B64)]),
            Op::Imm(v) if W::B32.fits(*v) => self.x(InstId::Push, &[io(*v)]),
            Op::Imm(v) => {
                self.load_scratch_imm(*v);
                self.x(InstId::Push, &[gw(SCRATCH, W::B64)]);
            }
            Op::Label(l) => {
                let lm = label_mem(self.asm, self.res, *l);
                self.x(InstId::Lea, &[gw(SCRATCH, W::B64), lm]);
                self.x(InstId::Push, &[gw(SCRATCH, W::B64)]);
            }
            Op::Sym(_) => return Err(self.bad("symbolic immediates are offlineasm-only")),
            Op::Extern(_) => return Err(self.bad(EXTERN_MISUSE)),
            Op::Fpr(_) => return Err(self.bad("cannot `push` a float register")),
        }
        Ok(())
    }

    fn pop(&mut self, op: &Op) -> Result<(), LowerError> {
        match op {
            Op::Gpr(g) => self.x(InstId::Pop, &[gw(*g, W::B64)]),
            Op::Mem(m) => self.x(InstId::Pop, &[self.mo(m, W::B64)]),
            _ => return Err(self.bad("`pop` needs a register or memory operand")),
        }
        Ok(())
    }

    fn bin2(&mut self, id: InstId, w: W, dst: &Op, src: &Op) -> Result<(), LowerError> {
        match (dst, src) {
            (Op::Gpr(d), Op::Gpr(s)) => self.x(id, &[gw(*d, w), gw(*s, w)]),
            (Op::Gpr(d), Op::Mem(m)) => self.x(id, &[gw(*d, w), self.mo(m, w)]),
            (Op::Gpr(d), Op::Imm(v)) => {
                if imm_encodable(w, *v) {
                    self.x(id, &[gw(*d, w), io(*v)]);
                } else {
                    self.load_scratch_imm(*v);
                    self.x(id, &[gw(*d, w), gw(SCRATCH, w)]);
                }
            }
            (Op::Mem(m), src) => {
                let addr = self.mo(m, w);
                let s = self.bin_source(w, src)?;
                self.x(id, &[addr, s]);
            }
            (Op::Gpr(_), Op::Sym(_)) => {
                return Err(self.bad("symbolic immediates are offlineasm-only"))
            }
            (Op::Imm(_), _) | (Op::Label(_), _) | (Op::Sym(_), _) | (Op::Fpr(_), _) => {
                return Err(self.bad("needs a register or memory destination"))
            }
            (Op::Gpr(_), Op::Fpr(_)) | (Op::Gpr(_), Op::Label(_)) => {
                return Err(self.bad("needs an integer source"))
            }
            (Op::Extern(_), _) | (_, Op::Extern(_)) => return Err(self.bad(EXTERN_MISUSE)),
        }
        Ok(())
    }

    fn bin_source(&mut self, w: W, src: &Op) -> Result<Operand, LowerError> {
        match src {
            Op::Gpr(g) => Ok(gw(*g, w)),
            Op::Imm(v) if imm_encodable(w, *v) => Ok(io(*v)),
            Op::Imm(v) => {
                self.load_scratch_imm(*v);
                Ok(gw(SCRATCH, w))
            }
            Op::Mem(m) => {
                self.x(InstId::Mov, &[gw(SCRATCH, w), self.mo(m, w)]);
                Ok(gw(SCRATCH, w))
            }
            Op::Sym(_) => Err(self.bad("symbolic immediates are offlineasm-only")),
            Op::Label(_) => Err(self.bad("cannot take a label as a source")),
            Op::Fpr(_) => Err(self.bad("needs an integer source")),
            Op::Extern(_) => Err(self.bad(EXTERN_MISUSE)),
        }
    }

    fn bin3(&mut self, op: Bin, w: W, alu: &Alu3) -> Result<(), LowerError> {
        let (dst, lhs, rhs) = (&alu.dst, &alu.lhs, &alu.rhs);
        if crate::ir::op_eq(lhs, dst) {
            if matches!(op, Bin::Add | Bin::Sub) && rhs.is_zero_imm() {
                return Ok(());
            }
            return self.bin2(op.id(), w, dst, rhs);
        }
        if op.commutative() && crate::ir::op_eq(rhs, dst) {
            return self.bin2(op.id(), w, dst, lhs);
        }
        if op == Bin::Sub && crate::ir::op_eq(rhs, dst) {
            self.unop(InstId::Neg, w, dst)?;
            return self.bin2(InstId::Add, w, dst, lhs);
        }
        if matches!(op, Bin::Add | Bin::Sub) && (lhs.is_zero_imm() || rhs.is_zero_imm()) {
            let other = if lhs.is_zero_imm() { rhs } else { lhs };
            return self.mov(w, dst, other);
        }
        self.mov(w, dst, lhs)?;
        self.bin2(op.id(), w, dst, rhs)
    }

    fn flag_bin3(&mut self, op: Bin, w: W, alu: &Alu3) -> Result<(), LowerError> {
        let (dst, lhs, rhs) = (&alu.dst, &alu.lhs, &alu.rhs);
        if crate::ir::op_eq(lhs, dst) {
            return self.bin2(op.id(), w, dst, rhs);
        }
        if op.commutative() && crate::ir::op_eq(rhs, dst) {
            return self.bin2(op.id(), w, dst, lhs);
        }
        if op == Bin::Sub && crate::ir::op_eq(rhs, dst) {
            if matches!(dst, Op::Gpr(_)) {
                self.mov(w, &Op::Gpr(SCRATCH), lhs)?;
                self.bin2(InstId::Sub, w, &Op::Gpr(SCRATCH), dst)?;
                return self.mov(w, dst, &Op::Gpr(SCRATCH));
            }
            self.unop(InstId::Neg, w, dst)?;
            return self.bin2(InstId::Add, w, dst, lhs);
        }
        self.mov(w, dst, lhs)?;
        self.bin2(op.id(), w, dst, rhs)
    }

    fn add3(&mut self, w: W, alu: &Alu3) -> Result<(), LowerError> {
        let (dst, lhs, rhs) = (&alu.dst, &alu.lhs, &alu.rhs);
        if crate::ir::op_eq(lhs, dst) {
            if rhs.is_zero_imm() {
                return Ok(());
            }
            return self.bin2(InstId::Add, w, dst, rhs);
        }
        if matches!(w, W::B32 | W::B64) {
            if let Op::Gpr(d) = dst {
                match (lhs, rhs) {
                    (Op::Gpr(a), Op::Gpr(b)) => {
                        let m = *sib(*a, *b, 0, 0, 0).as_operand();
                        self.x(InstId::Lea, &[gw(*d, w), m]);
                        return Ok(());
                    }
                    (Op::Gpr(a), Op::Imm(v)) | (Op::Imm(v), Op::Gpr(a)) => {
                        if *v == 0 {
                            self.x(InstId::Mov, &[gw(*d, w), gw(*a, w)]);
                            return Ok(());
                        }
                        if let Ok(disp) = i32::try_from(*v) {
                            let m = *ptr(&gx(*a), disp, 0).as_operand();
                            self.x(InstId::Lea, &[gw(*d, w), m]);
                            return Ok(());
                        }
                    }
                    _ => {}
                }
            }
        }
        self.bin3(Bin::Add, w, alu)
    }

    fn mul3(&mut self, w: W, alu: &Alu3) -> Result<(), LowerError> {
        let (dst, lhs, rhs) = (&alu.dst, &alu.lhs, &alu.rhs);
        if crate::ir::op_eq(lhs, dst) {
            return self.imul2(w, dst, rhs);
        }
        // Multiplication commutes: with `dst == rhs`, copying `lhs` into
        // `dst` first would clobber `rhs` and compute `lhs * lhs`.
        if crate::ir::op_eq(rhs, dst) {
            return self.imul2(w, dst, lhs);
        }
        if let Op::Imm(v) = rhs {
            if W::B32.fits(*v) {
                let d = self.mul_dst(w, dst)?;
                let l = match lhs {
                    Op::Gpr(g) => gw(*g, w),
                    Op::Mem(m) => self.mo(m, w),
                    _ => return Err(self.bad("`imul` needs a register or memory source here")),
                };
                self.x(InstId::Imul, &[d, l, io(*v)]);
                return Ok(());
            }
        }
        self.mov(w, dst, lhs)?;
        self.imul2(w, dst, rhs)
    }

    fn imul2(&mut self, w: W, dst: &Op, src: &Op) -> Result<(), LowerError> {
        if matches!(dst, Op::Mem(_)) {
            if matches!(src, Op::Imm(v) if !W::B32.fits(*v)) {
                return Err(self.bad("`imul` to memory needs a 32-bit immediate"));
            }
            let scratch = Op::Gpr(SCRATCH);
            self.mov(w, &scratch, dst)?;
            self.imul2(w, &scratch, src)?;
            return self.mov(w, dst, &scratch);
        }
        let d = self.mul_dst(w, dst)?;
        match src {
            Op::Gpr(g) => self.x(InstId::Imul, &[d, gw(*g, w)]),
            Op::Mem(m) => self.x(InstId::Imul, &[d, self.mo(m, w)]),
            Op::Imm(v) if W::B32.fits(*v) => self.x(InstId::Imul, &[d, d, io(*v)]),
            Op::Imm(v) => {
                self.load_scratch_imm(*v);
                self.x(InstId::Imul, &[d, gw(SCRATCH, w)]);
            }
            _ => return Err(self.bad("`imul` needs a register, memory, or immediate source")),
        }
        Ok(())
    }

    fn mul_dst(&self, w: W, dst: &Op) -> Result<Operand, LowerError> {
        if !matches!(w, W::B32 | W::B64) {
            return Err(self.bad("`imul` needs a 32- or 64-bit width"));
        }
        match dst {
            Op::Gpr(g) => Ok(gw(*g, w)),
            _ => Err(self.bad("`imul` needs a register destination")),
        }
    }

    fn mul_imm(&mut self, w: W, dst: Gpr, lhs: Gpr, v: i64) {
        if W::B32.fits(v) {
            self.x(InstId::Imul, &[gw(dst, w), gw(lhs, w), io(v)]);
            return;
        }
        self.load_scratch_imm(v);
        if dst != lhs {
            self.x(InstId::Mov, &[gw(dst, w), gw(lhs, w)]);
        }
        self.x(InstId::Imul, &[gw(dst, w), gw(SCRATCH, w)]);
    }

    fn unop(&mut self, id: InstId, w: W, dst: &Op) -> Result<(), LowerError> {
        match dst {
            Op::Gpr(g) => self.x(id, &[gw(*g, w)]),
            Op::Mem(m) => self.x(id, &[self.mo(m, w)]),
            _ => return Err(self.bad("needs a register or memory operand")),
        }
        Ok(())
    }

    fn shift(&mut self, w: W, op: ShiftOp, dst: Gpr, cnt: &ShiftCnt) -> Result<(), LowerError> {
        let id = match op {
            ShiftOp::Shl => InstId::Shl,
            ShiftOp::ShrSar => InstId::Sar,
            ShiftOp::Shr => InstId::Shr,
            ShiftOp::Rotl => InstId::Rol,
            ShiftOp::Rotr => InstId::Ror,
        };
        let d = gw(dst, w);
        match cnt {
            ShiftCnt::Imm(v) => {
                if !(-128..=255).contains(v) {
                    return Err(self.bad(format!("shift count {v} is out of range")));
                }
                self.x(id, &[d, io(*v)]);
            }
            ShiftCnt::Reg(g) => {
                let cl = gw(RCX, W::B8);
                if *g == RCX {
                    self.x(id, &[d, cl]);
                    return Ok(());
                }
                if dst == RCX {
                    return Err(self.bad("cannot shift the count register by another register"));
                }
                // The ISA takes the count from `cl`. The swap keeps the source
                // register intact.
                self.x(InstId::Xchg, &[gw(*g, W::B64), gw(RCX, W::B64)]);
                self.x(id, &[d, cl]);
                self.x(InstId::Xchg, &[gw(*g, W::B64), gw(RCX, W::B64)]);
            }
        }
        Ok(())
    }

    fn mul_wide(&mut self, signed: bool, dst: Gpr, lhs: Gpr, rhs: Gpr) {
        if signed {
            self.x(InstId::Movsxd, &[gw(SCRATCH, W::B64), gw(rhs, W::B32)]);
            self.x(InstId::Movsxd, &[gw(dst, W::B64), gw(lhs, W::B32)]);
        } else {
            self.x(InstId::Mov, &[gw(SCRATCH, W::B32), gw(rhs, W::B32)]);
            self.x(InstId::Mov, &[gw(dst, W::B32), gw(lhs, W::B32)]);
        }
        self.x(InstId::Imul, &[gw(dst, W::B64), gw(SCRATCH, W::B64)]);
    }

    fn mul_high(&mut self, signed: bool, rhs: &Op) -> Result<(), LowerError> {
        let src = self.rm(
            W::B64,
            rhs,
            "multiply-high needs a register or memory factor",
        )?;
        self.x(if signed { InstId::Imul } else { InstId::Mul }, &[src]);
        Ok(())
    }

    fn div_mod1(&mut self, signed: bool, w: W, divisor: &Op) -> Result<(), LowerError> {
        let src = match divisor {
            Op::Gpr(g) => gw(*g, w),
            Op::Mem(m) => self.mo(m, w),
            Op::Imm(v) => {
                self.load_scratch_imm(*v);
                gw(SCRATCH, w)
            }
            _ => return Err(self.bad("divide needs a register, memory, or immediate divisor")),
        };
        self.x(if signed { InstId::Idiv } else { InstId::Div }, &[src]);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn div3(
        &mut self,
        signed: bool,
        w: W,
        dst: Gpr,
        dvd: &Op,
        dvs: &Op,
        remainder: bool,
    ) -> Result<(), LowerError> {
        if w != W::B32 && w != W::B64 {
            return Err(self.bad("divide needs a 32- or 64-bit width"));
        }

        let acc = |g: &Gpr| *g == RAX || *g == RDX;
        let acc_mem =
            |m: &Mem| m.base.is_some_and(|g| acc(&g)) || matches!(m.index, Some((i, _)) if acc(&i));
        let sc = gw(SCRATCH, w);
        let divisor = match dvs {
            Op::Gpr(g) if acc(g) => {
                self.x(InstId::Mov, &[sc, gw(*g, w)]);
                sc
            }
            Op::Gpr(g) => gw(*g, w),
            Op::Mem(m) if acc_mem(m) => {
                self.x(InstId::Mov, &[sc, self.mo(m, w)]);
                sc
            }
            Op::Mem(m) => self.mo(m, w),
            Op::Imm(v) => {
                self.load_scratch_imm(*v);
                sc
            }
            _ => return Err(self.bad("divide needs a register, memory, or immediate divisor")),
        };
        let (ax64, dx64) = (gw(RAX, W::B64), gw(RDX, W::B64));
        let (axw, dxw) = (gw(RAX, w), gw(RDX, w));
        self.x(InstId::Push, &[ax64]);
        self.x(InstId::Push, &[dx64]);
        match dvd {
            Op::Gpr(g) => self.x(InstId::Mov, &[axw, gw(*g, w)]),
            Op::Mem(m) => self.x(InstId::Mov, &[axw, self.mo(m, w)]),
            Op::Imm(v) => {
                if w == W::B32 && !imm_encodable(w, *v) {
                    self.x(InstId::Movabs, &[ax64, io(*v)]);
                } else {
                    self.x(InstId::Mov, &[axw, io(*v)]);
                }
            }
            _ => {
                self.x(InstId::Pop, &[dx64]);
                self.x(InstId::Pop, &[ax64]);
                return Err(self.bad("divide needs a register, memory, or immediate dividend"));
            }
        }
        if signed {
            self.x(
                if w == W::B64 {
                    InstId::Cqo
                } else {
                    InstId::Cdq
                },
                &[],
            );
        } else {
            self.x(InstId::Xor, &[dxw, dxw]);
        }
        self.x(if signed { InstId::Idiv } else { InstId::Div }, &[divisor]);
        let half = if remainder { dxw } else { axw };
        if dst == RAX || dst == RDX {
            self.x(InstId::Mov, &[sc, half]);
            self.x(InstId::Pop, &[dx64]);
            self.x(InstId::Pop, &[ax64]);
            self.x(InstId::Mov, &[gw(dst, w), sc]);
            return Ok(());
        }
        self.x(InstId::Mov, &[gw(dst, w), half]);
        self.x(InstId::Pop, &[dx64]);
        self.x(InstId::Pop, &[ax64]);
        Ok(())
    }

    fn extend(&mut self, from: W, to: W, sx: Sx, dst: Gpr, src: &Op) -> Result<(), LowerError> {
        if from == W::B32 && to == W::B32 {
            return self.mov(W::B32, &Op::Gpr(dst), src);
        }
        let s = self.rm(
            from,
            src,
            "extending move needs a register or memory source",
        )?;
        let id = match (from, to, sx) {
            (W::B8 | W::B16, W::B32 | W::B64, Sx::Zero) => InstId::Movzx,
            (W::B8 | W::B16, W::B32 | W::B64, Sx::Sign) => InstId::Movsx,
            (W::B32, W::B64, Sx::Sign) => InstId::Movsxd,
            _ => {
                return Err(self.bad(format!(
                    "unsupported {} -> {} extension",
                    from.bytes() * 8,
                    to.bytes() * 8
                )))
            }
        };
        self.x(id, &[gw(dst, to), s]);
        Ok(())
    }

    fn count_zeros(&mut self, w: W, dst: Gpr, src: &Op, trailing: bool) -> Result<(), LowerError> {
        if w != W::B32 && w != W::B64 {
            return Err(self.bad("zero count needs a 32- or 64-bit width"));
        }
        let d = gw(dst, w);
        let s = self.rm(w, src, "zero count needs a register or memory source")?;
        self.x(if trailing { InstId::Bsf } else { InstId::Bsr }, &[d, s]);
        let nonzero = self.new_label();
        jcc(self.asm, Cond::NZ, nonzero);
        self.x(InstId::Mov, &[d, io(i64::from(w.bytes()) * 8)]);
        if trailing {
            self.bind(nonzero);
            return Ok(());
        }
        let done = self.new_label();
        self.jmp_label(done);
        self.bind(nonzero);
        self.x(InstId::Xor, &[d, io(if w == W::B64 { 0x3f } else { 0x1f })]);
        self.bind(done);
        Ok(())
    }

    fn add_shifted(&mut self, dst: Gpr, lhs: Gpr, rhs: Gpr, amount: u8) {
        let d = gw(dst, W::B64);
        if amount <= 3 {
            let m = *sib(lhs, rhs, u32::from(amount), 0, 0).as_operand();
            self.x(InstId::Lea, &[d, m]);
            return;
        }
        let s = gw(SCRATCH, W::B64);
        self.x(InstId::Mov, &[s, gw(rhs, W::B64)]);
        self.x(InstId::Shl, &[s, io(i64::from(amount))]);
        if dst == lhs {
            self.x(InstId::Add, &[d, s]);
        } else if dst == SCRATCH {
            self.x(InstId::Add, &[d, gw(lhs, W::B64)]);
        } else {
            self.x(InstId::Mov, &[d, gw(lhs, W::B64)]);
            self.x(InstId::Add, &[d, s]);
        }
    }

    fn cmov(&mut self, w: W, zero: bool, dst: Gpr, src: &Op, test: Gpr) -> Result<(), LowerError> {
        let t = gw(test, W::B64);
        self.x(InstId::Test, &[t, t]);
        let s = match src {
            Op::Gpr(g) => gw(*g, w),
            Op::Mem(m) => {
                self.x(InstId::Mov, &[gw(SCRATCH, w), self.mo(m, w)]);
                gw(SCRATCH, w)
            }
            Op::Imm(v) => {
                self.load_scratch_imm(*v);
                gw(SCRATCH, w)
            }
            _ => {
                return Err(
                    self.bad("conditional move needs a register, memory, or immediate source")
                )
            }
        };
        let id = if zero { InstId::Cmovz } else { InstId::Cmovnz };
        self.x(id, &[gw(dst, w), s]);
        Ok(())
    }

    fn int_compare(&mut self, cc: IntCc, w: W, lhs: &Op, rhs: &Op) -> Result<(), LowerError> {
        if matches!(cc, IntCc::Eq | IntCc::Ne) {
            for (value, other) in [(lhs, rhs), (rhs, lhs)] {
                if value.is_zero_imm() {
                    if let Op::Gpr(g) = other {
                        self.x(InstId::Test, &[gw(*g, w), gw(*g, w)]);
                        return Ok(());
                    }
                }
            }
        }
        let mut scratch = false;
        let l = match lhs {
            Op::Imm(_) if matches!(rhs, Op::Imm(_)) => {
                return Err(self.bad("compare needs at least one register operand"))
            }
            Op::Imm(v) => {
                if imm_encodable(w, *v) {
                    self.x(InstId::Mov, &[gw(SCRATCH, w), io(*v)]);
                } else {
                    self.load_scratch_imm(*v);
                }
                scratch = true;
                gw(SCRATCH, w)
            }
            Op::Mem(m) if matches!(rhs, Op::Imm(_) | Op::Mem(_)) => {
                self.x(InstId::Mov, &[gw(SCRATCH, w), self.mo(m, w)]);
                scratch = true;
                gw(SCRATCH, w)
            }
            _ => self.op_at(lhs, w)?,
        };
        let r = match rhs {
            Op::Imm(v) if imm_encodable(w, *v) => io(*v),
            Op::Imm(v) => {
                if scratch {
                    return Err(self.bad("compare needs both immediates to be encodable"));
                }
                self.load_scratch_imm(*v);
                gw(SCRATCH, w)
            }
            _ => self.op_at(rhs, w)?,
        };
        self.x(InstId::Cmp, &[l, r]);
        Ok(())
    }

    fn test_flags(&mut self, w: W, value: &Op, mask: Option<&Op>) -> Result<(), LowerError> {
        if matches!(mask, None | Some(Op::Imm(-1))) {
            match value {
                Op::Gpr(g) => self.x(InstId::Test, &[gw(*g, w), gw(*g, w)]),
                Op::Mem(m) => self.x(InstId::Cmp, &[self.mo(m, w), io(0)]),
                _ => return Err(self.bad("test needs a register or memory value")),
            }
            return Ok(());
        }
        let mask = mask.ok_or_else(|| self.bad("test is missing its mask operand"))?;
        match (mask, value) {
            (Op::Imm(v), Op::Gpr(g)) => {
                if !imm_encodable(w, *v) {
                    return Err(self.bad("test mask is out of range for this width"));
                }
                self.x(InstId::Test, &[gw(*g, w), io(*v)]);
            }
            (Op::Imm(v), Op::Mem(m)) => {
                if !imm_encodable(w, *v) {
                    return Err(self.bad("test mask is out of range for this width"));
                }
                self.x(InstId::Test, &[self.mo(m, w), io(*v)]);
            }
            (Op::Gpr(m), Op::Gpr(v)) => self.x(InstId::Test, &[gw(*v, w), gw(*m, w)]),
            _ => return Err(self.bad("unsupported test operands")),
        }
        Ok(())
    }

    fn set_zx(&mut self, cc: Cond, dst: &Op) -> Result<(), LowerError> {
        match dst {
            Op::Gpr(g) => {
                self.x(cc.setcc(), &[gw(*g, W::B8)]);
                self.x(InstId::Movzx, &[gw(*g, W::B32), gw(*g, W::B8)]);
            }
            Op::Mem(m) => self.x(cc.setcc(), &[self.mo(m, W::B8)]),
            _ => return Err(self.bad("`set*` needs a register or memory destination")),
        }
        Ok(())
    }

    fn op_branch(
        &mut self,
        op: FlagAlu,
        w: W,
        flag: PredFlag,
        args: &[Op],
    ) -> Result<(), LowerError> {
        self.op_branch_alu(op, w, args)?;
        if op == FlagAlu::Mul && flag != PredFlag::O {
            let d = match args.last() {
                Some(Op::Gpr(d)) => *d,
                _ => SCRATCH,
            };
            self.x(InstId::Test, &[gw(d, w), gw(d, w)]);
        }
        Ok(())
    }

    fn op_branch_alu(&mut self, op: FlagAlu, w: W, args: &[Op]) -> Result<(), LowerError> {
        if op == FlagAlu::Sub
            && args.len() == 3
            && crate::ir::op_eq(&args[1], &args[2])
            && !crate::ir::op_eq(&args[0], &args[2])
        {
            let scratch = Op::Gpr(SCRATCH);
            self.mov(w, &scratch, &args[0])?;
            self.bin2(InstId::Sub, w, &scratch, &args[2])?;
            return self.mov(w, &args[2], &scratch);
        }
        let (dst, src) = match args {
            [src, dst] => (dst, src),
            [lhs, rhs, dst] if crate::ir::op_eq(lhs, dst) => (dst, rhs),
            [lhs, rhs, dst] if crate::ir::op_eq(rhs, dst) => (dst, lhs),
            [lhs, rhs, dst] => {
                self.mov(w, dst, lhs)?;
                (dst, rhs)
            }
            _ => {
                return Err(self.bad(format!(
                    "op-branch expects 2 or 3 leading operands, got {}",
                    args.len()
                )))
            }
        };
        match op {
            FlagAlu::Add => self.bin2(InstId::Add, w, dst, src),
            FlagAlu::Sub => self.bin2(InstId::Sub, w, dst, src),
            FlagAlu::Mul => self.imul2(w, dst, src),
            FlagAlu::Or => self.bin2(InstId::Or, w, dst, src),
        }
    }

    fn jump(
        &mut self,
        target: &IrTarget,
        patch: bool,
        is_call: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        let id = if is_call { InstId::Call } else { InstId::Jmp };
        if patch && !matches!(target, IrTarget::Label(_)) {
            return Err(LowerError::NotPatchable(self.mn.to_string()));
        }
        match target {
            IrTarget::Label(l) => {
                let t = self.res.resolve(*l, || self.asm.get_label());
                if patch {
                    let h: PatchableJump = if is_call {
                        self.asm.patchable_call(t)
                    } else {
                        self.asm.patchable_jmp(t)
                    };
                    return Ok(Some(PatchHandle::Jump(h)));
                }
                self.x(id, &[*t.as_operand()]);
            }
            IrTarget::Reg(g) => self.x(id, &[gw(*g, W::B64)]),
            IrTarget::Mem(m) => self.x(id, &[self.mo(m, W::B64)]),
            IrTarget::Abs(v) => {
                self.load_scratch_imm(*v);
                self.x(id, &[gw(SCRATCH, W::B64)]);
            }
            // `call sym` (rel32).
            IrTarget::Extern(e) if e.reach == Reach::Near => {
                self.x(id, &[*ext_sym(*e).as_operand()]);
            }
            // `call qword ptr [rip + sym@GOTPCREL]`.
            IrTarget::Extern(e) => self.x(id, &[*sym_ptr(ext_sym(*e), 0, 8).as_operand()]),
        }
        Ok(None)
    }

    fn farith(&mut self, op: FAlu, k: FKind, arith: &FArith3) -> Result<(), LowerError> {
        let dst = arith.dst;
        let Some(rhs) = &arith.rhs else {
            return self.fp_fold(op, k, dst, &arith.lhs);
        };
        let lhs = &arith.lhs;
        let vectorizable = matches!(op, FAlu::Add | FAlu::Sub | FAlu::Mul | FAlu::Div);
        if vectorizable && self.asm.environment().avx() {
            if let Op::Fpr(l) = lhs {
                let r = self.fp_src(k, rhs)?;
                self.x(vex_farith_id(op, k), &[xo(dst), xo(*l), r]);
                return Ok(());
            }
        }
        if matches!(lhs, Op::Fpr(l) if *l == dst) {
            return self.fp_fold(op, k, dst, rhs);
        }
        if matches!(rhs, Op::Fpr(r) if *r == dst) {
            if op.is_commutative() {
                return self.fp_fold(op, k, dst, lhs);
            }

            self.fp_stage(k, FSCRATCH, lhs)?;
            self.fp_fold(op, k, FSCRATCH, &Op::Fpr(dst))?;
            self.x(fk_mov(k), &[xo(dst), xo(FSCRATCH)]);
            return Ok(());
        }
        self.fp_stage(k, dst, lhs)?;
        self.fp_fold(op, k, dst, rhs)
    }

    fn fp_fold(&mut self, op: FAlu, k: FKind, dst: Fpr, src: &Op) -> Result<(), LowerError> {
        let s = self.fp_src(k, src)?;
        self.x(farith_id(op, k), &[xo(dst), s]);
        Ok(())
    }

    fn fp_stage(&mut self, k: FKind, dst: Fpr, src: &Op) -> Result<(), LowerError> {
        let s = self.fp_src(k, src)?;
        self.x(fk_mov(k), &[xo(dst), s]);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn fma(
        &mut self,
        op: FmaOp,
        k: FKind,
        a: &Op,
        b: &Op,
        c: &Op,
        dst: Fpr,
    ) -> Result<(), LowerError> {
        if !self.asm.environment().avx() {
            return Err(self.bad(
                "fused multiply-add requires the AVX/FMA3 CPU features (guard the call with \
                 `if HAS_AVX`)",
            ));
        }
        let id = match (op, k) {
            (FmaOp::Add, FKind::F32) => InstId::Vfmadd213ss,
            (FmaOp::Add, FKind::F64) => InstId::Vfmadd213sd,
            (FmaOp::Sub, FKind::F32) => InstId::Vfmsub213ss,
            (FmaOp::Sub, FKind::F64) => InstId::Vfmsub213sd,
            (FmaOp::NegAdd, FKind::F32) => InstId::Vfnmadd213ss,
            (FmaOp::NegAdd, FKind::F64) => InstId::Vfnmadd213sd,
            (FmaOp::NegSub, FKind::F32) => InstId::Vfnmsub213ss,
            (FmaOp::NegSub, FKind::F64) => InstId::Vfnmsub213sd,
        };
        self.fp_stage(k, FSCRATCH, a)?;
        let (b, c) = (self.fp_src(k, b)?, self.fp_src(k, c)?);
        self.x(id, &[xo(FSCRATCH), b, c]);
        self.x(fk_mov(k), &[xo(dst), xo(FSCRATCH)]);
        Ok(())
    }

    fn fp_sign(&mut self, k: FKind, dst: Fpr, src: &Op, negate: bool) -> Result<(), LowerError> {
        let aliased = matches!(src, Op::Fpr(x) if *x == dst);
        if aliased {
            self.x(fk_mov(k), &[xo(FSCRATCH), xo(dst)]);
        }
        let (mask, id) = match (k, negate) {
            (FKind::F64, false) => (0x8000_0000_0000_0000u64 as i64, InstId::Andnps),
            (FKind::F64, true) => (0x8000_0000_0000_0000u64 as i64, InstId::Xorpd),
            (FKind::F32, false) => (0x8000_0000i64, InstId::Andnps),
            (FKind::F32, true) => (0x8000_0000i64, InstId::Xorps),
        };
        self.load_scratch_imm(mask);
        let mv = match k {
            FKind::F32 => InstId::Movd,
            FKind::F64 => InstId::Movq,
        };
        self.x(mv, &[xo(dst), gw(SCRATCH, fk_width(k))]);
        let s = match src {
            Op::Fpr(_) if aliased => xo(FSCRATCH),
            Op::Fpr(x) => xo(*x),
            Op::Mem(m) => {
                self.x(fk_mov(k), &[xo(FSCRATCH), self.mo(m, fk_width(k))]);
                xo(FSCRATCH)
            }
            _ => return Err(self.bad("`abs`/`neg` needs a register or memory source")),
        };
        self.x(id, &[xo(dst), s]);
        Ok(())
    }

    fn bitcast(&mut self, dir: BitcastDir, dst: &Op, src: &Op) -> Result<(), LowerError> {
        let (id, w) = match dir {
            BitcastDir::Q2D | BitcastDir::D2Q => (InstId::Movq, W::B64),
            BitcastDir::I2F | BitcastDir::F2I => (InstId::Movd, W::B32),
        };
        let to_fpr = matches!(dir, BitcastDir::Q2D | BitcastDir::I2F);
        let ops = match (to_fpr, dst, src) {
            (true, Op::Fpr(d), Op::Gpr(s)) => [xo(*d), gw(*s, w)],
            (true, Op::Fpr(d), Op::Mem(m)) => [xo(*d), self.mo(m, w)],
            (false, Op::Gpr(d), Op::Fpr(s)) => [gw(*d, w), xo(*s)],
            (false, Op::Mem(m), Op::Fpr(s)) => [self.mo(m, w), xo(*s)],
            _ => {
                return Err(self.bad(match dir {
                    BitcastDir::Q2D => {
                        "`fq2d` needs a quad or memory source and an FPR destination"
                    }
                    BitcastDir::D2Q => {
                        "`fd2q` needs an FPR source and a quad or memory destination"
                    }
                    BitcastDir::I2F => {
                        "`fi2f` needs an int or memory source and an FPR destination"
                    }
                    BitcastDir::F2I => {
                        "`ff2i` needs an FPR source and an int or memory destination"
                    }
                }))
            }
        };
        self.x(id, &ops);
        Ok(())
    }

    fn fp_ucomi(&mut self, k: FKind, lhs: &Op, rhs: &Op) -> Result<(), LowerError> {
        let l = match lhs {
            Op::Fpr(x) => xo(*x),
            Op::Mem(m) => {
                self.x(fk_mov(k), &[xo(FSCRATCH), self.mo(m, fk_width(k))]);
                xo(FSCRATCH)
            }
            _ => return Err(self.bad("float compare needs a register or memory left side")),
        };
        let r = match rhs {
            Op::Fpr(x) => xo(*x),
            Op::Mem(m) => self.mo(m, fk_width(k)),
            _ => return Err(self.bad("float compare needs a register or memory right side")),
        };
        let id = match k {
            FKind::F32 => InstId::Ucomiss,
            FKind::F64 => InstId::Ucomisd,
        };
        self.x(id, &[l, r]);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn branch_f(
        &mut self,
        cc: FCc,
        k: FKind,
        lhs: &Op,
        rhs: &Op,
        target: Lbl,
        patch: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        let one = match cc {
            FCc::Eq | FCc::NeUn => None,
            FCc::Ne => Some(Cond::NZ),
            FCc::Gt | FCc::Lt => Some(Cond::A),
            FCc::Ge | FCc::Le => Some(Cond::NB),
            FCc::EqUn => Some(Cond::Z),
            FCc::GtUn | FCc::LtUn => Some(Cond::B),
            FCc::GeUn | FCc::LeUn => Some(Cond::BE),
        };
        if let Some(c) = one {
            self.fp_ucomi(k, lhs, rhs)?;
            return Ok(branch_to(self.asm, self.res, c, target, patch));
        }
        if patch {
            return Err(LowerError::NotPatchable(self.mn.to_string()));
        }
        self.fp_ucomi(k, lhs, rhs)?;
        if cc == FCc::Eq {
            let unordered = self.new_label();
            jcc(self.asm, Cond::P, unordered);
            branch_to(self.asm, self.res, Cond::Z, target, false);
            self.bind(unordered);
        } else {
            branch_to(self.asm, self.res, Cond::P, target, false);
            branch_to(self.asm, self.res, Cond::NZ, target, false);
        }
        Ok(None)
    }

    fn fset(&mut self, cc: FCc, k: FKind, dst: &Op, lhs: &Op, rhs: &Op) -> Result<(), LowerError> {
        match cc {
            FCc::Eq | FCc::NeUn => {
                let eq = cc == FCc::Eq;
                if crate::ir::op_eq(lhs, rhs) {
                    self.fp_ucomi(k, rhs, lhs)?;
                    return self.set_zx(if eq { Cond::NP } else { Cond::P }, dst);
                }
                let Op::Gpr(d) = dst else {
                    return Err(self.bad("`cf*`/`cd*` need a register destination"));
                };
                self.x(InstId::Mov, &[gw(*d, W::B64), io(if eq { 0 } else { 1 })]);
                self.fp_ucomi(k, rhs, lhs)?;
                let unordered = self.new_label();
                jcc(self.asm, Cond::P, unordered);
                self.set_zx(if eq { Cond::Z } else { Cond::NZ }, dst)?;
                self.bind(unordered);
                Ok(())
            }
            FCc::Ne => self.set_cc(k, Cond::NZ, lhs, rhs, dst, false),
            FCc::Gt => self.set_cc(k, Cond::A, lhs, rhs, dst, false),
            FCc::Ge => self.set_cc(k, Cond::NB, lhs, rhs, dst, false),
            FCc::Lt => self.set_cc(k, Cond::A, lhs, rhs, dst, true),
            FCc::Le => self.set_cc(k, Cond::NB, lhs, rhs, dst, true),
            FCc::EqUn | FCc::GtUn | FCc::GeUn | FCc::LtUn | FCc::LeUn => {
                Err(self.bad("unordered float set is only defined for eq/nequn"))
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn set_cc(
        &mut self,
        k: FKind,
        cc: Cond,
        lhs: &Op,
        rhs: &Op,
        dst: &Op,
        reverse: bool,
    ) -> Result<(), LowerError> {
        if reverse {
            self.fp_ucomi(k, rhs, lhs)?;
        } else {
            self.fp_ucomi(k, lhs, rhs)?;
        }
        self.set_zx(cc, dst)
    }

    fn tls(
        &mut self,
        w: W,
        reg: Gpr,
        idx: i64,
        load: bool,
        abi: crate::Abi,
    ) -> Result<(), LowerError> {
        let off = tls_offset(self.mn, idx)?;
        let m = tls_mem(off, w.bytes(), abi);
        if load {
            self.x(InstId::Mov, &[gw(reg, w), m]);
            self.zero_extend_result(reg, w);
        } else {
            self.x(InstId::Mov, &[m, gw(reg, w)]);
        }
        Ok(())
    }

    fn rmw_operands<'o>(&self, a: &'o Op, b: &'o Op) -> Result<(Gpr, &'o Mem), LowerError> {
        match (a, b) {
            (Op::Gpr(g), Op::Mem(m)) | (Op::Mem(m), Op::Gpr(g)) => Ok((*g, m)),
            _ => Err(self.bad("needs a register and a memory operand")),
        }
    }

    /// Atomic read-modify-write / exchange.
    fn atomic_rmw(&mut self, op: AtomicOp, w: W, a: &Op, b: &Op) -> Result<(), LowerError> {
        match op {
            AtomicOp::Add | AtomicOp::Sub => {
                let (reg, mem) = self.rmw_operands(a, b)?;
                if op == AtomicOp::Sub {
                    self.x(InstId::Neg, &[gw(reg, w)]);
                }
                e_lock(self.asm, InstId::Xadd, &[self.mo(mem, w), gw(reg, w)]);
                self.zero_extend_result(reg, w);
            }
            AtomicOp::Xchg => {
                let (reg, mem) = self.rmw_operands(a, b)?;
                self.x(InstId::Xchg, &[self.mo(mem, w), gw(reg, w)]);
                self.zero_extend_result(reg, w);
            }
            AtomicOp::And | AtomicOp::Or | AtomicOp::Xor => self.atomic_logic(op, w, a, b)?,
        }
        Ok(())
    }

    fn atomic_logic(&mut self, op: AtomicOp, w: W, a: &Op, b: &Op) -> Result<(), LowerError> {
        let (reg, mem) = self.rmw_operands(a, b)?;
        let (ax, d, s) = (gw(RAX, w), gw(reg, w), gw(SCRATCH, w));
        let m = self.mo(mem, w);
        let id = match op {
            AtomicOp::And => InstId::And,
            AtomicOp::Or => InstId::Or,
            _ => InstId::Xor,
        };
        let retry = self.new_label();
        if reg == RAX {
            self.x(InstId::Push, &[gw(reg, W::B64)]);
            self.bind(retry);
            self.x(InstId::Mov, &[ax, m]);
            self.x(InstId::Mov, &[s, ax]);
            self.x(id, &[s, rsp_mem(0, w.bytes())]);
            e_lock(self.asm, InstId::Cmpxchg, &[m, s]);
            jcc(self.asm, Cond::NZ, retry);
            self.x(InstId::Add, &[gw(RSP, W::B64), io(8)]);
            self.zero_extend_result(reg, w);
            return Ok(());
        }
        self.x(InstId::Push, &[gw(RAX, W::B64)]);
        self.bind(retry);
        self.x(InstId::Mov, &[ax, m]);
        if reg == SCRATCH {
            self.x(id, &[d, ax]);
        } else {
            self.x(InstId::Mov, &[s, ax]);
            self.x(id, &[s, d]);
        }
        e_lock(self.asm, InstId::Cmpxchg, &[m, s]);
        jcc(self.asm, Cond::NZ, retry);
        self.x(InstId::Mov, &[d, ax]);
        self.zero_extend_result(reg, w);
        self.x(InstId::Pop, &[gw(RAX, W::B64)]);
        Ok(())
    }

    fn zero_extend_result(&mut self, dst: Gpr, w: W) {
        if matches!(w, W::B8 | W::B16) {
            self.x(InstId::Movzx, &[gw(dst, W::B32), gw(dst, w)]);
        }
    }

    fn pair(
        &mut self,
        w: PairW,
        first: &Op,
        second: &Op,
        mem: &Mem,
        load: bool,
    ) -> Result<(), LowerError> {
        let gpr = |op: &Op| match op {
            Op::Gpr(g) => Ok(*g),
            _ => Err(bad(self.mn, "paired access needs register operands")),
        };
        let fpr = |op: &Op| match op {
            Op::Fpr(x) => Ok(*x),
            _ => Err(bad(self.mn, "paired access needs register operands")),
        };
        match (w, load) {
            (PairW::B64 | PairW::B32, true) => {
                let dw = if w == PairW::B64 { W::B64 } else { W::B32 };
                let (g1, g2) = (gpr(first)?, gpr(second)?);
                let (d1, d2) = (gw(g1, dw), gw(g2, dw));
                let (m1, m2) = (
                    self.mo(mem, dw),
                    self.mo_at(mem, dw.bytes(), i64::from(dw.bytes())),
                );
                let clobbers =
                    |g: Gpr| mem.base == Some(g) || mem.index.is_some_and(|(idx, _)| idx == g);
                if clobbers(g1) && (g1 == g2 || clobbers(g2)) {
                    let t = gw(SCRATCH, dw);
                    self.x(InstId::Mov, &[t, m2]);
                    self.x(InstId::Mov, &[d1, m1]);
                    self.x(InstId::Mov, &[d2, t]);
                } else if clobbers(g1) {
                    self.x(InstId::Mov, &[d2, m2]);
                    self.x(InstId::Mov, &[d1, m1]);
                } else {
                    self.x(InstId::Mov, &[d1, m1]);
                    self.x(InstId::Mov, &[d2, m2]);
                }
            }
            (PairW::B64 | PairW::B32, false) => {
                let dw = if w == PairW::B64 { W::B64 } else { W::B32 };
                let (s1, s2) = (gw(gpr(first)?, dw), gw(gpr(second)?, dw));
                let (m1, m2) = (
                    self.mo(mem, dw),
                    self.mo_at(mem, dw.bytes(), i64::from(dw.bytes())),
                );
                self.x(InstId::Mov, &[m1, s1]);
                self.x(InstId::Mov, &[m2, s2]);
            }
            (PairW::F64, true) => {
                let (d1, d2) = (xo(fpr(first)?), xo(fpr(second)?));
                self.x(InstId::Movsd, &[d1, self.mo_at(mem, 8, 0)]);
                self.x(InstId::Movsd, &[d2, self.mo_at(mem, 8, 8)]);
            }
            (PairW::F64, false) => {
                let (s1, s2) = (xo(fpr(first)?), xo(fpr(second)?));
                self.x(InstId::Movsd, &[self.mo_at(mem, 8, 0), s1]);
                self.x(InstId::Movsd, &[self.mo_at(mem, 8, 8), s2]);
            }
            (PairW::V128, true) => {
                let (d1, d2) = (xo(fpr(first)?), xo(fpr(second)?));
                self.x(InstId::Movdqu, &[d1, self.mo_at(mem, 16, 0)]);
                self.x(InstId::Movdqu, &[d2, self.mo_at(mem, 16, 16)]);
            }
            (PairW::V128, false) => {
                let (s1, s2) = (xo(fpr(first)?), xo(fpr(second)?));
                self.x(InstId::Movups, &[self.mo_at(mem, 16, 0), s1]);
                self.x(InstId::Movups, &[self.mo_at(mem, 16, 16), s2]);
            }
        }
        Ok(())
    }
}

fn farith_id(op: FAlu, k: FKind) -> InstId {
    match (op, k) {
        (FAlu::Add, FKind::F32) => InstId::Addss,
        (FAlu::Add, FKind::F64) => InstId::Addsd,
        (FAlu::Sub, FKind::F32) => InstId::Subss,
        (FAlu::Sub, FKind::F64) => InstId::Subsd,
        (FAlu::Mul, FKind::F32) => InstId::Mulss,
        (FAlu::Mul, FKind::F64) => InstId::Mulsd,
        (FAlu::Div, FKind::F32) => InstId::Divss,
        (FAlu::Div, FKind::F64) => InstId::Divsd,
        (FAlu::Min, FKind::F32) => InstId::Minss,
        (FAlu::Min, FKind::F64) => InstId::Minsd,
        (FAlu::Max, FKind::F32) => InstId::Maxss,
        (FAlu::Max, FKind::F64) => InstId::Maxsd,
    }
}

fn vex_farith_id(op: FAlu, k: FKind) -> InstId {
    match (op, k) {
        (FAlu::Add, FKind::F32) => InstId::Vaddss,
        (FAlu::Add, FKind::F64) => InstId::Vaddsd,
        (FAlu::Sub, FKind::F32) => InstId::Vsubss,
        (FAlu::Sub, FKind::F64) => InstId::Vsubsd,
        (FAlu::Mul, FKind::F32) => InstId::Vmulss,
        (FAlu::Mul, FKind::F64) => InstId::Vmulsd,
        (FAlu::Div, FKind::F32) => InstId::Vdivss,
        (FAlu::Div, FKind::F64) => InstId::Vdivsd,
        (FAlu::Min | FAlu::Max, _) => unreachable!("min/max have no three-operand VEX form"),
    }
}
