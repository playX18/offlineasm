//! RISC-V 64 lowering.

use crate::ir::{
    expand, Alu3, AluOp, AtomicOp, BitcastDir, FAlu, FArith3, FCc, FKind, FlagAlu, FmaOp, Fpr,
};
use crate::ir::{
    Disp, Gpr, Inst, IntCc, LabelResolver, Lbl, LeaSrc, LowerError, Mem, Mnemonic, Op, PairW,
};
use crate::ir::{Extern, Reach, Target as IrTarget, Width};
use crate::ir::{PatchHandle, PredFlag, RoundMode, Scratch, ShiftCnt, ShiftOp, Sx, TestKind};
use asmkit::riscv::*;
use asmkit::{imm, Label, Operand, OperandCast, Reloc, RelocTarget, Sym};

const SCRATCH: Scratch = offlineasm_ir::regs::RISCV64.scratch;
/// First expansion scratch (`x31`).
const G1: Gpr = SCRATCH.gpr;
/// Second expansion scratch (`x29`).
const G2: Gpr = SCRATCH.gpr2;
/// FP scratch (`f31`).
const SF: Fpr = SCRATCH.fpr;
/// The flags register (`x30`).
const FLAGS: Gpr = Gpr(30);
const X0: Gpr = Gpr(0);
const RA: Gpr = Gpr(1);
const SP: Gpr = Gpr(2);
/// The thread pointer (`x4` / `tp`).
const TP: Gpr = Gpr(4);
/// The `t0` accumulator role (`a0` = `x10`).
const T0: Gpr = Gpr(10);
/// The `t2` accumulator role (`a2` = `x12`).
const T2: Gpr = Gpr(12);

/// Dynamic rounding mode (`dyn`).
const DYN: i64 = 7;
/// Round toward zero (`rtz`).
const RTZ: i64 = 1;

fn bad(mn: Mnemonic, msg: impl Into<String>) -> LowerError {
    LowerError::BadOperand {
        mnemonic: mn.to_string(),
        msg: msg.into(),
    }
}

fn x(g: Gpr) -> Gp {
    assert!(g.0 <= 31, "onlineasm: riscv64 GPR id {} out of range", g.0);
    Gp::from_id(u32::from(g.0))
}

fn fl(f: Fpr) -> Fp {
    assert!(f.0 <= 31, "onlineasm: riscv64 FPR id {} out of range", f.0);
    Fp::from_id(u32::from(f.0))
}

pub fn gpr_id(g: Gp) -> Gpr {
    Gpr(g.id() as u8)
}

pub fn fpr_id(v: Fp) -> Fpr {
    Fpr(v.id() as u8)
}

fn g(r: Gpr) -> Operand {
    *x(r).as_operand()
}

fn f(r: Fpr) -> Operand {
    *fl(r).as_operand()
}

fn i(v: i64) -> Operand {
    *imm(v).as_operand()
}

fn fhi(mn: Mnemonic, r: Fpr) -> Result<Fpr, LowerError> {
    if r.0 > 30 {
        return Err(bad(mn, format!("fpr{} has no pair high half", r.0)));
    }
    Ok(Fpr(r.0 + 1))
}

fn fits12(v: i64) -> bool {
    (-2048..2048).contains(&v)
}

fn fits_d12(disp: i32) -> bool {
    (-2048..2048).contains(&disp)
}

fn lane_bits(w: Width) -> u32 {
    match w {
        Width::B8 => 8,
        Width::B16 => 16,
        Width::B32 => 32,
        Width::B64 => 64,
    }
}

fn lane_mask(w: Width) -> i64 {
    match w {
        Width::B8 => 0xFF,
        Width::B16 => 0xFFFF,
        Width::B32 => 0xFFFF_FFFF,
        Width::B64 => 0,
    }
}

fn load_op(w: Width, sx: Sx) -> Opcode {
    match (w, sx) {
        (Width::B8, Sx::Zero) => Opcode::LBU,
        (Width::B8, Sx::Sign) => Opcode::LB,
        (Width::B16, Sx::Zero) => Opcode::LHU,
        (Width::B16, Sx::Sign) => Opcode::LH,
        (Width::B32, Sx::Zero) => Opcode::LWU,
        (Width::B32, Sx::Sign) => Opcode::LW,
        (Width::B64, _) => Opcode::LD,
    }
}

fn store_op(w: Width) -> Opcode {
    match w {
        Width::B8 => Opcode::SB,
        Width::B16 => Opcode::SH,
        Width::B32 => Opcode::SW,
        Width::B64 => Opcode::SD,
    }
}

fn fsel(k: FKind, s: Opcode, d: Opcode) -> Opcode {
    match k {
        FKind::F32 => s,
        FKind::F64 => d,
    }
}

/// The `w` form of a shift when `w` is `B32`.
fn wsel(w: Width, full: Opcode, word: Opcode) -> Opcode {
    if w == Width::B32 {
        word
    } else {
        full
    }
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
    fn op(self) -> Opcode {
        match self {
            AluKind::Add => Opcode::ADD,
            AluKind::Sub => Opcode::SUB,
            AluKind::Mul => Opcode::MUL,
            AluKind::And => Opcode::AND,
            AluKind::Or => Opcode::OR,
            AluKind::Xor => Opcode::XOR,
        }
    }

    fn imm_op(self) -> Opcode {
        match self {
            AluKind::Add | AluKind::Sub | AluKind::Mul => Opcode::ADDI,
            AluKind::And => Opcode::ANDI,
            AluKind::Or => Opcode::ORI,
            AluKind::Xor => Opcode::XORI,
        }
    }
}

fn alu_args(alu: &Alu3) -> Vec<Op> {
    if crate::ir::op_eq(&alu.lhs, &alu.dst) {
        vec![alu.rhs, alu.dst]
    } else {
        vec![alu.lhs, alu.rhs, alu.dst]
    }
}

/// Flip an integer condition (for canonicalizing `imm OP x`).
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

impl crate::IntoOperand for Gp {
    fn into_operand(self, _asm: &crate::Assembler) -> Op {
        Op::Gpr(gpr_id(self))
    }
}

impl crate::IntoOperand for Fp {
    fn into_operand(self, _asm: &crate::Assembler) -> Op {
        Op::Fpr(fpr_id(self))
    }
}

use crate::TargetInfo;
use asmkit::CodeBuffer;

pub(crate) fn lower(
    buf: &mut CodeBuffer,
    ctx: &Scratch,
    labels: &[asmkit::Label],
    mnemonic: Mnemonic,
    ops: &[Op],
    abi: crate::Abi,
) -> Result<(), LowerError> {
    let _ = abi;
    let mut asm = asmkit::riscv::Assembler::new(buf);
    let mut res = LabelResolver::new(labels);
    lower_ops(&mut asm, ctx, mnemonic, ops, &mut res)
}

pub(crate) fn lower_patched(
    buf: &mut CodeBuffer,
    ctx: &Scratch,
    labels: &[asmkit::Label],
    mnemonic: Mnemonic,
    ops: &[Op],
    abi: crate::Abi,
) -> Result<PatchHandle, LowerError> {
    let _ = abi;
    let mut asm = asmkit::riscv::Assembler::new(buf);
    let mut res = LabelResolver::new(labels);
    lower_ops_patched(&mut asm, ctx, mnemonic, ops, &mut res)
}

pub(crate) static INFO: TargetInfo = {
    let t = offlineasm_ir::regs::RISCV64;
    TargetInfo {
        scratch: t.scratch,
        registers: t.registers,
        vreg_gpr: t.vreg_gpr,
        vreg_fpr: t.vreg_fpr,
        lower,
        lower_patched,
    }
};

/// Lowers one mnemonic: expands to IR, then emits each node. One fresh
/// [`LabelResolver`] scopes the expansion-internal labels to this call.
pub fn lower_ops(
    asm: &mut Assembler,
    ctx: &Scratch,
    mnemonic: Mnemonic,
    ops: &[Op],
    res: &mut LabelResolver,
) -> Result<(), LowerError> {
    crate::ir::check_callee_saved(mnemonic, ops, &[9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27])?;
    let insts = expand(mnemonic, ops, ctx, false)?;
    for inst in &insts {
        let mut l = Lx {
            asm,
            mn: mnemonic,
            res,
        };
        let handle = l.emit(inst)?;
        debug_assert!(handle.is_none(), "unpatched lowering emitted a patch site");
    }
    Ok(())
}

/// Lowers one `#[patch]` mnemonic. Exactly one patch handle must result.
pub fn lower_ops_patched(
    asm: &mut Assembler,
    ctx: &Scratch,
    mnemonic: Mnemonic,
    ops: &[Op],
    res: &mut LabelResolver,
) -> Result<PatchHandle, LowerError> {
    let insts = expand(mnemonic, ops, ctx, true)?;
    let mut handle = None;
    for inst in &insts {
        let mut l = Lx {
            asm,
            mn: mnemonic,
            res,
        };
        if let Some(h) = l.emit(inst)? {
            if handle.is_some() {
                return Err(bad(mnemonic, "expansion emitted several patch sites"));
            }
            handle = Some(h);
        }
    }
    handle.ok_or_else(|| bad(mnemonic, "no patch site in this expansion"))
}

#[derive(Clone, Copy)]
enum BSide {
    Op,
    Snap,
    SameAsA,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ZCond {
    Eqz,
    Nez,
    Ltz,
}

#[derive(Clone, Copy)]
enum OvfB {
    Reg(Gpr),
    Imm(i64),
}

struct Lx<'a, 'b, 'c> {
    asm: &'a mut Assembler<'b>,
    mn: Mnemonic,
    res: &'a mut LabelResolver<'c>,
}

impl Lx<'_, '_, '_> {
    fn bad(&self, msg: impl Into<String>) -> LowerError {
        bad(self.mn, msg)
    }

    fn e(&mut self, op: Opcode, ops: &[Operand]) {
        let refs: Vec<&Operand> = ops.iter().collect();
        self.asm.emit_n(op as i64, &refs);
    }

    /// `op rd, rs1, rs2`.
    fn rr(&mut self, op: Opcode, d: Gpr, a: Gpr, b: Gpr) {
        self.e(op, &[g(d), g(a), g(b)]);
    }

    /// `op rd, rs1, imm`.
    fn ri(&mut self, op: Opcode, d: Gpr, a: Gpr, v: i64) {
        self.e(op, &[g(d), g(a), i(v)]);
    }

    /// `op rd, off(base)`.
    fn load(&mut self, op: Opcode, d: Gpr, base: Gpr, off: i64) {
        self.e(op, &[g(d), g(base), i(off)]);
    }

    /// `op src, off(base)`.
    fn store(&mut self, op: Opcode, src: Gpr, base: Gpr, off: i64) {
        self.e(op, &[g(base), g(src), i(off)]);
    }

    fn fload(&mut self, op: Opcode, d: Fpr, base: Gpr, off: i64) {
        self.e(op, &[f(d), g(base), i(off)]);
    }

    fn fstore(&mut self, op: Opcode, src: Fpr, base: Gpr, off: i64) {
        self.e(op, &[g(base), f(src), i(off)]);
    }

    /// `mv d, s` (`addi d, s, 0`).
    fn mv(&mut self, d: Gpr, s: Gpr) {
        self.ri(Opcode::ADDI, d, s, 0);
    }

    fn slli(&mut self, d: Gpr, s: Gpr, n: i64) {
        self.ri(Opcode::SLLI, d, s, n);
    }

    fn srli(&mut self, d: Gpr, s: Gpr, n: i64) {
        self.ri(Opcode::SRLI, d, s, n);
    }

    fn srai(&mut self, d: Gpr, s: Gpr, n: i64) {
        self.ri(Opcode::SRAI, d, s, n);
    }

    /// `seqz d, s` (`sltiu d, s, 1`).
    fn seqz(&mut self, d: Gpr, s: Gpr) {
        self.ri(Opcode::SLTIU, d, s, 1);
    }

    /// `snez d, s` (`sltu d, x0, s`).
    fn snez(&mut self, d: Gpr, s: Gpr) {
        self.rr(Opcode::SLTU, d, X0, s);
    }

    fn fmv_fx(&mut self, k: FKind, d: Fpr, s: Gpr) {
        self.e(fsel(k, Opcode::FMVWX, Opcode::FMVDX), &[f(d), g(s)]);
    }

    fn fmv_xf(&mut self, k: FKind, d: Gpr, s: Fpr) {
        self.e(fsel(k, Opcode::FMVXW, Opcode::FMVXD), &[g(d), f(s)]);
    }

    fn label(&mut self, l: Lbl) -> Label {
        self.res.resolve(l, || self.asm.get_label())
    }

    fn fresh(&mut self) -> Label {
        self.asm.get_label()
    }

    fn bind(&mut self, l: Label) {
        self.asm.bind_label(l);
    }

    /// `op a, b, label`.
    fn br(&mut self, op: Opcode, a: Gpr, b: Gpr, t: Label) {
        self.e(op, &[g(a), g(b), *t.as_operand()]);
    }

    /// `j label` (`jal x0, label`).
    fn j(&mut self, t: Label) {
        self.e(Opcode::JAL, &[g(X0), *t.as_operand()]);
    }

    /// A patchable `j label`.
    fn patch_j(&mut self, t: Label) -> PatchHandle {
        PatchHandle::Jump(self.asm.patchable_j(t))
    }

    fn mov_imm(&mut self, dst: Gpr, v: i64) {
        use offlineasm_ir::riscv::LiStep;
        for (k, step) in offlineasm_ir::riscv::li(v).into_iter().enumerate() {
            let src = if k == 0 { X0 } else { dst };
            match step {
                LiStep::Lui(hi20) => {
                    self.e(Opcode::LUI, &[g(dst), i(i64::from((hi20 << 12) as i32))]);
                }
                LiStep::Addi(lo) => self.ri(Opcode::ADDI, dst, src, lo),
                LiStep::Addiw(lo) => self.ri(Opcode::ADDIW, dst, dst, lo),
                LiStep::Slli(n) => self.slli(dst, dst, i64::from(n)),
                LiStep::Srli(n) => self.srli(dst, dst, i64::from(n)),
            }
        }
    }

    fn mov_imm32(&mut self, dst: Gpr, v: u32) {
        self.mov_imm(dst, i64::from(v));
    }

    fn zero_upper32(&mut self, d: Gpr) {
        self.slli(d, d, 32);
        self.srli(d, d, 32);
    }

    fn mov_imm_w(&mut self, dst: Gpr, w: Width, v: i64) {
        if w == Width::B64 {
            self.mov_imm(dst, v);
        } else {
            self.mov_imm32(dst, v as u32);
        }
    }

    fn mov_reg(&mut self, dst: Gpr, src: Gpr, w: Width) {
        if dst == src {
            return;
        }
        match w {
            Width::B64 => self.ri(Opcode::ADDI, dst, src, 0),
            _ => self.ri(Opcode::ADDIW, dst, src, 0),
        }
    }

    fn neg_reg(&mut self, r: Gpr, w: Width) {
        if w == Width::B32 {
            self.rr(Opcode::SUBW, r, X0, r);
        } else {
            self.rr(Opcode::SUB, r, X0, r);
        }
    }

    fn gpr_dst(&self, op: &Op) -> Result<Gpr, LowerError> {
        match op {
            Op::Gpr(r) => Ok(*r),
            _ => Err(self.bad("expected a GPR destination")),
        }
    }

    fn sym_err(&self) -> LowerError {
        self.bad("symbolic immediates are offlineasm-only")
    }

    fn load_op_gpr(&mut self, op: &Op, w: Width, tmp: Gpr) -> Result<Gpr, LowerError> {
        match op {
            Op::Gpr(r) => Ok(*r),
            Op::Imm(v) => {
                self.mov_imm_w(tmp, w, *v);
                Ok(tmp)
            }
            Op::Sym(_) => Err(self.sym_err()),
            Op::Mem(a) => {
                self.e_load(w, Sx::Zero, tmp, a)?;
                Ok(tmp)
            }
            _ => Err(self.bad("expected a register, immediate, or memory operand")),
        }
    }

    /// `(base, disp)` when `a` encodes as `disp(base)` directly.
    fn direct_addr(&self, a: &Mem) -> Result<Option<(Gpr, i64)>, LowerError> {
        let Some(base) = a.base else {
            return Ok(None);
        };
        if a.index.is_some() {
            return Ok(None);
        }
        match a.disp {
            Disp::Const(v) if fits_d12(v) => Ok(Some((base, i64::from(v)))),
            Disp::Const(_) => Ok(None),
            Disp::Sym(_) => Err(self.bad("symbolic displacements are offlineasm-only")),
        }
    }

    /// Synthesize `base + disp + index * scale` into `tmp`.
    fn addr_scratch(&mut self, a: &Mem, tmp: Gpr) -> Result<(), LowerError> {
        let (base, disp) = match a.base {
            Some(b) => (b, a.disp),
            None => {
                match a.disp {
                    Disp::Const(v) => self.mov_imm(tmp, i64::from(v)),
                    Disp::Sym(_) => return Err(self.sym_err()),
                }
                (tmp, Disp::Const(0))
            }
        };
        match a.index {
            None => match disp {
                Disp::Const(v) if fits12(i64::from(v)) => {
                    self.ri(Opcode::ADDI, tmp, base, i64::from(v));
                }
                Disp::Const(v) => {
                    self.mov_imm(tmp, i64::from(v));
                    self.rr(Opcode::ADD, tmp, tmp, base);
                }
                Disp::Sym(_) => return Err(self.sym_err()),
            },
            Some((idx, scale)) => {
                let sh: i64 = match scale {
                    1 => 0,
                    2 => 1,
                    4 => 2,
                    8 => 3,
                    _ => return Err(self.bad("address scale out of range")),
                };
                if sh == 0 {
                    self.rr(Opcode::ADD, tmp, base, idx);
                } else {
                    self.slli(tmp, idx, sh);
                    self.rr(Opcode::ADD, tmp, tmp, base);
                }
                match disp {
                    Disp::Const(0) => {}
                    Disp::Const(v) if fits12(i64::from(v)) => {
                        self.ri(Opcode::ADDI, tmp, tmp, i64::from(v));
                    }
                    _ => {
                        return Err(
                            self.bad("indexed address with a large displacement is unsupported")
                        )
                    }
                }
            }
        }
        Ok(())
    }

    fn e_load(&mut self, w: Width, sx: Sx, dst: Gpr, a: &Mem) -> Result<(), LowerError> {
        let op = load_op(w, sx);
        if let Some((b, d)) = self.direct_addr(a)? {
            self.load(op, dst, b, d);
            return Ok(());
        }
        self.addr_scratch(a, G1)?;
        self.load(op, dst, G1, 0);
        Ok(())
    }

    fn e_store(&mut self, w: Width, src: &Op, a: &Mem) -> Result<(), LowerError> {
        let op = store_op(w);
        let direct = self.direct_addr(a)?;
        match src {
            Op::Gpr(r) => {
                if let Some((b, d)) = direct {
                    self.store(op, *r, b, d);
                    return Ok(());
                }
                let s = if *r == G1 {
                    self.mov_reg(G2, G1, Width::B64);
                    self.addr_scratch(a, G1)?;
                    G2
                } else {
                    self.addr_scratch(a, G1)?;
                    *r
                };
                self.store(op, s, G1, 0);
                Ok(())
            }
            Op::Imm(v) => {
                if let Some((b, d)) = direct {
                    self.mov_imm_w(G1, w, *v);
                    self.store(op, G1, b, d);
                    return Ok(());
                }
                self.mov_imm_w(G1, w, *v);
                self.addr_scratch(a, G2)?;
                self.store(op, G1, G2, 0);
                Ok(())
            }
            Op::Sym(_) => Err(self.sym_err()),
            _ => Err(self.bad("store needs a register, immediate, or symbolic source")),
        }
    }

    fn e_loadf(&mut self, k: FKind, dst: Fpr, a: &Mem) -> Result<(), LowerError> {
        let op = fsel(k, Opcode::FLW, Opcode::FLD);
        if let Some((b, d)) = self.direct_addr(a)? {
            self.fload(op, dst, b, d);
            return Ok(());
        }
        self.addr_scratch(a, G1)?;
        self.fload(op, dst, G1, 0);
        Ok(())
    }

    fn e_storef(&mut self, k: FKind, src: Fpr, a: &Mem) -> Result<(), LowerError> {
        let op = fsel(k, Opcode::FSW, Opcode::FSD);
        if let Some((b, d)) = self.direct_addr(a)? {
            self.fstore(op, src, b, d);
            return Ok(());
        }
        self.addr_scratch(a, G1)?;
        self.fstore(op, src, G1, 0);
        Ok(())
    }

    fn vec_hi_disp(&self, a: &Mem) -> Result<i32, LowerError> {
        a.disp
            .const_or_zero()
            .checked_add(8)
            .ok_or_else(|| self.bad("vector address overflow"))
    }

    fn e_loadv(&mut self, dst: Fpr, a: &Mem) -> Result<(), LowerError> {
        let hi = fhi(self.mn, dst)?;
        let hi_disp = self.vec_hi_disp(a)?;
        if a.index.is_none()
            && a.base.is_some()
            && fits_d12(a.disp.const_or_zero())
            && fits_d12(hi_disp)
        {
            let b = a.base_reg();
            self.fload(Opcode::FLD, dst, b, i64::from(a.disp.const_or_zero()));
            self.fload(Opcode::FLD, hi, b, i64::from(hi_disp));
            return Ok(());
        }
        self.addr_scratch(a, G1)?;
        self.fload(Opcode::FLD, dst, G1, 0);
        self.fload(Opcode::FLD, hi, G1, 8);
        Ok(())
    }

    fn e_storev(&mut self, src: Fpr, a: &Mem) -> Result<(), LowerError> {
        let hi = fhi(self.mn, src)?;
        let hi_disp = self.vec_hi_disp(a)?;
        if a.index.is_none()
            && a.base.is_some()
            && fits_d12(a.disp.const_or_zero())
            && fits_d12(hi_disp)
        {
            let b = a.base_reg();
            self.fstore(Opcode::FSD, src, b, i64::from(a.disp.const_or_zero()));
            self.fstore(Opcode::FSD, hi, b, i64::from(hi_disp));
            return Ok(());
        }
        // Park the high lane in the FP scratch while the address folds.
        if hi != SF {
            self.rv_fmov(FKind::F64, SF, hi);
        }
        self.addr_scratch(a, G1)?;
        self.fstore(Opcode::FSD, src, G1, 0);
        self.fstore(Opcode::FSD, SF, G1, 8);
        Ok(())
    }

    fn e_vmov(&mut self, dst: Fpr, src: Fpr) -> Result<(), LowerError> {
        if dst == src {
            return Ok(());
        }
        let dhi = fhi(self.mn, dst)?;
        let shi = fhi(self.mn, src)?;
        self.rv_fmov(FKind::F64, dst, src);
        self.rv_fmov(FKind::F64, dhi, shi);
        Ok(())
    }

    fn e_vecextract(&mut self, w: Width, dst: Gpr, src: Fpr, lane: u8) -> Result<(), LowerError> {
        let size = w.bytes();
        let lanes = 16 / size;
        if u32::from(lane) >= lanes {
            return Err(self.bad("lane out of range"));
        }
        let hi = fhi(self.mn, src)?;
        if w == Width::B64 {
            let from = if lane == 0 { src } else { hi };
            self.fmv_xf(FKind::F64, dst, from);
            return Ok(());
        }
        // Sub-64 lanes spill the holding half through `sp` (balanced).
        let byte = u32::from(lane) * size;
        let (half, off) = if byte < 8 {
            (src, i64::from(byte))
        } else {
            (hi, i64::from(byte - 8))
        };
        self.ri(Opcode::ADDI, SP, SP, -8);
        self.fstore(Opcode::FSD, half, SP, 0);
        let op = match w {
            Width::B8 => Opcode::LBU,
            Width::B16 => Opcode::LHU,
            Width::B32 => Opcode::LW,
            Width::B64 => Opcode::LD,
        };
        self.load(op, dst, SP, off);
        self.ri(Opcode::ADDI, SP, SP, 8);
        Ok(())
    }

    /// `la d, label`: `auipc` + `addi` with the label's PC-relative offset.
    fn la(&mut self, d: Gpr, l: Lbl) {
        let t = self.label(l);
        self.asm.la(x(d), t);
    }

    /// Address of extern `e` into `d`, as `lla` (near: `auipc` + `addi`)
    /// or `lga` (far: `auipc` + `ld` of its GOT entry) expand. The low
    /// relocation names the `auipc`, as in the psABI.
    fn extern_address(&mut self, d: Gpr, e: Extern) {
        let sym = RelocTarget::Sym(Sym::from_id(e.id.0));
        let hi = match e.reach {
            Reach::Near => Reloc::RiscvPCRelHi20,
            Reach::Far => Reloc::RiscvGotHi20,
        };
        let buf = self.asm.buffer_mut();
        let auipc = buf.get_label();
        buf.bind_label(auipc);
        buf.add_reloc(hi, sym, 0);
        self.e(Opcode::AUIPC, &[g(d), i(0)]);
        self.asm
            .buffer_mut()
            .add_reloc(Reloc::RiscvPCRelLo12I, RelocTarget::Label(auipc), 0);
        match e.reach {
            Reach::Near => self.ri(Opcode::ADDI, d, d, 0),
            Reach::Far => self.load(Opcode::LD, d, d, 0),
        }
    }

    fn extern_call_plt(&mut self, e: Extern, is_call: bool) {
        let (tmp, link) = if is_call { (RA, RA) } else { (G1, X0) };
        let sym = RelocTarget::Sym(Sym::from_id(e.id.0));
        self.asm.buffer_mut().add_reloc(Reloc::RiscvCallPlt, sym, 0);
        self.e(Opcode::AUIPC, &[g(tmp), i(0)]);
        self.ri(Opcode::JALR, link, tmp, 0);
    }

    fn e_mov(&mut self, w: Width, dst: &Op, src: &Op) -> Result<(), LowerError> {
        match (src, dst) {
            (Op::Imm(v), Op::Gpr(d)) => {
                self.mov_imm_w(*d, w, *v);
                Ok(())
            }
            (Op::Sym(_), Op::Gpr(_)) => Err(self.sym_err()),
            (Op::Gpr(s), Op::Gpr(d)) => {
                match w {
                    Width::B64 => self.mov_reg(*d, *s, Width::B64),
                    Width::B32 => {
                        // A 32-bit move zeroes the upper half, even when the
                        // source and destination are the same register.
                        self.slli(*d, *s, 32);
                        self.srli(*d, *d, 32);
                    }
                    Width::B8 | Width::B16 => {
                        if s != d {
                            let (sh, n) = if w == Width::B8 { (56, 8) } else { (48, 16) };
                            self.slli(G1, *s, sh);
                            self.srli(G1, G1, sh);
                            self.srli(*d, *d, n);
                            self.slli(*d, *d, n);
                            self.rr(Opcode::OR, *d, *d, G1);
                        }
                    }
                }
                Ok(())
            }
            (Op::Label(l), Op::Gpr(d)) => {
                self.la(*d, *l);
                match w {
                    Width::B64 => {}
                    Width::B32 => self.zero_upper32(*d),
                    _ => self.mov_reg(*d, *d, w),
                }
                Ok(())
            }
            (Op::Mem(a), Op::Gpr(d)) => self.e_load(w, Sx::Zero, *d, a),
            (Op::Gpr(s), Op::Mem(a)) => self.e_store(w, &Op::Gpr(*s), a),
            (Op::Imm(v), Op::Mem(a)) => self.e_store(w, &Op::Imm(*v), a),
            (Op::Sym(_), Op::Mem(_)) => Err(self.sym_err()),
            _ => Err(self.bad("unsupported mov operand pair")),
        }
    }

    fn e_movzero32(&mut self, dst: &Op, src: &Op) -> Result<(), LowerError> {
        match (dst, src) {
            (Op::Gpr(d), Op::Gpr(s)) => {
                self.slli(*d, *s, 32);
                self.srli(*d, *d, 32);
                Ok(())
            }
            (Op::Gpr(d), Op::Mem(a)) => self.e_load(Width::B32, Sx::Zero, *d, a),
            (Op::Mem(a), Op::Gpr(s)) => self.e_store(Width::B32, &Op::Gpr(*s), a),
            _ => Err(self.bad("movzero32 needs register/memory operands")),
        }
    }

    fn e_bswap(&mut self, w: Width, dst: &Op, src: &Op) -> Result<(), LowerError> {
        let (d, s) = match (dst, src) {
            (Op::Gpr(d), Op::Gpr(s)) => (*d, *s),
            _ => return Err(self.bad("bswap needs general-purpose registers")),
        };
        let (mask1, mask2) = match w {
            Width::B32 => (0x00FF_00FFi64, 0x0000_FFFFi64),
            Width::B64 => (
                0x00FF_00FF_00FF_00FFu64 as i64,
                0x0000_FFFF_0000_FFFFu64 as i64,
            ),
            _ => return Err(self.bad("bswap needs a 32/64-bit width")),
        };
        if d != s {
            self.rr(Opcode::ADD, d, s, X0);
        }
        // Byte swap inside each 16-bit half.
        self.mov_imm(G1, mask1);
        self.rr(Opcode::AND, G2, d, G1);
        self.slli(G2, G2, 8);
        self.srli(G1, d, 8);
        self.mov_imm(d, mask1);
        self.rr(Opcode::AND, d, G1, d);
        self.rr(Opcode::OR, d, d, G2);
        // Then the 16-bit halves.
        self.mov_imm(G1, mask2);
        self.rr(Opcode::AND, G2, d, G1);
        self.slli(G2, G2, 16);
        self.srli(G1, d, 16);
        self.mov_imm(d, mask2);
        self.rr(Opcode::AND, d, G1, d);
        self.rr(Opcode::OR, d, d, G2);
        if w == Width::B64 {
            self.slli(G1, d, 32);
            self.srli(d, d, 32);
            self.rr(Opcode::OR, d, d, G1);
        }
        Ok(())
    }

    fn e_lea(&mut self, w: Width, dst: Gpr, src: &LeaSrc) -> Result<(), LowerError> {
        match src {
            LeaSrc::Mem(a) => {
                let needs_tmp = a.index.is_none()
                    && !fits12(i64::from(a.disp.const_or_zero()))
                    && a.base == Some(dst);
                if needs_tmp {
                    self.addr_scratch(a, G1)?;
                    self.mov_reg(dst, G1, Width::B64);
                } else {
                    self.addr_scratch(a, dst)?;
                }
            }
            LeaSrc::Label(l) => self.la(dst, *l),
            LeaSrc::Extern(e) => self.extern_address(dst, *e),
        }
        if w == Width::B32 {
            self.zero_upper32(dst);
        }
        Ok(())
    }

    fn alu_rr(&mut self, k: AluKind, w: Width, dst: Gpr, lhs: Gpr, rhs: Gpr) {
        self.rr(k.op(), dst, lhs, rhs);
        if w == Width::B32 {
            self.zero_upper32(dst);
        }
    }

    fn alu_narrow_merge(&mut self, w: Width, dst: Gpr) {
        let n = if w == Width::B8 { 8 } else { 16 };
        self.slli(G1, G1, 64 - n);
        self.srli(G1, G1, 64 - n);
        self.srli(dst, dst, n);
        self.slli(dst, dst, n);
        self.rr(Opcode::OR, dst, dst, G1);
    }

    fn alu_narrow(&mut self, k: AluKind, w: Width, dst: Gpr, rhs: Gpr) -> Result<(), LowerError> {
        if dst == G1 {
            return Err(self.bad("narrow ALU aliased the scratch register"));
        }
        self.rr(k.op(), G1, dst, rhs);
        self.alu_narrow_merge(w, dst);
        Ok(())
    }

    fn alu_reg(&mut self, k: AluKind, w: Width, dst: Gpr, rhs: &Op) -> Result<(), LowerError> {
        let narrow = w == Width::B8 || w == Width::B16;
        match rhs {
            Op::Gpr(s) => {
                if narrow {
                    self.alu_narrow(k, w, dst, *s)?;
                } else {
                    self.alu_rr(k, w, dst, dst, *s);
                }
                Ok(())
            }
            Op::Mem(a) => {
                let lw = if w == Width::B64 { w } else { Width::B32 };
                self.e_load(lw, Sx::Zero, G1, a)?;
                if narrow {
                    self.alu_narrow(k, w, dst, G1)?;
                } else {
                    self.alu_rr(k, w, dst, dst, G1);
                }
                Ok(())
            }
            Op::Imm(v) => self.alu_imm(k, w, dst, *v),
            Op::Sym(_) => Err(self.sym_err()),
            _ => Err(self.bad("ALU needs a register, memory, or immediate source")),
        }
    }

    fn alu_imm(&mut self, k: AluKind, w: Width, dst: Gpr, v: i64) -> Result<(), LowerError> {
        let narrow = w == Width::B8 || w == Width::B16;
        if fits12(v) && k != AluKind::Mul {
            let v = if k == AluKind::Sub { -v } else { v };
            if narrow {
                self.ri(k.imm_op(), G1, dst, v);
                self.alu_narrow_merge(w, dst);
                return Ok(());
            }
            self.ri(k.imm_op(), dst, dst, v);
            if w == Width::B32 {
                self.zero_upper32(dst);
            }
            return Ok(());
        }
        let lw = if w == Width::B64 { w } else { Width::B32 };
        self.mov_imm_w(G1, lw, v);
        if narrow {
            self.alu_narrow(k, w, dst, G1)
        } else {
            self.alu_rr(k, w, dst, dst, G1);
            Ok(())
        }
    }

    fn alu_mem_dst(&mut self, k: AluKind, w: Width, a: &Mem, rhs: &Op) -> Result<(), LowerError> {
        let lw = if w == Width::B64 { w } else { Width::B32 };
        self.e_load(lw, Sx::Zero, G1, a)?;
        self.alu_mem_rhs(k, w, rhs)?;
        self.e_store(w, &Op::Gpr(G1), a)
    }

    fn alu_mem_dst3(
        &mut self,
        k: AluKind,
        w: Width,
        a: &Mem,
        lhs: &Op,
        rhs: &Op,
    ) -> Result<(), LowerError> {
        let lw = if w == Width::B64 { w } else { Width::B32 };
        match lhs {
            Op::Gpr(r) => self.mov_reg(G1, *r, lw),
            Op::Imm(v) => self.mov_imm_w(G1, lw, *v),
            Op::Sym(_) => return Err(self.sym_err()),
            Op::Mem(l) => self.e_load(lw, Sx::Zero, G1, l)?,
            _ => return Err(self.bad("ALU needs a register, memory, or immediate source")),
        }
        self.alu_mem_rhs(k, w, rhs)?;
        self.e_store(w, &Op::Gpr(G1), a)
    }

    fn alu_mem_rhs(&mut self, k: AluKind, w: Width, rhs: &Op) -> Result<(), LowerError> {
        match rhs {
            Op::Gpr(s) => {
                self.rr(k.op(), G1, G1, *s);
                if w == Width::B8 || w == Width::B16 {
                    // The cell is reloaded fresh, so no upper-bit preservation
                    // is needed. Truncate the folded lane.
                    let sh = if w == Width::B8 { 56 } else { 48 };
                    self.slli(G1, G1, sh);
                    self.srli(G1, G1, sh);
                } else if w == Width::B32 {
                    self.zero_upper32(G1);
                }
                Ok(())
            }
            Op::Imm(v) => match k {
                AluKind::Add | AluKind::Sub => {
                    let (add, mag) = if *v < 0 {
                        (k != AluKind::Add, v.wrapping_neg())
                    } else {
                        (k == AluKind::Add, *v)
                    };
                    if !fits12(mag) {
                        return Err(self.bad(
                            "memory-destination ALU needs a register or 12-bit immediate rhs",
                        ));
                    }
                    self.ri(Opcode::ADDI, G1, G1, if add { mag } else { -mag });
                    if w == Width::B32 {
                        self.zero_upper32(G1);
                    }
                    Ok(())
                }
                _ => Err(self.bad("memory-destination ALU needs a register or add/sub rhs")),
            },
            Op::Sym(_) => Err(self.sym_err()),
            _ => Err(self.bad("memory-destination ALU needs a register or immediate rhs")),
        }
    }

    fn stage_lhs(&mut self, op: &Op, dst: Gpr, w: Width, lw: Width) -> Result<(), LowerError> {
        match op {
            Op::Gpr(r) => self.mov_reg(dst, *r, w),
            Op::Imm(v) => self.mov_imm_w(dst, w, *v),
            Op::Sym(_) => return Err(self.sym_err()),
            Op::Mem(a) => self.e_load(lw, Sx::Zero, dst, a)?,
            _ => return Err(self.bad("ALU needs a register, memory, or immediate source")),
        }
        Ok(())
    }

    fn op_n(&mut self, k: AluKind, w: Width, ops: &[Op]) -> Result<(), LowerError> {
        if ops.len() != 2 && ops.len() != 3 {
            return Err(self.bad(format!("expected 2 or 3 operands, got {}", ops.len())));
        }
        if ops.len() == 2 {
            if let Op::Mem(a) = &ops[1] {
                return self.alu_mem_dst(k, w, a, &ops[0]);
            }
            let dst = self.gpr_dst(&ops[1])?;
            return self.alu_reg(k, w, dst, &ops[0]);
        }
        if let Op::Mem(a) = &ops[2] {
            return self.alu_mem_dst3(k, w, a, &ops[0], &ops[1]);
        }
        let dst = self.gpr_dst(&ops[2])?;
        if crate::ir::op_eq(&ops[0], &ops[2]) {
            return self.alu_reg(k, w, dst, &ops[1]);
        }
        if crate::ir::op_eq(&ops[1], &ops[2]) {
            if k == AluKind::Sub {
                if w == Width::B8 || w == Width::B16 {
                    // `dst = lhs - dst`: the old dst survives on the stack
                    // while scratch folds the subtraction.
                    let n = if w == Width::B8 { 8 } else { 16 };
                    self.ri(Opcode::ADDI, SP, SP, -8);
                    self.store(Opcode::SD, dst, SP, 0);
                    self.ri(Opcode::ADDI, G1, dst, 0);
                    self.neg_reg(G1, Width::B64);
                    self.stage_lhs(&ops[0], dst, w, Width::B32)?;
                    self.rr(Opcode::ADD, G1, dst, G1);
                    self.slli(G1, G1, 64 - n);
                    self.srli(G1, G1, 64 - n);
                    self.load(Opcode::LD, dst, SP, 0);
                    self.ri(Opcode::ADDI, SP, SP, 8);
                    self.srli(dst, dst, n);
                    self.slli(dst, dst, n);
                    self.rr(Opcode::OR, dst, dst, G1);
                    return Ok(());
                }
                // `dst = lhs - dst`: negate the old dst in scratch, move lhs
                // to dst, then add.
                self.mov_reg(G1, dst, w);
                self.neg_reg(G1, w);
                let lw = if w == Width::B64 { w } else { Width::B32 };
                self.stage_lhs(&ops[0], dst, w, lw)?;
                if w == Width::B32 {
                    self.zero_upper32(G1);
                }
                return self.alu_reg(AluKind::Add, w, dst, &Op::Gpr(G1));
            }
            if matches!(
                k,
                AluKind::Add | AluKind::Mul | AluKind::And | AluKind::Or | AluKind::Xor
            ) {
                return self.alu_reg(k, w, dst, &ops[0]);
            }
            return Err(self.bad("aliased operands need a commutative op"));
        }

        if let (Width::B64 | Width::B32, Op::Gpr(l), Op::Gpr(r)) = (w, &ops[0], &ops[1]) {
            self.rr(k.op(), dst, *l, *r);
            if w == Width::B32 {
                self.zero_upper32(dst);
            }
            return Ok(());
        }

        let lw = if w == Width::B64 { w } else { Width::B32 };
        self.stage_lhs(&ops[0], dst, lw, lw)?;
        self.alu_reg(k, w, dst, &ops[1])
    }

    fn e_not_neg(&mut self, w: Width, dst: &Op, neg: bool) -> Result<(), LowerError> {
        let d = self.gpr_dst(dst)?;
        if neg {
            if w == Width::B32 {
                self.rr(Opcode::SUBW, d, X0, d);
                self.zero_upper32(d);
            } else {
                self.rr(Opcode::SUB, d, X0, d);
            }
            return Ok(());
        }
        if w == Width::B8 || w == Width::B16 {
            let n = if w == Width::B8 { 8 } else { 16 };
            let t = if d == G1 { G2 } else { G1 };

            self.ri(Opcode::ADDI, SP, SP, -8);
            self.store(Opcode::SD, d, SP, 0);
            self.ri(Opcode::XORI, t, d, -1);
            self.slli(t, t, 64 - n);
            self.srli(t, t, 64 - n);
            self.load(Opcode::LD, d, SP, 0);
            self.ri(Opcode::ADDI, SP, SP, 8);
            self.srli(d, d, n);
            self.slli(d, d, n);
            self.rr(Opcode::OR, d, d, t);
        } else {
            self.ri(Opcode::XORI, d, d, -1);
            if w == Width::B32 {
                self.zero_upper32(d);
            }
        }
        Ok(())
    }

    fn e_mulimm(&mut self, w: Width, dst: Gpr, lhs: Gpr, v: i64) -> Result<(), LowerError> {
        // Power-of-two multipliers become shifts.
        if v > 0 && (v as u64).is_power_of_two() {
            let sh = i64::from((v as u64).trailing_zeros());
            if dst != lhs {
                self.mov_reg(dst, lhs, w);
            }
            if w == Width::B32 {
                self.ri(Opcode::SLLIW, dst, dst, sh);
                return Ok(());
            }
            return self.e_shift(w, ShiftOp::Shl, dst, &ShiftCnt::Imm(sh));
        }
        let lw = if w == Width::B64 { w } else { Width::B32 };
        self.mov_imm_w(G1, lw, v);
        if w == Width::B8 || w == Width::B16 {
            self.alu_narrow(AluKind::Mul, w, dst, G1)
        } else {
            self.alu_rr(AluKind::Mul, w, dst, lhs, G1);
            Ok(())
        }
    }

    // rotate by already masked immediate
    fn rotl_imm(&mut self, w: Width, dst: Gpr, r: i64) -> Result<(), LowerError> {
        if r == 0 {
            return Ok(());
        }
        if dst == G1 {
            return Err(self.bad("rotate aliased the scratch register"));
        }
        let bits: i64 = if w == Width::B32 { 32 } else { 64 };
        self.ri(wsel(w, Opcode::SLLI, Opcode::SLLIW), G1, dst, r);
        self.ri(wsel(w, Opcode::SRLI, Opcode::SRLIW), dst, dst, bits - r);
        self.rr(Opcode::OR, dst, dst, G1);
        if w == Width::B32 {
            self.zero_upper32(dst);
        }
        Ok(())
    }

    /// rotate by a register
    fn rot_reg(&mut self, w: Width, dst: Gpr, cnt: Gpr, left: bool) -> Result<(), LowerError> {
        let bits: i64 = if w == Width::B32 { 32 } else { 64 };
        if dst == G1 || cnt == G1 {
            return Err(self.bad("rotate aliased the scratch register"));
        }
        self.rr(Opcode::SUB, G1, X0, cnt);
        self.ri(Opcode::ADDI, G1, G1, bits);
        let sll = wsel(w, Opcode::SLL, Opcode::SLLW);
        let srl = wsel(w, Opcode::SRL, Opcode::SRLW);
        let (a, b) = if left { (srl, sll) } else { (sll, srl) };
        self.rr(a, G1, dst, G1);
        self.rr(b, dst, dst, cnt);
        self.rr(Opcode::OR, dst, dst, G1);
        if w == Width::B32 {
            self.zero_upper32(dst);
        }
        Ok(())
    }

    fn lane_rot_reg(&mut self, n: i64, dst: Gpr, cnt: Gpr, left: bool) {
        self.ri(Opcode::ADDI, G1, X0, n);
        self.rr(Opcode::REMU, G1, cnt, G1);
        let done = self.fresh();
        self.br(Opcode::BEQ, G1, X0, done);
        self.ri(Opcode::ADDI, SP, SP, -24);
        self.store(Opcode::SD, dst, SP, 16);
        self.store(Opcode::SD, dst, SP, 8);
        self.store(Opcode::SD, G1, SP, 0);
        let (shift_in, shift_out) = if left {
            (Opcode::SLL, Opcode::SRL)
        } else {
            (Opcode::SRL, Opcode::SLL)
        };
        self.load(Opcode::LD, dst, SP, 16);
        self.load(Opcode::LD, G1, SP, 0);
        self.rr(shift_in, dst, dst, G1);
        self.store(Opcode::SD, dst, SP, 16);
        self.load(Opcode::LD, dst, SP, 8);
        self.load(Opcode::LD, G1, SP, 0);
        self.rr(Opcode::SUB, G1, X0, G1);
        self.ri(Opcode::ADDI, G1, G1, n);
        self.rr(shift_out, dst, dst, G1);
        self.load(Opcode::LD, G1, SP, 16);
        self.rr(Opcode::OR, dst, dst, G1);
        self.ri(Opcode::ADDI, SP, SP, 24);
        self.bind(done);
    }

    fn e_shift_narrow(
        &mut self,
        w: Width,
        op: ShiftOp,
        dst: Gpr,
        cnt: &ShiftCnt,
    ) -> Result<(), LowerError> {
        let n: i64 = if w == Width::B8 { 8 } else { 16 };
        if dst == G1 {
            return Err(self.bad("narrow shift aliased the scratch register"));
        }
        self.ri(Opcode::ADDI, SP, SP, -8);
        self.store(Opcode::SD, dst, SP, 0);
        self.slli(dst, dst, 64 - n);
        self.srli(dst, dst, 64 - n);
        match cnt {
            ShiftCnt::Imm(v) => {
                let c = (*v as u64 & 63) as i64;
                match op {
                    ShiftOp::Shl => self.slli(dst, dst, c),
                    ShiftOp::Shr | ShiftOp::ShrSar => self.srli(dst, dst, c),
                    ShiftOp::Rotl | ShiftOp::Rotr => {
                        let r = if op == ShiftOp::Rotl {
                            c as u64 % n as u64
                        } else {
                            (n as u64 - c as u64) % n as u64
                        } as i64;
                        if r != 0 {
                            self.slli(G1, dst, r);
                            self.srli(dst, dst, n - r);
                            self.rr(Opcode::OR, dst, dst, G1);
                        }
                    }
                }
            }
            ShiftCnt::Reg(r) => {
                if *r == G1 {
                    return Err(self.bad("narrow shift count aliased scratch"));
                }
                match op {
                    ShiftOp::Shl => self.rr(Opcode::SLL, dst, dst, *r),
                    ShiftOp::Shr | ShiftOp::ShrSar => self.rr(Opcode::SRL, dst, dst, *r),
                    ShiftOp::Rotl | ShiftOp::Rotr => {
                        self.lane_rot_reg(n, dst, *r, op == ShiftOp::Rotl);
                    }
                }
            }
        }

        self.slli(G1, dst, 64 - n);
        self.srli(G1, G1, 64 - n);
        self.load(Opcode::LD, dst, SP, 0);
        self.ri(Opcode::ADDI, SP, SP, 8);
        self.srli(dst, dst, n);
        self.slli(dst, dst, n);
        self.rr(Opcode::OR, dst, dst, G1);
        Ok(())
    }

    fn e_shift(
        &mut self,
        w: Width,
        op: ShiftOp,
        dst: Gpr,
        cnt: &ShiftCnt,
    ) -> Result<(), LowerError> {
        if w == Width::B8 || w == Width::B16 {
            return self.e_shift_narrow(w, op, dst, cnt);
        }
        let bits: i64 = if w == Width::B32 { 32 } else { 64 };
        match cnt {
            ShiftCnt::Imm(v) => {
                let mask: u64 = if w == Width::B32 { 31 } else { 63 };
                let c = (*v as u64 & mask) as i64;
                match op {
                    ShiftOp::Shl => self.ri(wsel(w, Opcode::SLLI, Opcode::SLLIW), dst, dst, c),
                    ShiftOp::Shr => self.ri(wsel(w, Opcode::SRLI, Opcode::SRLIW), dst, dst, c),
                    ShiftOp::ShrSar => self.ri(wsel(w, Opcode::SRAI, Opcode::SRAIW), dst, dst, c),
                    ShiftOp::Rotl | ShiftOp::Rotr => {
                        let r = if op == ShiftOp::Rotl {
                            c as u64
                        } else {
                            (bits as u64 - c as u64) % bits as u64
                        };
                        self.rotl_imm(w, dst, r as i64)?;
                    }
                }
            }
            ShiftCnt::Reg(r) => match op {
                ShiftOp::Shl => self.rr(wsel(w, Opcode::SLL, Opcode::SLLW), dst, dst, *r),
                ShiftOp::Shr => self.rr(wsel(w, Opcode::SRL, Opcode::SRLW), dst, dst, *r),
                ShiftOp::ShrSar => self.rr(wsel(w, Opcode::SRA, Opcode::SRAW), dst, dst, *r),
                ShiftOp::Rotl | ShiftOp::Rotr => {
                    self.rot_reg(w, dst, *r, op == ShiftOp::Rotl)?;
                }
            },
        }
        if w == Width::B32 {
            self.zero_upper32(dst);
        }
        Ok(())
    }

    fn e_extend(
        &mut self,
        from: Width,
        to: Width,
        sx: Sx,
        dst: Gpr,
        src: &Op,
    ) -> Result<(), LowerError> {
        let v = self.load_op_gpr(src, from, G1)?;
        let d = dst;
        match (from, to, sx) {
            (Width::B8, _, Sx::Zero) => self.ri(Opcode::ANDI, d, v, 255),
            (Width::B8, Width::B32, Sx::Sign) => {
                self.slli(d, v, 56);
                self.srai(d, d, 56);
                // keep only low 32 bits
                self.slli(d, d, 32);
                self.srli(d, d, 32);
            }
            (Width::B8, _, Sx::Sign) => {
                self.slli(d, v, 56);
                self.srai(d, d, 56);
            }
            (Width::B16, _, Sx::Zero) => {
                self.slli(d, v, 48);
                self.srli(d, d, 48);
            }
            (Width::B16, Width::B32, Sx::Sign) => {
                self.slli(d, v, 48);
                self.srai(d, d, 48);
                self.slli(d, d, 32);
                self.srli(d, d, 32);
            }
            (Width::B16, _, Sx::Sign) => {
                self.slli(d, v, 48);
                self.srai(d, d, 48);
            }
            (Width::B32, Width::B64, Sx::Sign) => self.ri(Opcode::ADDIW, d, v, 0),
            (Width::B32, _, _) => {
                self.slli(d, v, 32);
                self.srli(d, d, 32);
            }
            _ => return Err(self.bad("unsupported extension combination")),
        }
        Ok(())
    }

    fn div_rr(&mut self, w: Width, signed: bool, div: bool, dst: Gpr, lhs: Gpr, rhs: Gpr) {
        let op = match (signed, div, w == Width::B32) {
            (true, true, false) => Opcode::DIV,
            (true, false, false) => Opcode::REM,
            (false, true, false) => Opcode::DIVU,
            (false, false, false) => Opcode::REMU,
            (true, true, true) => Opcode::DIVW,
            (true, false, true) => Opcode::REMW,
            (false, true, true) => Opcode::DIVUW,
            (false, false, true) => Opcode::REMUW,
        };
        self.rr(op, dst, lhs, rhs);
        if w == Width::B32 {
            self.zero_upper32(dst);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn e_div(
        &mut self,
        w: Width,
        signed: bool,
        div: bool,
        dst: Gpr,
        dvd: &Op,
        dvs: &Op,
    ) -> Result<(), LowerError> {
        let l = self.load_op_gpr(dvd, w, G1)?;
        if !matches!(dvs, Op::Gpr(_)) && l == G1 {
            self.ri(Opcode::ADDI, SP, SP, -8);
            self.store(Opcode::SD, l, SP, 0);
            let r = self.load_op_gpr(dvs, w, G1)?;
            self.load(Opcode::LD, l, SP, 0);
            self.ri(Opcode::ADDI, SP, SP, 8);
            self.div_rr(w, signed, div, dst, l, r);
            return Ok(());
        }
        let r = self.load_op_gpr(dvs, w, G1)?;
        self.div_rr(w, signed, div, dst, l, r);
        Ok(())
    }

    // TODO: Zbb?
    fn clz_rr(&mut self, w: Width, dst: Gpr, src: Gpr) {
        self.mov_reg(dst, src, Width::B64);
        let (d, n, t) = (dst, G1, G2);
        if w == Width::B32 {
            self.slli(d, d, 32);
            self.mov_imm(G2, 0xFFFF_FFFF);
            self.rr(Opcode::OR, d, d, t);
        }
        self.ri(Opcode::ADDI, n, X0, 0);
        for k in [32, 16, 8, 4, 2, 1] {
            self.srli(t, d, 64 - k);
            let skip = self.fresh();
            self.br(Opcode::BNE, t, X0, skip);
            self.ri(Opcode::ADDI, n, n, k);
            self.slli(d, d, k);
            self.bind(skip);
        }
        let nonzero = self.fresh();
        self.br(Opcode::BNE, d, X0, nonzero);
        self.ri(Opcode::ADDI, n, n, 1);
        self.bind(nonzero);
        self.mov_reg(dst, G1, Width::B64);
    }

    /// TODO: Zbb?
    fn ctz_rr(&mut self, w: Width, dst: Gpr, src: Gpr) {
        self.mov_reg(dst, src, Width::B64);
        let (d, n, t) = (dst, G1, G2);
        if w == Width::B32 {
            self.mov_imm(G2, 0xFFFF_FFFF_0000_0000u64 as i64);
            self.rr(Opcode::OR, d, d, t);
        }
        self.ri(Opcode::ADDI, n, X0, 0);
        for k in [32, 16, 8, 4, 2, 1] {
            self.slli(t, d, 64 - k);
            let keep = self.fresh();
            let next = self.fresh();
            self.br(Opcode::BNE, t, X0, keep);
            self.ri(Opcode::ADDI, n, n, k);
            self.srli(d, d, k);
            self.j(next);
            self.bind(keep);
            self.bind(next);
        }
        let nonzero = self.fresh();
        self.br(Opcode::BNE, d, X0, nonzero);
        self.ri(Opcode::ADDI, n, n, 1);
        self.bind(nonzero);
        self.mov_reg(dst, G1, Width::B64);
    }

    /// TODO: Zbb?
    fn popcnt_rr(&mut self, dst: Gpr, src: Gpr) {
        self.mov_reg(dst, src, Width::B64);
        let (d, t, m) = (dst, G1, G2);
        self.mov_imm(G2, 0x5555_5555_5555_5555u64 as i64);
        self.srli(t, d, 1);
        self.rr(Opcode::AND, t, t, m);
        self.rr(Opcode::SUB, d, d, t);
        self.mov_imm(G2, 0x3333_3333_3333_3333u64 as i64);
        self.rr(Opcode::AND, t, d, m);
        self.srli(d, d, 2);
        self.rr(Opcode::AND, d, d, m);
        self.rr(Opcode::ADD, d, d, t);
        self.mov_imm(G2, 0x0F0F_0F0F_0F0F_0F0Fu64 as i64);
        self.srli(t, d, 4);
        self.rr(Opcode::ADD, d, d, t);
        self.rr(Opcode::AND, d, d, m);
        self.srli(t, d, 8);
        self.rr(Opcode::ADD, d, d, t);
        self.srli(t, d, 16);
        self.rr(Opcode::ADD, d, d, t);
        self.srli(t, d, 32);
        self.rr(Opcode::ADD, d, d, t);
        self.ri(Opcode::ANDI, d, d, 127);
    }

    fn intset_rr(&mut self, cc: IntCc, d: Gpr, l: Gpr, r: Gpr) {
        match cc {
            IntCc::Eq => {
                self.rr(Opcode::XOR, d, l, r);
                self.seqz(d, d);
            }
            IntCc::Ne => {
                self.rr(Opcode::XOR, d, l, r);
                self.snez(d, d);
            }
            IntCc::Lt => self.rr(Opcode::SLT, d, l, r),
            IntCc::Ge => {
                self.rr(Opcode::SLT, d, l, r);
                self.ri(Opcode::XORI, d, d, 1);
            }
            IntCc::Gt => self.rr(Opcode::SLT, d, r, l),
            IntCc::Le => {
                self.rr(Opcode::SLT, d, r, l);
                self.ri(Opcode::XORI, d, d, 1);
            }
            IntCc::Lo => self.rr(Opcode::SLTU, d, l, r),
            IntCc::Hs => {
                self.rr(Opcode::SLTU, d, l, r);
                self.ri(Opcode::XORI, d, d, 1);
            }
            IntCc::Hi => self.rr(Opcode::SLTU, d, r, l),
            IntCc::Ls => {
                self.rr(Opcode::SLTU, d, r, l);
                self.ri(Opcode::XORI, d, d, 1);
            }
        }
    }

    fn canon_lane(&mut self, v: Gpr, w: Width, signed: bool) {
        match (signed, w) {
            (_, Width::B64) => {}
            (false, Width::B8) => self.ri(Opcode::ANDI, v, v, 255),
            (false, Width::B16) => {
                self.slli(v, v, 48);
                self.srli(v, v, 48);
            }
            (false, _) => {
                self.slli(v, v, 32);
                self.srli(v, v, 32);
            }
            (true, Width::B8) => {
                self.slli(v, v, 56);
                self.srai(v, v, 56);
            }
            (true, Width::B16) => {
                self.slli(v, v, 48);
                self.srai(v, v, 48);
            }
            (true, _) => {
                self.slli(v, v, 32);
                self.srai(v, v, 32);
            }
        }
    }

    fn e_intset(
        &mut self,
        cc: IntCc,
        w: Width,
        dst: &Op,
        lhs: &Op,
        rhs: &Op,
    ) -> Result<(), LowerError> {
        let l = self.load_op_gpr(lhs, w, G1)?;
        let rhs_needs_scratch = !matches!(rhs, Op::Gpr(_));
        let d = match dst {
            Op::Gpr(d) => *d,
            Op::Mem(_) => G2,
            _ => return Err(self.bad("compare-set needs a register or memory destination")),
        };
        let signed = matches!(cc, IntCc::Gt | IntCc::Ge | IntCc::Lt | IntCc::Le);
        if rhs_needs_scratch && l == G1 {
            self.ri(Opcode::ADDI, SP, SP, -8);
            self.store(Opcode::SD, l, SP, 0);
            let r = self.load_op_gpr(rhs, w, G1)?;
            self.load(Opcode::LD, l, SP, 0);
            self.ri(Opcode::ADDI, SP, SP, 8);
            self.canon_lane(l, w, signed);
            self.canon_lane(r, w, signed);
            self.intset_rr(cc, d, l, r);
        } else {
            let r = self.load_op_gpr(rhs, w, G1)?;
            self.canon_lane(l, w, signed);
            self.canon_lane(r, w, signed);
            self.intset_rr(cc, d, l, r);
        }
        match dst {
            Op::Mem(a) => self.e_store(w, &Op::Gpr(G2), a),
            _ => Ok(()),
        }
    }

    fn test_value(&mut self, w: Width, value: &Op, mask: Option<&Op>) -> Result<Gpr, LowerError> {
        let lw = if w == Width::B64 { w } else { Width::B32 };
        let v = match value {
            Op::Gpr(r) => *r,
            Op::Mem(a) => {
                self.e_load(lw, Sx::Zero, G1, a)?;
                G1
            }
            Op::Imm(vv) => {
                self.mov_imm_w(G1, lw, *vv);
                G1
            }
            Op::Sym(_) => return Err(self.sym_err()),
            _ => return Err(self.bad("test needs a register, memory, or immediate value")),
        };
        let Some(m) = mask else {
            return Ok(v);
        };
        let mv = match m {
            Op::Gpr(r) => *r,
            _ if v == G1 => self.load_op_gpr(m, Width::B32, G2)?,
            _ => self.load_op_gpr(m, Width::B32, G1)?,
        };
        if v == G1 {
            self.rr(Opcode::AND, G1, G1, mv);
            Ok(G1)
        } else {
            self.rr(Opcode::AND, G2, v, mv);
            Ok(G2)
        }
    }

    fn sign_bit(&mut self, v: Gpr, bits: u32) {
        if bits == 64 {
            self.ri(Opcode::SLTI, G2, v, 0);
        } else {
            self.srli(G2, v, i64::from(bits) - 1);
            self.ri(Opcode::ANDI, G2, G2, 1);
        }
    }

    fn e_testset(
        &mut self,
        w: Width,
        value: &Op,
        mask: Option<&Op>,
        test: TestKind,
        dst: &Op,
    ) -> Result<(), LowerError> {
        let v = self.test_value(w, value, mask)?;
        match test {
            TestKind::Zero => self.seqz(G2, v),
            TestKind::NonZero => self.snez(G2, v),
            TestKind::Sign => self.sign_bit(v, lane_bits(w)),
        }
        match dst {
            Op::Gpr(d) => {
                self.mov_reg(*d, G2, Width::B64);
                Ok(())
            }
            Op::Mem(a) => self.e_store(w, &Op::Gpr(G2), a),
            _ => Err(self.bad("test-set needs a register or memory destination")),
        }
    }

    fn emit_cond_branch(
        &mut self,
        eq: bool,
        v: Gpr,
        target: Label,
        patch: bool,
    ) -> Option<PatchHandle> {
        if patch {
            let skip = self.fresh();
            self.br(if eq { Opcode::BNE } else { Opcode::BEQ }, v, X0, skip);
            let h = self.patch_j(target);
            self.bind(skip);
            return Some(h);
        }
        self.br(if eq { Opcode::BEQ } else { Opcode::BNE }, v, X0, target);
        None
    }

    #[allow(clippy::too_many_arguments)]
    fn e_testbranch(
        &mut self,
        w: Width,
        value: &Op,
        mask: Option<&Op>,
        test: TestKind,
        target: Lbl,
        patch: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        let v = self.test_value(w, value, mask)?;
        let t = self.label(target);
        let v = if test == TestKind::Sign {
            self.sign_bit(v, lane_bits(w));
            G2
        } else {
            v
        };
        Ok(self.emit_cond_branch(test == TestKind::Zero, v, t, patch))
    }

    fn branch_side(&mut self, op: &Op, w: Width, cc: IntCc, tmp: Gpr) -> Result<Gpr, LowerError> {
        let r = self.load_op_gpr(op, if w == Width::B64 { w } else { Width::B32 }, tmp)?;
        if matches!(cc, IntCc::Gt | IntCc::Ge | IntCc::Lt | IntCc::Le) {
            match w {
                Width::B8 => {
                    self.slli(tmp, r, 56);
                    self.srai(tmp, r, 56);
                    return Ok(tmp);
                }
                Width::B16 => {
                    self.slli(tmp, r, 48);
                    self.srai(tmp, r, 48);
                    return Ok(tmp);
                }
                Width::B32 => {
                    self.slli(tmp, r, 32);
                    self.srai(tmp, tmp, 32);
                    return Ok(tmp);
                }
                Width::B64 => {}
            }
        }
        Ok(r)
    }

    fn emit_branch_cc_raw(&mut self, cc: IntCc, l: Gpr, r: Gpr, t: Label) {
        match cc {
            IntCc::Eq => self.br(Opcode::BEQ, l, r, t),
            IntCc::Ne => self.br(Opcode::BNE, l, r, t),
            IntCc::Lt => self.br(Opcode::BLT, l, r, t),
            IntCc::Ge => self.br(Opcode::BGE, l, r, t),
            IntCc::Lo => self.br(Opcode::BLTU, l, r, t),
            IntCc::Hs => self.br(Opcode::BGEU, l, r, t),
            IntCc::Gt => self.br(Opcode::BLT, r, l, t),
            IntCc::Le => self.br(Opcode::BGE, r, l, t),
            IntCc::Hi => self.br(Opcode::BLTU, r, l, t),
            IntCc::Ls => self.br(Opcode::BGEU, r, l, t),
        }
    }

    fn emit_branch_cc(
        &mut self,
        cc: IntCc,
        l: Gpr,
        r: Gpr,
        t: Label,
        patch: bool,
    ) -> Option<PatchHandle> {
        if patch {
            let skip = self.fresh();
            self.emit_branch_cc_raw(flip_cc(cc), l, r, skip);
            let h = self.patch_j(t);
            self.bind(skip);
            return Some(h);
        }
        self.emit_branch_cc_raw(cc, l, r, t);
        None
    }

    #[allow(clippy::too_many_arguments)]
    fn e_branch(
        &mut self,
        cc: IntCc,
        w: Width,
        lhs: &Op,
        rhs: &Op,
        target: Lbl,
        patch: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        let (cc, lhs, rhs) = match (lhs, rhs) {
            (Op::Imm(_), Op::Gpr(_)) | (Op::Imm(_), Op::Mem(_)) => (flip_cc(cc), rhs, lhs),
            _ => (cc, lhs, rhs),
        };
        let l = self.branch_side(lhs, w, cc, G1)?;
        let r = self.branch_side(rhs, w, cc, if l == G1 { G2 } else { G1 })?;
        let t = self.label(target);
        Ok(self.emit_branch_cc(cc, l, r, t, patch))
    }

    fn flag_op(&mut self, op: &Op, w: Width, tmp: Gpr) -> Result<Gpr, LowerError> {
        let lw = if w == Width::B64 { w } else { Width::B32 };
        match op {
            Op::Gpr(r) => Ok(*r),
            Op::Imm(v) => {
                self.mov_imm_w(tmp, lw, *v);
                Ok(tmp)
            }
            Op::Sym(_) => Err(self.sym_err()),
            Op::Mem(a) => {
                self.e_load(lw, Sx::Zero, tmp, a)?;
                Ok(tmp)
            }
            _ => Err(self.bad("flag ALU needs a register, memory, or immediate operand")),
        }
    }

    fn stash_a(&mut self, a: &Op) -> Result<(), LowerError> {
        match a {
            Op::Gpr(r) => self.mov_reg(G2, *r, Width::B64),
            Op::Imm(v) => self.mov_imm(G2, *v),
            Op::Sym(_) => return Err(self.sym_err()),
            Op::Mem(m) => self.e_load(Width::B64, Sx::Zero, G2, m)?,
            _ => return Err(self.bad("flag ALU needs a register, memory, or immediate operand")),
        }
        Ok(())
    }

    fn flags_zn(&mut self, t: Gpr, bits: u32) {
        self.seqz(FLAGS, t);
        if bits == 64 {
            self.ri(Opcode::SLTI, G1, t, 0);
        } else {
            self.srli(G1, t, i64::from(bits) - 1);
            self.ri(Opcode::ANDI, G1, G1, 1);
        }
        self.slli(G1, G1, 1);
        self.rr(Opcode::OR, FLAGS, FLAGS, G1);
    }

    fn derive_addsub_64(&mut self, sub: bool, r: Gpr, a: Gpr, b: Gpr) {
        let (fr, tv) = (FLAGS, G1);
        // C (bit 2): carry (`r < a`, unsigned) / not-borrow (`!(a < b)`).
        if sub {
            self.rr(Opcode::SLTU, fr, a, b);
            self.ri(Opcode::XORI, fr, fr, 1);
        } else {
            self.rr(Opcode::SLTU, fr, r, a);
        }
        self.slli(fr, fr, 2);
        // V (bit 3): sign((a ^ b) & (a ^ r)) for Sub, sign((~(a ^ b)) &
        // (a ^ r)) for Add.
        self.rr(Opcode::XOR, tv, a, b);
        if !sub {
            self.ri(Opcode::XORI, tv, tv, -1);
        }
        self.rr(Opcode::XOR, a, a, r);
        self.rr(Opcode::AND, tv, tv, a);
        self.srli(tv, tv, 63);
        self.slli(tv, tv, 3);
        self.rr(Opcode::OR, fr, fr, tv);
        // Z (bit 0) / N (bit 1) from the result.
        self.seqz(tv, r);
        self.ri(Opcode::SLTI, a, r, 0);
        self.slli(a, a, 1);
        self.rr(Opcode::OR, tv, tv, a);
        self.rr(Opcode::OR, fr, fr, tv);
    }

    fn derive_addsub_narrow(&mut self, sub: bool, mask: i64, bits: u32) {
        let sh = 64 - i64::from(bits);
        let (a, b, fr) = (G2, G1, FLAGS);
        // Widen both sides (sign-extended exact) and get the exact sum.
        self.slli(a, a, sh);
        self.srai(a, a, sh);
        self.slli(b, b, sh);
        self.srai(b, b, sh);
        self.rr(if sub { Opcode::SUB } else { Opcode::ADD }, fr, a, b);
        self.ri(Opcode::ADDI, SP, SP, -16);
        self.store(Opcode::SD, fr, SP, 0);
        // C from the zero-extended values: carry out (Add) / not-borrow (Sub).
        self.mov_imm(FLAGS, mask);
        self.rr(Opcode::AND, a, a, fr);
        self.rr(Opcode::AND, b, b, fr);
        if sub {
            self.rr(Opcode::SLTU, b, a, b);
            self.ri(Opcode::XORI, b, b, 1);
        } else {
            self.rr(Opcode::ADD, b, a, b);
            self.srli(b, b, i64::from(bits));
            self.ri(Opcode::ANDI, b, b, 1);
        }
        self.slli(fr, b, 2);
        // V = (sext(trunc(sum)) != sum). `G2` holds the mask.
        self.load(Opcode::LD, b, SP, 0);
        self.mov_imm(G2, mask);
        self.rr(Opcode::AND, b, b, a);
        self.slli(a, b, sh);
        self.srai(a, a, sh);
        self.load(Opcode::LD, b, SP, 0);
        self.rr(Opcode::XOR, b, a, b);
        self.snez(b, b);
        self.slli(b, b, 3);
        self.rr(Opcode::OR, fr, fr, b);
        // Z / N from the truncated lane.
        self.load(Opcode::LD, b, SP, 0);
        self.mov_imm(G2, mask);
        self.rr(Opcode::AND, b, b, a);
        self.srli(a, b, i64::from(bits) - 1);
        self.ri(Opcode::ANDI, a, a, 1);
        self.slli(a, a, 1);
        self.seqz(b, b);
        self.rr(Opcode::OR, b, b, a);
        self.rr(Opcode::OR, fr, fr, b);
        self.ri(Opcode::ADDI, SP, SP, 16);
    }

    fn pin_b(&mut self, a_op: &Op, b_op: &Op, dst: Gpr) -> BSide {
        match b_op {
            Op::Gpr(r) if *r == dst => {
                if matches!(a_op, Op::Gpr(ag) if *ag == dst) {
                    BSide::SameAsA
                } else {
                    self.mov_reg(FLAGS, dst, Width::B64);
                    BSide::Snap
                }
            }
            _ => BSide::Op,
        }
    }

    fn derive_reg(
        &mut self,
        sub: bool,
        w: Width,
        b_op: &Op,
        bside: BSide,
        r: Gpr,
    ) -> Result<(), LowerError> {
        let b = match bside {
            BSide::Snap => {
                self.mov_reg(G1, FLAGS, Width::B64);
                G1
            }
            BSide::SameAsA => G2,
            BSide::Op => self.flag_op(b_op, w, G1)?,
        };
        if w == Width::B64 {
            self.derive_addsub_64(sub, r, G2, b);
            return Ok(());
        }

        self.mov_reg(G1, b, Width::B64);
        self.derive_addsub_narrow(sub, lane_mask(w), lane_bits(w));
        Ok(())
    }

    fn e_alus(&mut self, op: AluOp, w: Width, alu: &Alu3) -> Result<(), LowerError> {
        let k = match op {
            AluOp::Add => AluKind::Add,
            AluOp::Sub => AluKind::Sub,
            AluOp::Or => AluKind::Or,
        };
        let ops = alu_args(alu);
        let mem_dst = ops.last().is_some_and(|o| matches!(o, Op::Mem(_)));
        let (a_op, b_op) = match ops.as_slice() {
            [rhs, dst] => (*dst, *rhs),
            [lhs, rhs, _] => (*lhs, *rhs),
            _ => return Err(self.bad("flag ALU takes 2 or 3 operands")),
        };
        let needs_ab = k == AluKind::Add || k == AluKind::Sub;
        let mut bside = BSide::Op;
        if needs_ab && !mem_dst {
            self.stash_a(&a_op)?;
            if let Some(Op::Gpr(d)) = ops.last() {
                bside = self.pin_b(&a_op, &b_op, *d);
            }
        }
        self.op_n(k, w, &ops)?;
        if mem_dst {
            if needs_ab {
                return Err(
                    self.bad("flag-setting add/sub over memory cannot persist carry/overflow")
                );
            }
            let Some(Op::Mem(a)) = ops.last() else {
                return Err(self.bad("flag ALU takes 2 or 3 operands"));
            };
            let lw = if w == Width::B64 { w } else { Width::B32 };
            self.e_load(lw, Sx::Zero, G1, a)?;
            let bits = lane_bits(w);
            if bits == 64 {
                self.flags_zn(G1, 64);
            } else {
                self.mov_imm(G2, lane_mask(w));
                self.rr(Opcode::AND, G1, G1, G2);
                self.flags_zn(G1, bits);
            }
            return Ok(());
        }
        if k == AluKind::Or {
            let bits = lane_bits(w);
            let Some(Op::Gpr(d)) = ops.last() else {
                return Err(self.bad("flag ALU takes 2 or 3 operands"));
            };
            let d = *d;
            if bits != 64 {
                self.mov_imm(G1, lane_mask(w));
                self.rr(Opcode::AND, G1, d, G1);
                self.flags_zn(G1, bits);
            } else {
                self.flags_zn(d, 64);
            }
            return Ok(());
        }
        let Some(Op::Gpr(r)) = ops.last() else {
            return Err(self.bad("flag ALU takes 2 or 3 operands"));
        };
        let r = *r;
        self.derive_reg(k == AluKind::Sub, w, &b_op, bside, r)
    }

    fn branch_flag(
        &mut self,
        bit: u32,
        taken_if_set: bool,
        target: Label,
        patch: bool,
    ) -> Option<PatchHandle> {
        self.ri(Opcode::ANDI, G1, FLAGS, 1i64 << bit);
        if patch {
            let skip = self.fresh();
            self.br(
                if taken_if_set {
                    Opcode::BEQ
                } else {
                    Opcode::BNE
                },
                G1,
                X0,
                skip,
            );
            let h = self.patch_j(target);
            self.bind(skip);
            return Some(h);
        }
        self.br(
            if taken_if_set {
                Opcode::BNE
            } else {
                Opcode::BEQ
            },
            G1,
            X0,
            target,
        );
        None
    }

    fn e_flagbranch(&mut self, flag: PredFlag, target: Lbl, patch: bool) -> Option<PatchHandle> {
        let (bit, set) = match flag {
            PredFlag::O => (3, true),
            PredFlag::S => (1, true),
            PredFlag::Z => (0, true),
            PredFlag::Nz => (0, false),
        };
        let t = self.label(target);
        self.branch_flag(bit, set, t, patch)
    }

    /// Branch to `target` when `cond` holds of `v`.
    fn branch_zero(
        &mut self,
        v: Gpr,
        cond: ZCond,
        target: Label,
        patch: bool,
    ) -> Option<PatchHandle> {
        let (taken, inverse) = match cond {
            ZCond::Eqz => (Opcode::BEQ, Opcode::BNE),
            ZCond::Nez => (Opcode::BNE, Opcode::BEQ),
            ZCond::Ltz => (Opcode::BLT, Opcode::BGE),
        };
        if patch {
            let skip = self.fresh();
            self.br(inverse, v, X0, skip);
            let h = self.patch_j(target);
            self.bind(skip);
            return Some(h);
        }
        self.br(taken, v, X0, target);
        None
    }

    /// Leave a nonzero value in `FLAGS` iff `a OP b` overflows (signed, at
    /// width `w`),.
    fn overflow_precheck(
        &mut self,
        k: AluKind,
        w: Width,
        a_op: &Op,
        b_op: &Op,
    ) -> Result<(), LowerError> {
        let lw = if w == Width::B64 { w } else { Width::B32 };
        let imm_ok = |v: i64| match k {
            AluKind::Sub => fits12(-v),
            AluKind::Add => fits12(v),
            _ => false,
        };

        let mut b_normalized = false;
        let b = match b_op {
            Op::Gpr(r) => OvfB::Reg(*r),
            Op::Imm(v) => {
                let v = if w == Width::B64 {
                    *v
                } else {
                    i64::from(*v as i32)
                };
                if imm_ok(v) {
                    OvfB::Imm(v)
                } else {
                    self.mov_imm(G2, v);
                    b_normalized = true;
                    OvfB::Reg(G2)
                }
            }
            Op::Sym(_) => return Err(self.sym_err()),
            Op::Mem(m) => {
                self.e_load(lw, Sx::Zero, G2, m)?;
                OvfB::Reg(G2)
            }
            _ => return Err(self.bad("op-branch needs register, memory, or immediate operands")),
        };
        let a = match a_op {
            Op::Gpr(r) => *r,
            Op::Imm(v) => {
                self.mov_imm(G1, *v);
                G1
            }
            Op::Sym(_) => return Err(self.sym_err()),
            Op::Mem(m) => {
                self.e_load(lw, Sx::Zero, G1, m)?;
                G1
            }
            _ => return Err(self.bad("op-branch needs register, memory, or immediate operands")),
        };
        if w == Width::B32 {
            self.ri(Opcode::ADDIW, G1, a, 0);
            let rb = match b {
                OvfB::Reg(r) => {
                    if b_normalized {
                        r
                    } else {
                        self.ri(Opcode::ADDIW, G2, r, 0);
                        G2
                    }
                }
                OvfB::Imm(_) => G2, // unused
            };
            match (k, b) {
                (AluKind::Add, OvfB::Imm(v)) => self.ri(Opcode::ADDI, FLAGS, G1, v),
                (AluKind::Sub, OvfB::Imm(v)) => self.ri(Opcode::ADDI, FLAGS, G1, -v),
                (AluKind::Add, _) => self.rr(Opcode::ADD, FLAGS, G1, rb),
                (AluKind::Sub, _) => self.rr(Opcode::SUB, FLAGS, G1, rb),
                (AluKind::Mul, OvfB::Reg(_)) => self.rr(Opcode::MUL, FLAGS, G1, rb),
                _ => return Err(self.bad("overflow check is add/sub/mul only")),
            }
            self.ri(Opcode::ADDIW, G1, FLAGS, 0);
            self.rr(Opcode::XOR, FLAGS, FLAGS, G1);
            return Ok(());
        }
        match k {
            AluKind::Add | AluKind::Sub => {
                let sub = k == AluKind::Sub;
                match b {
                    OvfB::Reg(r) => {
                        self.rr(if sub { Opcode::SUB } else { Opcode::ADD }, FLAGS, a, r);
                    }
                    OvfB::Imm(v) => self.ri(Opcode::ADDI, FLAGS, a, if sub { -v } else { v }),
                }
                self.rr(Opcode::SLT, FLAGS, FLAGS, a); // r < a
                match b {
                    OvfB::Reg(r) => {
                        if sub {
                            self.rr(Opcode::SLT, G2, X0, r); // b > 0
                        } else {
                            self.ri(Opcode::SLTI, G2, r, 0); // b < 0
                        }
                        self.rr(Opcode::XOR, FLAGS, FLAGS, G2);
                    }
                    OvfB::Imm(v) => {
                        if (sub && v > 0) || (!sub && v < 0) {
                            self.ri(Opcode::XORI, FLAGS, FLAGS, 1);
                        }
                    }
                }
            }
            AluKind::Mul => {
                let OvfB::Reg(r) = b else {
                    unreachable!("mul immediates are always materialized")
                };
                self.rr(Opcode::MULH, FLAGS, a, r);
                self.rr(Opcode::MUL, G1, a, r);
                self.srai(G1, G1, 63);
                self.rr(Opcode::XOR, FLAGS, FLAGS, G1);
            }
            _ => return Err(self.bad("overflow check is add/sub/mul only")),
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn e_opbranch(
        &mut self,
        op: FlagAlu,
        w: Width,
        flag: PredFlag,
        args: &[Op],
        target: Lbl,
        patch: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        let k = match op {
            FlagAlu::Add => AluKind::Add,
            FlagAlu::Sub => AluKind::Sub,
            FlagAlu::Mul => AluKind::Mul,
            FlagAlu::Or => AluKind::Or,
        };
        if w == Width::B8 || w == Width::B16 {
            return Err(self.bad("op-branch is defined for 32- and 64-bit widths only"));
        }
        let (a_op, b_op, dst_op) = match args {
            [rhs, dst] => (*dst, *rhs, *dst),
            [lhs, rhs, dst] => (*lhs, *rhs, *dst),
            _ => return Err(self.bad(format!("expected 2 or 3 operands, got {}", args.len()))),
        };
        let t = self.label(target);
        if flag == PredFlag::O {
            if k == AluKind::Or {
                if patch {
                    return Err(LowerError::NotPatchable(self.mn.to_string()));
                }
                self.op_n(k, w, args)?;
                return Ok(None);
            }
            self.overflow_precheck(k, w, &a_op, &b_op)?;
            self.op_n(k, w, args)?;
            return Ok(self.branch_zero(FLAGS, ZCond::Nez, t, patch));
        }
        self.op_n(k, w, args)?;
        let mut v = match dst_op {
            Op::Gpr(d) => d,
            Op::Mem(m) => {
                self.e_load(w, Sx::Sign, G1, &m)?;
                G1
            }
            _ => return Err(self.bad("op-branch destination must be a register or memory")),
        };
        let cond = match flag {
            PredFlag::Z => ZCond::Eqz,
            PredFlag::Nz => ZCond::Nez,
            _ => ZCond::Ltz,
        };
        if cond == ZCond::Ltz && w == Width::B32 && matches!(dst_op, Op::Gpr(_)) {
            self.ri(Opcode::ADDIW, G1, v, 0);
            v = G1;
        }
        Ok(self.branch_zero(v, cond, t, patch))
    }

    fn e_adc_sbb(&mut self, dst: &Op, src: &Op, borrow: bool) -> Result<(), LowerError> {
        let arith = if borrow { Opcode::SUB } else { Opcode::ADD };
        self.ri(Opcode::ADDI, SP, SP, -48);
        self.srli(G2, FLAGS, 2);
        self.ri(Opcode::ANDI, G2, G2, 1);
        if borrow {
            self.ri(Opcode::XORI, G2, G2, 1);
        }
        self.store(Opcode::SD, G2, SP, 16);
        match src {
            Op::Gpr(s) => self.store(Opcode::SD, *s, SP, 8),
            Op::Imm(v) => {
                if !Width::B32.fits(*v) {
                    return Err(self.bad("adc/sbb immediate must fit in 32 bits"));
                }
                self.mov_imm(G2, *v);
                self.store(Opcode::SD, G2, SP, 8);
            }
            Op::Sym(_) => return Err(self.sym_err()),
            Op::Mem(a) => {
                self.e_load(Width::B64, Sx::Zero, G2, a)?;
                self.store(Opcode::SD, G2, SP, 8);
            }
            _ => return Err(self.bad("adc/sbb needs register/memory operands")),
        }
        let r = match dst {
            Op::Gpr(d) => {
                let d = *d;
                self.store(Opcode::SD, d, SP, 0);
                self.load(Opcode::LD, G2, SP, 8);
                self.rr(arith, d, d, G2);
                self.load(Opcode::LD, G2, SP, 16);
                self.rr(arith, d, d, G2);
                d
            }
            Op::Mem(a) => {
                if a.index.is_some() || !fits_d12(a.disp.const_or_zero()) {
                    return Err(
                        self.bad("adc/sbb memory destination needs a directly encodable address")
                    );
                }
                self.e_load(Width::B64, Sx::Zero, G2, a)?;
                self.store(Opcode::SD, G2, SP, 0);
                self.load(Opcode::LD, G1, SP, 8);
                self.load(Opcode::LD, G2, SP, 16);
                self.rr(arith, G1, G1, G2);
                self.load(Opcode::LD, G2, SP, 8);
                self.rr(arith, G1, G1, G2);
                self.e_store(Width::B64, &Op::Gpr(G1), a)?;
                G1
            }
            _ => return Err(self.bad("adc/sbb needs register/memory operands")),
        };
        self.derive_adc_sbb_64(borrow, r);
        self.ri(Opcode::ADDI, SP, SP, 48);
        Ok(())
    }

    fn derive_adc_sbb_64(&mut self, sub: bool, r: Gpr) {
        let (tmp, fr) = (G2, FLAGS);
        // V.
        self.load(Opcode::LD, fr, SP, 0);
        self.load(Opcode::LD, tmp, SP, 8);
        self.rr(Opcode::XOR, fr, fr, tmp);
        if !sub {
            self.ri(Opcode::XORI, fr, fr, -1);
        }
        self.load(Opcode::LD, tmp, SP, 0);
        self.rr(Opcode::XOR, tmp, tmp, r);
        self.rr(Opcode::AND, fr, fr, tmp);
        self.srai(fr, fr, 63);
        self.ri(Opcode::ANDI, fr, fr, 1);
        self.slli(fr, fr, 3);
        self.store(Opcode::SD, fr, SP, 24);
        // C / not-borrow.
        self.load(Opcode::LD, tmp, SP, 16);
        if sub {
            self.load(Opcode::LD, fr, SP, 0);
            self.load(Opcode::LD, tmp, SP, 8);
            self.rr(Opcode::SLTU, fr, fr, tmp);
            self.store(Opcode::SD, fr, SP, 32);
            self.load(Opcode::LD, fr, SP, 0);
            self.load(Opcode::LD, tmp, SP, 8);
            self.rr(Opcode::SUB, fr, fr, tmp);
            self.load(Opcode::LD, tmp, SP, 16);
            self.rr(Opcode::SLTU, fr, fr, tmp);
            self.load(Opcode::LD, tmp, SP, 32);
            self.rr(Opcode::OR, fr, fr, tmp);
            self.ri(Opcode::XORI, fr, fr, 1);
        } else {
            self.load(Opcode::LD, fr, SP, 0);
            self.rr(Opcode::ADD, fr, fr, tmp);
            self.rr(Opcode::SLTU, tmp, fr, tmp);
            self.rr(Opcode::SLTU, fr, r, fr);
            self.rr(Opcode::OR, fr, tmp, fr);
        }
        self.slli(fr, fr, 2);
        self.load(Opcode::LD, tmp, SP, 24);
        self.rr(Opcode::OR, fr, fr, tmp);
        // Z / N from the result.
        self.seqz(tmp, r);
        self.store(Opcode::SD, fr, SP, 32);
        self.ri(Opcode::SLTI, fr, r, 0);
        self.slli(fr, fr, 1);
        self.rr(Opcode::OR, tmp, tmp, fr);
        self.load(Opcode::LD, fr, SP, 32);
        self.rr(Opcode::OR, fr, fr, tmp);
    }

    fn spill_ra(&mut self) {
        self.ri(Opcode::ADDI, SP, SP, -16);
        self.store(Opcode::SD, RA, SP, 0);
    }

    fn unspill_ra(&mut self) {
        self.load(Opcode::LD, RA, SP, 0);
        self.ri(Opcode::ADDI, SP, SP, 16);
    }

    fn e_jmp_call(
        &mut self,
        target: &IrTarget,
        patch: bool,
        is_call: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        if patch && !matches!(target, IrTarget::Label(_)) {
            return Err(LowerError::NotPatchable(self.mn.to_string()));
        }
        let reg = match target {
            IrTarget::Label(l) => {
                let t = self.label(*l);
                if !is_call {
                    if patch {
                        return Ok(Some(self.patch_j(t)));
                    }
                    self.j(t);
                    return Ok(None);
                }
                self.spill_ra();
                let h = if patch {
                    Some(PatchHandle::Jump(self.asm.patchable_call(t)))
                } else {
                    // `call label`: `auipc ra` + `jalr ra`.
                    self.asm.call(t);
                    None
                };
                self.unspill_ra();
                return Ok(h);
            }
            IrTarget::Reg(r) => *r,
            IrTarget::Mem(a) => {
                self.e_load(Width::B64, Sx::Zero, G1, a)?;
                G1
            }
            IrTarget::Abs(v) => {
                self.mov_imm(G1, *v);
                G1
            }
            IrTarget::Extern(e) if e.reach == Reach::Near => {
                if is_call {
                    self.spill_ra();
                    self.extern_call_plt(*e, true);
                    self.unspill_ra();
                } else {
                    self.extern_call_plt(*e, false);
                }
                return Ok(None);
            }
            IrTarget::Extern(e) => {
                self.extern_address(G1, *e);
                G1
            }
        };
        if is_call {
            self.spill_ra();
            self.ri(Opcode::JALR, RA, reg, 0);
            self.unspill_ra();
        } else {
            self.ri(Opcode::JALR, X0, reg, 0);
        }
        Ok(None)
    }

    fn e_push_pop(&mut self, op: &Op, push: bool) -> Result<(), LowerError> {
        let Op::Gpr(r) = op else {
            return Err(self.bad("push/pop needs a GPR operand"));
        };
        if push {
            self.ri(Opcode::ADDI, SP, SP, -8);
            self.store(Opcode::SD, *r, SP, 0);
        } else {
            self.load(Opcode::LD, *r, SP, 0);
            self.ri(Opcode::ADDI, SP, SP, 8);
        }
        Ok(())
    }

    fn e_push_pop_v(&mut self, fr: Fpr, push: bool) -> Result<(), LowerError> {
        let hi = fhi(self.mn, fr)?;
        if push {
            self.ri(Opcode::ADDI, SP, SP, -16);
            self.fstore(Opcode::FSD, fr, SP, 0);
            self.fstore(Opcode::FSD, hi, SP, 8);
        } else {
            self.fload(Opcode::FLD, fr, SP, 0);
            self.fload(Opcode::FLD, hi, SP, 8);
            self.ri(Opcode::ADDI, SP, SP, 16);
        }
        Ok(())
    }

    fn e_peek_poke(&mut self, disp: i32, reg: Gpr, load: bool) {
        if fits_d12(disp) {
            if load {
                self.load(Opcode::LD, reg, SP, i64::from(disp));
            } else {
                self.store(Opcode::SD, reg, SP, i64::from(disp));
            }
            return;
        }
        self.mov_imm(G1, i64::from(disp));
        self.rr(Opcode::ADD, G1, G1, SP);
        if load {
            self.load(Opcode::LD, reg, G1, 0);
        } else {
            self.store(Opcode::SD, reg, G1, 0);
        }
    }

    fn e_mulwide(&mut self, signed: bool, dst: Gpr, lhs: Gpr, rhs: Gpr) {
        let (a, b) = (G1, G2);
        self.slli(a, lhs, 32);
        self.slli(b, rhs, 32);
        if signed {
            self.srai(a, a, 32);
            self.srai(b, b, 32);
        } else {
            self.srli(a, a, 32);
            self.srli(b, b, 32);
        }
        self.rr(Opcode::MUL, dst, a, b);
    }

    fn e_divmod1(&mut self, signed: bool, w: Width, divisor: &Op) -> Result<(), LowerError> {
        if w != Width::B32 && w != Width::B64 {
            return Err(self.bad("div needs 32/64-bit widths"));
        }
        let Op::Gpr(dvs) = *divisor else {
            return Err(self.bad("1-op divide needs a register divisor"));
        };
        let trap = self.fresh();
        let done = self.fresh();
        if w == Width::B64 {
            self.br(Opcode::BEQ, dvs, X0, trap);
        } else {
            self.slli(G1, dvs, 32);
            self.srai(G1, G1, 32);
            self.br(Opcode::BEQ, G1, X0, trap);
        }
        if signed {
            let bound = if w == Width::B64 {
                i64::MIN
            } else {
                i64::from(i32::MIN)
            };
            self.mov_imm(G1, bound);
            let no_trap = self.fresh();
            if w == Width::B64 {
                self.br(Opcode::BNE, T0, G1, no_trap);
                self.ri(Opcode::ADDI, G1, X0, -1);
                self.br(Opcode::BNE, dvs, G1, no_trap);
            } else {
                self.slli(G2, T0, 32);
                self.srai(G2, G2, 32);
                self.br(Opcode::BNE, G2, G1, no_trap);
                self.slli(G2, dvs, 32);
                self.srai(G2, G2, 32);
                self.ri(Opcode::ADDI, G1, X0, -1);
                self.br(Opcode::BNE, G2, G1, no_trap);
            }
            self.j(trap);
            self.bind(no_trap);
        }
        self.mov_reg(G1, T0, if w == Width::B64 { w } else { Width::B32 });
        let (div, rem) = match (w == Width::B64, signed) {
            (true, true) => (Opcode::DIV, Opcode::REM),
            (true, false) => (Opcode::DIVU, Opcode::REMU),
            (false, true) => (Opcode::DIVW, Opcode::REMW),
            (false, false) => (Opcode::DIVUW, Opcode::REMUW),
        };
        self.rr(div, T0, T0, dvs);
        self.rr(rem, T2, G1, dvs);
        self.j(done);
        self.bind(trap);
        self.e(Opcode::EBREAK, &[]);
        self.bind(done);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn e_cmov(
        &mut self,
        w: Width,
        zero: bool,
        dst: Gpr,
        src: &Op,
        test: Gpr,
    ) -> Result<(), LowerError> {
        let done = self.fresh();
        self.br(if zero { Opcode::BNE } else { Opcode::BEQ }, test, X0, done);
        match src {
            Op::Gpr(r) => self.mov_reg(dst, *r, w),
            Op::Imm(v) => self.mov_imm_w(dst, w, *v),
            Op::Sym(_) => return Err(self.sym_err()),
            Op::Mem(a) => {
                let lw = if w == Width::B64 { w } else { Width::B32 };
                self.e_load(lw, Sx::Zero, dst, a)?;
            }
            _ => return Err(self.bad("cmov needs a register, immediate, or memory source")),
        }
        self.bind(done);
        Ok(())
    }

    fn fp_src(&mut self, k: FKind, op: &Op) -> Result<Fpr, LowerError> {
        match op {
            Op::Fpr(r) => Ok(*r),
            Op::Mem(a) => {
                self.e_loadf(k, SF, a)?;
                Ok(SF)
            }
            Op::Imm(v) => {
                self.mov_imm(G1, *v);
                self.fmv_fx(k, SF, G1);
                Ok(SF)
            }
            Op::Sym(_) => Err(self.sym_err()),
            _ => Err(self.bad("float operand needs an FPR, memory, or immediate")),
        }
    }

    /// Move one FP register to another (`fmv.s`/`fmv.d` = `fsgnj`).
    fn rv_fmov(&mut self, k: FKind, dst: Fpr, src: Fpr) {
        if dst == src {
            return;
        }
        self.e(
            fsel(k, Opcode::FSGNJS, Opcode::FSGNJD),
            &[f(dst), f(src), f(src)],
        );
    }

    /// Materialize a memory or immediate operand into a chosen FP register.
    fn rv_stage(&mut self, k: FKind, dst: Fpr, src: &Op) -> Result<(), LowerError> {
        match src {
            Op::Fpr(r) => self.rv_fmov(k, dst, *r),
            Op::Mem(a) => self.e_loadf(k, dst, a)?,
            Op::Imm(v) => {
                self.mov_imm(G1, *v);
                self.fmv_fx(k, dst, G1);
            }
            Op::Sym(_) => return Err(self.sym_err()),
            _ => return Err(self.bad("float operand needs an FPR, memory, or immediate")),
        }
        Ok(())
    }

    fn e_farith(&mut self, op: FAlu, k: FKind, arith: &FArith3) -> Result<(), LowerError> {
        let d = arith.dst;
        let (n, m) = match &arith.rhs {
            Some(rhs) => {
                let m = match rhs {
                    Op::Fpr(r) if *r != arith.dst => *r,
                    Op::Fpr(r) => {
                        self.rv_fmov(k, SF, *r);
                        SF
                    }
                    other => {
                        self.rv_stage(k, SF, other)?;
                        SF
                    }
                };
                let n = match &arith.lhs {
                    Op::Fpr(r) => *r,
                    other => {
                        self.rv_stage(k, arith.dst, other)?;
                        arith.dst
                    }
                };
                (n, m)
            }
            None => (d, self.fp_src(k, &arith.lhs)?),
        };
        let code = match op {
            FAlu::Add => fsel(k, Opcode::FADDS, Opcode::FADDD),
            FAlu::Sub => fsel(k, Opcode::FSUBS, Opcode::FSUBD),
            FAlu::Mul => fsel(k, Opcode::FMULS, Opcode::FMULD),
            FAlu::Div => fsel(k, Opcode::FDIVS, Opcode::FDIVD),
            FAlu::Min => fsel(k, Opcode::FMINS, Opcode::FMIND),
            FAlu::Max => fsel(k, Opcode::FMAXS, Opcode::FMAXD),
        };
        if matches!(op, FAlu::Min | FAlu::Max) {
            self.e(code, &[f(d), f(n), f(m)]);
        } else {
            self.e(code, &[f(d), f(n), f(m), i(DYN)]);
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn e_fma(
        &mut self,
        op: FmaOp,
        k: FKind,
        a: &Op,
        b: &Op,
        c: &Op,
        dst: Fpr,
    ) -> Result<(), LowerError> {
        let ra = self.fp_src(k, a)?;
        let rb = self.fp_src(k, b)?;
        let rc = self.fp_src(k, c)?;
        let code = match op {
            FmaOp::Add => fsel(k, Opcode::FMADDS, Opcode::FMADDD),
            FmaOp::Sub => fsel(k, Opcode::FMSUBS, Opcode::FMSUBD),
            FmaOp::NegAdd => fsel(k, Opcode::FNMSUBS, Opcode::FNMSUBD),
            FmaOp::NegSub => fsel(k, Opcode::FNMADDS, Opcode::FNMADDD),
        };
        self.e(code, &[f(dst), f(ra), f(rb), f(rc), i(DYN)]);
        Ok(())
    }

    fn e_fbit(&mut self, or: bool, k: FKind, dst: Fpr, src: &Op) -> Result<(), LowerError> {
        let r = self.fp_src(k, src)?;
        self.fmv_xf(k, G1, dst);
        self.fmv_xf(k, G2, r);
        self.rr(if or { Opcode::OR } else { Opcode::AND }, G1, G1, G2);
        self.fmv_fx(k, dst, G1);
        Ok(())
    }

    fn e_cvtfi(&mut self, k: FKind, w: Width, dst: Gpr, src: &Op) -> Result<(), LowerError> {
        let r = self.fp_src(k, src)?;
        match w {
            Width::B32 => {
                self.e(
                    fsel(k, Opcode::FCVTWS, Opcode::FCVTWD),
                    &[g(dst), f(r), i(RTZ)],
                );
                self.mov_imm(G1, i64::from(i32::MAX));
                let done = self.fresh();
                self.br(Opcode::BNE, dst, G1, done);
                self.mov_imm(dst, i64::from(i32::MIN));
                self.bind(done);
                self.zero_upper32(dst);
            }
            Width::B64 => {
                self.e(
                    fsel(k, Opcode::FCVTLS, Opcode::FCVTLD),
                    &[g(dst), f(r), i(RTZ)],
                );
                self.mov_imm(G1, i64::MAX);
                let done = self.fresh();
                self.br(Opcode::BNE, dst, G1, done);
                self.mov_imm(dst, i64::MIN);
                self.bind(done);
            }
            _ => return Err(self.bad("float-to-int needs 32/64-bit widths")),
        }
        Ok(())
    }

    fn e_cvtif(
        &mut self,
        signed: bool,
        from: Width,
        k: FKind,
        dst: Fpr,
        src: &Op,
    ) -> Result<(), LowerError> {
        let s = self.load_op_gpr(src, from, G1)?;
        // Sub-64 signed sides sign-extend first (loads zero-extend).
        let s = if signed {
            match from {
                Width::B64 | Width::B32 => s,
                Width::B8 => {
                    self.slli(G1, s, 56);
                    self.srai(G1, G1, 56);
                    G1
                }
                Width::B16 => {
                    self.slli(G1, s, 48);
                    self.srai(G1, G1, 48);
                    G1
                }
            }
        } else {
            s
        };
        let code = match (signed, from == Width::B64, k) {
            (true, true, FKind::F32) => Opcode::FCVTSL,
            (true, true, FKind::F64) => Opcode::FCVTDL,
            (true, false, FKind::F32) => Opcode::FCVTSW,
            (true, false, FKind::F64) => Opcode::FCVTDW,
            (false, true, FKind::F32) => Opcode::FCVTSLU,
            (false, true, FKind::F64) => Opcode::FCVTDLU,
            (false, false, FKind::F32) => Opcode::FCVTSWU,
            (false, false, FKind::F64) => Opcode::FCVTDWU,
        };
        self.e(code, &[f(dst), g(s), i(DYN)]);
        Ok(())
    }

    fn e_cvtff(&mut self, from: FKind, to: FKind, dst: Fpr, src: &Op) -> Result<(), LowerError> {
        let r = self.fp_src(from, src)?;
        match (from, to) {
            (FKind::F32, FKind::F64) => self.e(Opcode::FCVTDS, &[f(dst), f(r), i(DYN)]),
            (FKind::F64, FKind::F32) => self.e(Opcode::FCVTSD, &[f(dst), f(r), i(DYN)]),
            _ => match src {
                Op::Fpr(s) => self.rv_fmov(to, dst, *s),
                _ => self.rv_fmov(to, dst, SF),
            },
        }
        Ok(())
    }

    fn e_bitcast(&mut self, dir: BitcastDir, dst: &Op, src: &Op) -> Result<(), LowerError> {
        match (dir, dst, src) {
            (BitcastDir::Q2D, Op::Fpr(d), Op::Gpr(s)) => self.fmv_fx(FKind::F64, *d, *s),
            (BitcastDir::D2Q, Op::Gpr(d), Op::Fpr(s)) => self.fmv_xf(FKind::F64, *d, *s),
            (BitcastDir::I2F, Op::Fpr(d), Op::Gpr(s)) => self.fmv_fx(FKind::F32, *d, *s),
            (BitcastDir::F2I, Op::Gpr(d), Op::Fpr(s)) => self.fmv_xf(FKind::F32, *d, *s),
            _ => return Err(self.bad("unsupported bit-cast pair")),
        }
        Ok(())
    }

    fn emit_fcmp(&mut self, k: FKind, op: FCmp, dst: Gpr, l: Fpr, r: Fpr) {
        let code = match op {
            FCmp::Eq => fsel(k, Opcode::FEQS, Opcode::FEQD),
            FCmp::Lt => fsel(k, Opcode::FLTS, Opcode::FLTD),
            FCmp::Le => fsel(k, Opcode::FLES, Opcode::FLED),
        };
        self.e(code, &[g(dst), f(l), f(r)]);
    }

    fn fcmp_ops(&mut self, k: FKind, lhs: &Op, rhs: &Op) -> Result<(Fpr, Fpr), LowerError> {
        if !matches!(lhs, Op::Fpr(_)) && !matches!(rhs, Op::Fpr(_)) {
            return Err(self.bad("float compare needs two live registers"));
        }
        Ok((self.fp_src(k, lhs)?, self.fp_src(k, rhs)?))
    }

    fn unordered_either(&mut self, k: FKind, l: Fpr, r: Fpr, t: Label) {
        self.emit_fcmp(k, FCmp::Eq, G2, l, l);
        self.br(Opcode::BEQ, G2, X0, t);
        self.emit_fcmp(k, FCmp::Eq, G2, r, r);
        self.br(Opcode::BEQ, G2, X0, t);
    }

    #[allow(clippy::too_many_arguments)]
    fn e_branchf(
        &mut self,
        cc: FCc,
        k: FKind,
        lhs: &Op,
        rhs: &Op,
        target: Lbl,
        patch: bool,
    ) -> Result<Option<PatchHandle>, LowerError> {
        let t = self.label(target);
        let not_patchable = || LowerError::NotPatchable(self.mn.to_string());
        match cc {
            FCc::Eq | FCc::Gt | FCc::Ge | FCc::Lt | FCc::Le => {
                let (l, r) = self.fcmp_ops(k, lhs, rhs)?;
                match cc {
                    FCc::Eq => self.emit_fcmp(k, FCmp::Eq, G1, l, r),
                    FCc::Gt => self.emit_fcmp(k, FCmp::Lt, G1, r, l),
                    FCc::Ge => self.emit_fcmp(k, FCmp::Le, G1, r, l),
                    FCc::Lt => self.emit_fcmp(k, FCmp::Lt, G1, l, r),
                    _ => self.emit_fcmp(k, FCmp::Le, G1, l, r),
                }
                Ok(self.emit_cond_branch(false, G1, t, patch))
            }
            FCc::Ne => {
                // Ordered not-equal: skip when either side is unordered,
                // then branch on inequality. Never patches (multi-branch).
                if patch {
                    return Err(not_patchable());
                }
                let (l, r) = self.fcmp_ops(k, lhs, rhs)?;
                self.emit_fcmp(k, FCmp::Eq, G1, l, l);
                let skip = self.fresh();
                self.br(Opcode::BEQ, G1, X0, skip);
                self.emit_fcmp(k, FCmp::Eq, G1, r, r);
                self.br(Opcode::BEQ, G1, X0, skip);
                self.emit_fcmp(k, FCmp::Eq, G1, l, r);
                self.br(Opcode::BEQ, G1, X0, t);
                self.bind(skip);
                Ok(None)
            }
            FCc::NeUn => {
                let (l, r) = self.fcmp_ops(k, lhs, rhs)?;
                self.emit_fcmp(k, FCmp::Eq, G1, l, r);
                if patch {
                    let skip = self.fresh();
                    self.br(Opcode::BNE, G1, X0, skip);
                    let h = self.patch_j(t);
                    self.bind(skip);
                    return Ok(Some(h));
                }
                self.br(Opcode::BEQ, G1, X0, t);
                Ok(None)
            }
            FCc::GtUn | FCc::LtUn | FCc::GeUn | FCc::LeUn | FCc::EqUn => {
                if patch {
                    return Err(not_patchable());
                }
                let (l, r) = self.fcmp_ops(k, lhs, rhs)?;
                let op = match cc {
                    FCc::GtUn | FCc::LtUn => FCmp::Lt,
                    FCc::GeUn | FCc::LeUn => FCmp::Le,
                    _ => FCmp::Eq,
                };
                self.emit_fcmp(k, op, G1, l, r);
                self.br(Opcode::BNE, G1, X0, t);
                self.unordered_either(k, l, r, t);
                Ok(None)
            }
        }
    }

    fn e_fset(
        &mut self,
        cc: FCc,
        k: FKind,
        dst: &Op,
        lhs: &Op,
        rhs: &Op,
    ) -> Result<(), LowerError> {
        let (swap, negate, ordered_ne, op) = match cc {
            FCc::Eq => (false, false, false, FCmp::Eq),
            FCc::Ne => (false, false, true, FCmp::Eq),
            FCc::NeUn => (false, true, false, FCmp::Eq),
            FCc::Gt | FCc::Lt => (true, false, false, FCmp::Lt),
            FCc::Ge | FCc::Le => (true, false, false, FCmp::Le),
            FCc::EqUn | FCc::GtUn | FCc::GeUn | FCc::LtUn | FCc::LeUn => {
                return Err(self.bad("unordered set is only defined for eq/ne"))
            }
        };
        let (mut l, mut r) = self.fcmp_ops(k, lhs, rhs)?;
        if swap {
            std::mem::swap(&mut l, &mut r);
        }

        self.emit_fcmp(k, op, G2, l, r);
        if ordered_ne {
            // `~eq & ordered(l) & ordered(r)`.
            self.emit_fcmp(k, FCmp::Eq, G1, l, l);
            self.emit_fcmp(k, FCmp::Eq, G2, r, r);
            self.rr(Opcode::AND, G1, G1, G2);
            self.emit_fcmp(k, FCmp::Eq, G2, l, r);
            self.ri(Opcode::XORI, G2, G2, 1);
            self.rr(Opcode::AND, G2, G2, G1);
        } else if negate {
            self.ri(Opcode::XORI, G2, G2, 1);
        }
        match dst {
            Op::Gpr(d) => {
                self.mov_reg(*d, G2, Width::B64);
                Ok(())
            }
            Op::Mem(a) => self.e_store(Width::B32, &Op::Gpr(G2), a),
            _ => Err(self.bad("float set needs a register or memory destination")),
        }
    }

    fn e_fround(
        &mut self,
        k: FKind,
        mode: RoundMode,
        dst: Fpr,
        src: &Op,
    ) -> Result<(), LowerError> {
        let r = self.fp_src(k, src)?;
        let (d, s) = (dst, SF);
        let (mbits, onebits) = match k {
            FKind::F64 => (
                0x4330_0000_0000_0000u64 as i64,
                0x3FF0_0000_0000_0000u64 as i64,
            ),
            FKind::F32 => (0x4B00_0000i64, 0x3F80_0000i64),
        };
        let fsgnj = fsel(k, Opcode::FSGNJS, Opcode::FSGNJD);
        let fsgnjx = fsel(k, Opcode::FSGNJXS, Opcode::FSGNJXD);
        let fadd = fsel(k, Opcode::FADDS, Opcode::FADDD);
        let fsub = fsel(k, Opcode::FSUBS, Opcode::FSUBD);
        // Park the input bits in the second scratch GPR. `r` may be the
        // scratch FPR, which `s` reuses below.
        self.fmv_xf(k, G2, r);
        // `d = |x|` (also the `|x| >= M` check input).
        self.e(fsgnjx, &[f(d), f(r), f(r)]);
        // `s = M` (the exactness bound).
        self.mov_imm(G1, mbits);
        self.fmv_fx(k, s, G1);
        let done = self.fresh();
        self.emit_fcmp(k, FCmp::Le, G1, s, d);
        let fast = self.fresh();
        self.br(Opcode::BEQ, G1, X0, fast);
        self.fmv_fx(k, d, G2);
        self.j(done);
        self.bind(fast);
        match mode {
            RoundMode::Nearest => {
                // `m = copysign(M, x); d = x + m - m`.
                self.fmv_fx(k, d, G2);
                self.e(fsgnj, &[f(s), f(s), f(d)]);
                self.e(fadd, &[f(d), f(d), f(s), i(DYN)]);
                self.e(fsub, &[f(d), f(d), f(s), i(DYN)]);
            }
            RoundMode::Trunc => {
                // `d = (|x| + M) - M` (= nearest, exact).
                self.e(fadd, &[f(d), f(d), f(s), i(DYN)]);
                self.e(fsub, &[f(d), f(d), f(s), i(DYN)]);
                // Pull toward zero when the nearest integer overshot the
                // magnitude (`|x| < d`), then apply the sign of `x`.
                self.fmv_fx(k, s, G2);
                self.e(fsgnjx, &[f(s), f(s), f(s)]);
                self.emit_fcmp(k, FCmp::Lt, G1, s, d);
                self.fmv_fx(k, s, G2);
                self.e(fsgnj, &[f(d), f(d), f(s)]);
                self.mov_imm(G2, onebits);
                self.fmv_fx(k, s, G2);
                // `s = copysign(1.0, d)`: subtracting it moves `d` toward
                // zero for either sign.
                self.e(fsgnj, &[f(s), f(s), f(d)]);
                let no_adj = self.fresh();
                self.br(Opcode::BEQ, G1, X0, no_adj);
                self.e(fsub, &[f(d), f(d), f(s), i(DYN)]);
                self.bind(no_adj);
            }
            RoundMode::Down | RoundMode::Up => {
                // `d = (|x| + M) - M`, sign applied. Then step toward -/+inf
                // when `d` is not already `x`.
                self.e(fadd, &[f(d), f(d), f(s), i(DYN)]);
                self.e(fsub, &[f(d), f(d), f(s), i(DYN)]);
                self.fmv_fx(k, s, G2);
                self.e(fsgnj, &[f(d), f(d), f(s)]);
                // Down adjusts iff `x < d`. Up adjusts iff `d < x`.
                if mode == RoundMode::Down {
                    self.emit_fcmp(k, FCmp::Lt, G1, s, d);
                } else {
                    self.emit_fcmp(k, FCmp::Lt, G1, d, s);
                }
                self.mov_imm(G2, onebits);
                self.fmv_fx(k, s, G2);
                let no_adj = self.fresh();
                self.br(Opcode::BEQ, G1, X0, no_adj);
                let step = if mode == RoundMode::Down { fsub } else { fadd };
                self.e(step, &[f(d), f(d), f(s), i(DYN)]);
                self.bind(no_adj);
            }
        }
        self.bind(done);
        Ok(())
    }

    fn e_tls(&mut self, w: Width, reg: Gpr, idx: i64, load: bool) -> Result<(), LowerError> {
        let off = idx
            .checked_mul(8)
            .ok_or_else(|| self.bad("tls index overflow"))?;
        let direct = i32::try_from(off).is_ok_and(fits_d12);
        if load {
            let op = load_op(w, Sx::Zero);
            if direct {
                self.load(op, reg, TP, off);
            } else {
                self.mov_imm(G1, off);
                self.rr(Opcode::ADD, G1, G1, TP);
                self.load(op, reg, G1, 0);
            }
        } else if direct {
            self.store(store_op(w), reg, TP, off);
        } else {
            self.fmv_fx(FKind::F64, SF, reg);
            self.mov_imm(G1, off);
            self.rr(Opcode::ADD, G1, G1, TP);
            self.fmv_xf(FKind::F64, G2, SF);
            self.store(store_op(w), G2, G1, 0);
        }
        Ok(())
    }

    fn e_tls_lea(&mut self, reg: Gpr, idx: i64) -> Result<(), LowerError> {
        let off = idx
            .checked_mul(8)
            .ok_or_else(|| self.bad("tls index overflow"))?;
        if off == 0 {
            if reg != TP {
                self.ri(Opcode::ADDI, reg, TP, 0);
            }
        } else if i32::try_from(off).is_ok_and(fits_d12) {
            self.ri(Opcode::ADDI, reg, TP, off);
        } else {
            self.mov_imm(G1, off);
            self.rr(Opcode::ADD, reg, G1, TP);
        }
        Ok(())
    }

    fn mask_lane(&mut self, w: Width, r: Gpr) {
        if w == Width::B8 {
            self.ri(Opcode::ANDI, r, r, 255);
        } else {
            self.slli(r, r, 48);
            self.srli(r, r, 48);
        }
    }

    /// `lr.w.aq`/`lr.d.aq rd, (addr)`.
    fn lr(&mut self, wide: bool, d: Gpr, addr: Gpr) {
        let code = if wide { Opcode::LRD } else { Opcode::LRW };
        self.e(code, &[g(d), g(addr), i(1), i(0)]);
    }

    /// `sc.w.rl`/`sc.d.rl status, value, (addr)`.
    fn sc(&mut self, wide: bool, status: Gpr, value: Gpr, addr: Gpr) {
        let code = if wide { Opcode::SCD } else { Opcode::SCW };
        self.e(code, &[g(status), g(addr), g(value), i(0), i(1)]);
    }

    /// Atomic read-modify-write / exchange.
    fn e_rmw(&mut self, op: AtomicOp, w: Width, a: &Op, b: &Op) -> Result<(), LowerError> {
        let (mem, reg) = match (a, b) {
            (Op::Mem(m), Op::Gpr(r)) | (Op::Gpr(r), Op::Mem(m)) => (*m, *r),
            _ => return Err(self.bad("atomic r/m needs one memory and one register operand")),
        };
        match w {
            Width::B32 | Width::B64 => {
                let staged = reg == G1;
                if staged {
                    self.mv(G2, reg);
                }
                self.addr_scratch(&mem, G1)?;
                let val = if staged { G2 } else { reg };
                // `Sub` negates the addend in place, then adds.
                if op == AtomicOp::Sub {
                    self.rr(wsel(w, Opcode::SUB, Opcode::SUBW), val, X0, val);
                }
                let wide = w == Width::B64;
                let code = match (op, wide) {
                    (AtomicOp::Add | AtomicOp::Sub, false) => Opcode::AMOADDW,
                    (AtomicOp::Add | AtomicOp::Sub, true) => Opcode::AMOADDD,
                    (AtomicOp::Xchg, false) => Opcode::AMOSWAPW,
                    (AtomicOp::Xchg, true) => Opcode::AMOSWAPD,
                    (AtomicOp::And, false) => Opcode::AMOANDW,
                    (AtomicOp::And, true) => Opcode::AMOANDD,
                    (AtomicOp::Or, false) => Opcode::AMOORW,
                    (AtomicOp::Or, true) => Opcode::AMOORD,
                    (AtomicOp::Xor, false) => Opcode::AMOXORW,
                    (AtomicOp::Xor, true) => Opcode::AMOXORD,
                };
                // `amo<op>.<w>.aqrl val, val, (addr)`.
                self.e(code, &[g(val), g(G1), g(val), i(1), i(1)]);
                if staged {
                    self.mv(reg, G2);
                }
                Ok(())
            }
            Width::B8 | Width::B16 => {
                let lanemask: i64 = if w == Width::B8 { 0xFF } else { 0xFFFF };
                if reg == G2 {
                    return Err(self.bad("atomic r/m needs a free scratch register"));
                }
                self.ri(Opcode::ADDI, SP, SP, -32);
                // Park the value before the address folds.
                self.store(Opcode::SD, reg, SP, 8);
                self.addr_scratch(&mem, G2)?;
                self.ri(Opcode::ANDI, G1, G2, 3);
                self.slli(G1, G1, 3);
                self.store(Opcode::SD, G1, SP, 0);
                self.ri(Opcode::ANDI, G2, G2, -4);
                let again = self.fresh();
                self.bind(again);
                self.lr(false, FLAGS, G2);
                self.store(Opcode::SD, FLAGS, SP, 16);
                self.load(Opcode::LD, G1, SP, 0);
                if op == AtomicOp::Xchg {
                    self.load(Opcode::LD, FLAGS, SP, 8);
                    self.mask_lane(w, FLAGS);
                    self.rr(Opcode::SLL, FLAGS, FLAGS, G1);
                    self.store(Opcode::SD, FLAGS, SP, 24);
                } else {
                    self.rr(Opcode::SRL, FLAGS, FLAGS, G1);
                    self.mask_lane(w, FLAGS);
                    self.load(Opcode::LD, G1, SP, 8);
                    let arith = match op {
                        AtomicOp::Add | AtomicOp::Xchg => Opcode::ADD,
                        AtomicOp::Sub => Opcode::SUB,
                        AtomicOp::Or => Opcode::OR,
                        AtomicOp::Xor => Opcode::XOR,
                        AtomicOp::And => Opcode::AND,
                    };
                    self.rr(arith, FLAGS, FLAGS, G1);
                    self.mask_lane(w, FLAGS);
                    self.load(Opcode::LD, G1, SP, 0);
                    self.rr(Opcode::SLL, FLAGS, FLAGS, G1);
                    self.store(Opcode::SD, FLAGS, SP, 24);
                }
                // `m = mask << shift`, `new = (old & ~m) | staged`.
                self.mov_imm(FLAGS, lanemask);
                self.rr(Opcode::SLL, G1, FLAGS, G1);
                self.ri(Opcode::XORI, G1, G1, -1);
                self.load(Opcode::LD, FLAGS, SP, 16);
                self.rr(Opcode::AND, FLAGS, FLAGS, G1);
                self.load(Opcode::LD, G1, SP, 24);
                self.rr(Opcode::OR, FLAGS, FLAGS, G1);
                self.sc(false, G1, FLAGS, G2);
                self.br(Opcode::BNE, G1, X0, again);
                // Old value (zero-extended) back into `reg`.
                self.load(Opcode::LD, G2, SP, 0);
                self.load(Opcode::LD, reg, SP, 16);
                self.rr(Opcode::SRL, reg, reg, G2);
                self.mask_lane(w, reg);
                self.ri(Opcode::ADDI, SP, SP, 32);
                Ok(())
            }
        }
    }

    /// Leave the observed old value in `dst`
    fn emit_cas_old_value(&mut self, w: Width, dst: Gpr) {
        match w {
            Width::B64 => self.mov_reg(dst, FLAGS, Width::B64),
            Width::B32 => {
                self.slli(dst, FLAGS, 32);
                self.srli(dst, dst, 32);
            }
            _ => {
                self.load(Opcode::LD, dst, SP, 16);
                self.load(Opcode::LD, G2, SP, 0);
                self.rr(Opcode::SRL, dst, dst, G2);
                self.mask_lane(w, dst);
            }
        }
    }

    /// `AtomicCas` with the expected value in the `t0`.
    fn e_cas(
        &mut self,
        w: Width,
        mem: &Mem,
        src: Gpr,
        branch: Option<Lbl>,
    ) -> Result<(), LowerError> {
        self.addr_scratch(mem, G1)?;
        let again = self.fresh();
        let fail = self.fresh();
        let done = self.fresh();
        let subword = w == Width::B8 || w == Width::B16;
        let lanemask: i64 = if w == Width::B8 { 0xFF } else { 0xFFFF };
        if subword {
            self.ri(Opcode::ADDI, SP, SP, -32);
            self.store(Opcode::SD, src, SP, 8);
            self.ri(Opcode::ANDI, G2, G1, 3);
            self.slli(G2, G2, 3);
            self.store(Opcode::SD, G2, SP, 0);
            self.ri(Opcode::ANDI, G1, G1, -4);
        }
        self.bind(again);
        self.lr(w == Width::B64, FLAGS, G1);
        if subword {
            self.store(Opcode::SD, FLAGS, SP, 16);
        }

        if w == Width::B64 {
            self.br(Opcode::BNE, FLAGS, T0, fail);
        } else if w == Width::B32 {
            // Low-word equality via the masked difference.
            self.slli(G2, FLAGS, 32);
            self.srli(G2, G2, 32);
            self.rr(Opcode::SUB, G2, G2, T0);
            self.slli(G2, G2, 32);
            self.srli(G2, G2, 32);
            self.br(Opcode::BNE, G2, X0, fail);
        } else {
            self.load(Opcode::LD, G2, SP, 0);
            self.rr(Opcode::SRL, G2, FLAGS, G2);
            self.rr(Opcode::SRL, FLAGS, T0, G2);
            self.rr(Opcode::SUB, G2, G2, FLAGS);
            self.mask_lane(w, G2);
            self.br(Opcode::BNE, G2, X0, fail);
            self.load(Opcode::LD, FLAGS, SP, 16);
        }

        if subword {
            self.load(Opcode::LD, G2, SP, 0);
            self.load(Opcode::LD, FLAGS, SP, 8);
            self.mask_lane(w, FLAGS);
            self.rr(Opcode::SLL, FLAGS, FLAGS, G2);
            self.store(Opcode::SD, FLAGS, SP, 8);
            self.mov_imm(FLAGS, lanemask);
            self.rr(Opcode::SLL, G2, FLAGS, G2);
            self.ri(Opcode::XORI, G2, G2, -1);
            self.load(Opcode::LD, FLAGS, SP, 16);
            self.rr(Opcode::AND, FLAGS, FLAGS, G2);
            self.load(Opcode::LD, G2, SP, 8);
            self.rr(Opcode::OR, FLAGS, FLAGS, G2);
        }
        match w {
            Width::B32 => self.sc(false, G2, src, G1),
            Width::B64 => self.sc(true, G2, src, G1),
            _ => self.sc(false, G2, FLAGS, G1),
        }
        self.br(Opcode::BNE, G2, X0, again);
        self.emit_cas_old_value(w, T0);
        self.j(done);
        self.bind(fail);
        self.emit_cas_old_value(w, T0);
        if let Some(target) = branch {
            let t = self.label(target);
            self.j(t);
        }
        self.bind(done);
        if subword {
            self.ri(Opcode::ADDI, SP, SP, 32);
        }
        Ok(())
    }

    /// Exclusive load (`lr.w`/`lr.d`, acquire).
    fn e_loadlinked(&mut self, w: Width, mem: &Mem, dst: Gpr) -> Result<(), LowerError> {
        self.addr_scratch(mem, G1)?;
        match w {
            Width::B32 => self.lr(false, dst, G1),
            Width::B64 => self.lr(true, dst, G1),
            Width::B8 | Width::B16 => {
                let sh = if w == Width::B8 { 3 } else { 4 };
                self.mov_reg(G2, G1, Width::B64);
                self.ri(Opcode::ANDI, G2, G2, 3);
                self.slli(G2, G2, sh);
                self.ri(Opcode::ANDI, dst, G1, -4);
                self.lr(false, dst, dst);
                self.rr(Opcode::SRL, dst, dst, G2);
                self.mask_lane(w, dst);
            }
        }
        Ok(())
    }

    /// Exclusive store (`sc.w`/`sc.d`, release): status 0/1 in `status`.
    fn e_storecond(
        &mut self,
        w: Width,
        status: Gpr,
        src: Gpr,
        mem: &Mem,
    ) -> Result<(), LowerError> {
        self.addr_scratch(mem, G1)?;
        match w {
            Width::B32 => self.sc(false, status, src, G1),
            Width::B64 => self.sc(true, status, src, G1),
            Width::B8 | Width::B16 => {
                // Lane merge with retry.
                let lanemask: i64 = if w == Width::B8 { 0xFF } else { 0xFFFF };
                self.ri(Opcode::ADDI, SP, SP, -32);
                self.store(Opcode::SD, src, SP, 8);
                self.ri(Opcode::ANDI, status, G1, 3);
                self.slli(status, status, if w == Width::B8 { 3 } else { 4 });
                self.store(Opcode::SD, status, SP, 0);
                self.ri(Opcode::ANDI, G1, G1, -4);
                let again = self.fresh();
                self.bind(again);
                self.lr(false, FLAGS, G1);
                self.load(Opcode::LD, status, SP, 8);
                self.mask_lane(w, status);
                self.load(Opcode::LD, G2, SP, 0);
                self.rr(Opcode::SLL, status, status, G2);
                self.mov_imm(G2, lanemask);
                self.load(Opcode::LD, src, SP, 0);
                self.rr(Opcode::SLL, G2, G2, src);
                self.ri(Opcode::XORI, G2, G2, -1);
                self.rr(Opcode::AND, FLAGS, FLAGS, G2);
                self.rr(Opcode::OR, FLAGS, FLAGS, status);
                self.sc(false, status, FLAGS, G1);
                self.br(Opcode::BNE, status, X0, again);
                self.ri(Opcode::ADDI, SP, SP, 32);
            }
        }
        Ok(())
    }

    fn e_pair(
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
        let direct = mem.index.is_none()
            && mem.base.is_some()
            && fits_d12(mem.disp.const_or_zero())
            && fits_d12(mem.disp.const_or_zero().wrapping_add(scale as i32));
        let (b, d0): (Gpr, i64) = if direct {
            (mem.base_reg(), i64::from(mem.disp.const_or_zero()))
        } else {
            self.addr_scratch(mem, G1)?;
            (G1, 0)
        };
        let off2 = d0 + scale;
        let vec_halves = |d0: i64| {
            let hi = d0 + 16;
            let at = |d: i64| Mem {
                base: Some(b),
                index: None,
                disp: Disp::Const(d as i32),
            };
            (fits_d12(d0 as i32) && fits_d12(hi as i32), at(d0), at(hi))
        };
        if load {
            match (first, second) {
                (Op::Gpr(a), Op::Gpr(bb)) => {
                    let op = match w {
                        PairW::B32 => Opcode::LWU,
                        PairW::B64 => Opcode::LD,
                        _ => return Err(self.bad("integer pair needs 32/64-bit width")),
                    };

                    if *a == b {
                        self.load(op, *bb, b, off2);
                        if a != bb {
                            self.load(op, *a, b, d0);
                        }
                    } else {
                        self.load(op, *a, b, d0);
                        self.load(op, *bb, b, off2);
                    }
                }
                (Op::Fpr(a), Op::Fpr(bb)) if w == PairW::F64 => {
                    self.fload(Opcode::FLD, *a, b, d0);
                    self.fload(Opcode::FLD, *bb, b, off2);
                }
                (Op::Fpr(a), Op::Fpr(bb)) if w == PairW::V128 => {
                    let (ok, ma, mb) = vec_halves(d0);
                    if !ok {
                        return Err(self.bad("pair address overflow"));
                    }
                    self.e_loadv(*a, &ma)?;
                    self.e_loadv(*bb, &mb)?;
                }
                _ => return Err(self.bad("pair load needs two GPRs (or two FPRs for fp pairs)")),
            }
            return Ok(());
        }
        match (first, second) {
            (Op::Gpr(a), Op::Gpr(bb)) => {
                let op = match w {
                    PairW::B32 => Opcode::SW,
                    PairW::B64 => Opcode::SD,
                    _ => return Err(self.bad("integer pair needs 32/64-bit width")),
                };
                self.store(op, *a, b, d0);
                self.store(op, *bb, b, off2);
            }
            (Op::Fpr(a), Op::Fpr(bb)) if w == PairW::F64 => {
                self.fstore(Opcode::FSD, *a, b, d0);
                self.fstore(Opcode::FSD, *bb, b, off2);
            }
            (Op::Fpr(a), Op::Fpr(bb)) if w == PairW::V128 => {
                let (ok, ma, mb) = vec_halves(d0);
                if !ok {
                    return Err(self.bad("pair address overflow"));
                }
                self.e_storev(*a, &ma)?;
                self.e_storev(*bb, &mb)?;
            }
            _ => return Err(self.bad("pair store needs two GPRs (or two FPRs for fp pairs)")),
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn emit(&mut self, inst: &Inst) -> Result<Option<PatchHandle>, LowerError> {
        let none = Ok(None);
        match inst {
            Inst::Mov { w, dst, src, patch } => {
                if *patch {
                    return match (src, dst) {
                        (Op::Imm(v), Op::Gpr(d)) => {
                            Ok(Some(PatchHandle::Data(self.asm.patchable_li(x(*d), *v))))
                        }
                        _ => Err(LowerError::NotPatchable(self.mn.to_string())),
                    };
                }
                self.e_mov(*w, dst, src)?;
                none
            }
            Inst::Bind(l) => {
                let t = self.label(*l);
                self.bind(t);
                none
            }
            Inst::MovZero32 { dst, src } => {
                self.e_movzero32(dst, src)?;
                none
            }
            Inst::Bswap { w, dst, src } => {
                self.e_bswap(*w, dst, src)?;
                none
            }
            Inst::Load {
                w,
                sx,
                dst,
                addr,
                acquire,
            } => {
                self.e_load(*w, *sx, *dst, addr)?;
                if *acquire {
                    self.asm.fence(0, 2, 3, 0, 0);
                }
                none
            }
            Inst::Store { w, src, addr } => {
                self.e_store(*w, src, addr)?;
                none
            }
            Inst::LoadF { k, dst, addr } => {
                self.e_loadf(*k, *dst, addr)?;
                none
            }
            Inst::StoreF { k, src, addr } => {
                self.e_storef(*k, *src, addr)?;
                none
            }
            Inst::FMov { k, dst, src } => {
                self.rv_fmov(*k, *dst, *src);
                none
            }
            Inst::LoadV { dst, addr } => {
                self.e_loadv(*dst, addr)?;
                none
            }
            Inst::StoreV { src, addr } => {
                self.e_storev(*src, addr)?;
                none
            }
            Inst::VMov { dst, src } => {
                self.e_vmov(*dst, *src)?;
                none
            }
            Inst::Lea { w, dst, src } => {
                self.e_lea(*w, *dst, src)?;
                none
            }
            Inst::Push { op } => {
                self.e_push_pop(op, true)?;
                none
            }
            Inst::Pop { op } => {
                self.e_push_pop(op, false)?;
                none
            }
            Inst::PushV { src } => {
                self.e_push_pop_v(*src, true)?;
                none
            }
            Inst::PopV { dst } => {
                self.e_push_pop_v(*dst, false)?;
                none
            }
            Inst::Peek { disp, dst } => {
                self.e_peek_poke(*disp, *dst, true);
                none
            }
            Inst::Poke { disp, src } => {
                self.e_peek_poke(*disp, *src, false);
                none
            }
            Inst::Add { w, op } => {
                self.op_n(AluKind::Add, *w, &alu_args(op))?;
                none
            }
            Inst::Sub { w, op } => {
                self.op_n(AluKind::Sub, *w, &alu_args(op))?;
                none
            }
            Inst::Mul { w, op } => {
                self.op_n(AluKind::Mul, *w, &alu_args(op))?;
                none
            }
            Inst::And { w, op } => {
                self.op_n(AluKind::And, *w, &alu_args(op))?;
                none
            }
            Inst::Or { w, op } => {
                self.op_n(AluKind::Or, *w, &alu_args(op))?;
                none
            }
            Inst::Xor { w, op } => {
                self.op_n(AluKind::Xor, *w, &alu_args(op))?;
                none
            }
            Inst::Not { w, dst } => {
                self.e_not_neg(*w, dst, false)?;
                none
            }
            Inst::Neg { w, dst } => {
                self.e_not_neg(*w, dst, true)?;
                none
            }
            Inst::Shift { w, op, dst, cnt } => {
                self.e_shift(*w, *op, *dst, cnt)?;
                none
            }
            Inst::MulImm { w, dst, lhs, imm } => {
                self.e_mulimm(*w, *dst, *lhs, *imm)?;
                none
            }
            Inst::AluS { op, w, alu } => {
                self.e_alus(*op, *w, alu)?;
                none
            }
            Inst::Adc { dst, src } => {
                self.e_adc_sbb(dst, src, false)?;
                none
            }
            Inst::Sbb { dst, src } => {
                self.e_adc_sbb(dst, src, true)?;
                none
            }
            Inst::MulWide {
                signed,
                dst,
                lhs,
                rhs,
            } => {
                self.e_mulwide(*signed, *dst, *lhs, *rhs);
                none
            }
            Inst::MulHigh { signed, rhs } => {
                let r = self.load_op_gpr(rhs, Width::B64, G1)?;
                self.rr(
                    if *signed { Opcode::MULH } else { Opcode::MULHU },
                    T2,
                    T0,
                    r,
                );
                self.rr(Opcode::MUL, T0, T0, r);
                none
            }
            Inst::DivMod1 { signed, w, divisor } => {
                self.e_divmod1(*signed, *w, divisor)?;
                none
            }
            Inst::Div3 {
                signed,
                w,
                dst,
                dvd,
                dvs,
            } => {
                self.e_div(*w, *signed, true, *dst, dvd, dvs)?;
                none
            }
            Inst::Rem3 {
                signed,
                w,
                dst,
                dvd,
                dvs,
            } => {
                self.e_div(*w, *signed, false, *dst, dvd, dvs)?;
                none
            }
            Inst::Extend {
                from,
                to,
                sx,
                dst,
                src,
            } => {
                self.e_extend(*from, *to, *sx, *dst, src)?;
                none
            }
            Inst::Ctz { w, dst, src } => {
                let s = self.load_op_gpr(src, *w, G1)?;
                self.ctz_rr(*w, *dst, s);
                none
            }
            Inst::Clz { w, dst, src } => {
                let s = self.load_op_gpr(src, *w, G1)?;
                self.clz_rr(*w, *dst, s);
                none
            }
            Inst::Popcnt { w, dst, src } => {
                // A `B32` count reads the zero-extended 32-bit operand.
                let s = self.load_op_gpr(src, *w, G1)?;
                self.popcnt_rr(*dst, s);
                none
            }
            Inst::Cqo { quad } => {
                if *quad {
                    self.srai(T2, T0, 63);
                } else {
                    self.slli(T2, T0, 32);
                    self.srai(T2, T2, 32);
                }
                none
            }
            Inst::AddShifted {
                dst,
                lhs,
                rhs,
                amount,
            } => {
                if *amount >= 64 {
                    return Err(self.bad("shift amount out of range"));
                }
                self.slli(*dst, *rhs, i64::from(*amount));
                self.rr(Opcode::ADD, *dst, *lhs, *dst);
                none
            }
            Inst::Cmov {
                w,
                zero,
                dst,
                src,
                test,
            } => {
                self.e_cmov(*w, *zero, *dst, src, *test)?;
                none
            }
            Inst::VecExtract { w, dst, src, lane } => {
                self.e_vecextract(*w, *dst, *src, *lane)?;
                none
            }
            Inst::Branch {
                cc,
                w,
                lhs,
                rhs,
                target,
                patch,
            } => self.e_branch(*cc, *w, lhs, rhs, *target, *patch),
            Inst::TestBranch {
                w,
                value,
                mask,
                test,
                target,
                patch,
            } => self.e_testbranch(*w, value, mask.as_ref(), *test, *target, *patch),
            Inst::OpBranch {
                op,
                w,
                flag,
                args,
                target,
                patch,
            } => self.e_opbranch(*op, *w, *flag, args, *target, *patch),
            Inst::FlagBranch {
                flag,
                target,
                patch,
            } => Ok(self.e_flagbranch(*flag, *target, *patch)),
            Inst::Jump { target, patch } => self.e_jmp_call(target, *patch, false),
            Inst::Call { target, patch } => self.e_jmp_call(target, *patch, true),
            Inst::Ret => {
                self.ri(Opcode::JALR, X0, RA, 0);
                none
            }
            Inst::Break => {
                self.e(Opcode::EBREAK, &[]);
                none
            }
            Inst::Nop => {
                self.ri(Opcode::ADDI, X0, X0, 0);
                none
            }
            Inst::IntSet {
                cc,
                w,
                dst,
                lhs,
                rhs,
            } => {
                self.e_intset(*cc, *w, dst, lhs, rhs)?;
                none
            }
            Inst::TestSet {
                w,
                value,
                mask,
                test,
                dst,
            } => {
                self.e_testset(*w, value, mask.as_ref(), *test, dst)?;
                none
            }
            Inst::FArith { op, k, arith } => {
                self.e_farith(*op, *k, arith)?;
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
                self.e_fma(*op, *k, a, b, c, *dst)?;
                none
            }
            Inst::FSqrt { k, dst, src } => {
                let r = self.fp_src(*k, src)?;
                self.e(
                    fsel(*k, Opcode::FSQRTS, Opcode::FSQRTD),
                    &[f(*dst), f(r), i(DYN)],
                );
                none
            }
            Inst::FRound { k, mode, dst, src } => {
                self.e_fround(*k, *mode, *dst, src)?;
                none
            }
            Inst::FAbs { k, dst, src } | Inst::FNeg { k, dst, src } => {
                // Sign injection: `fsgnjx` clears, `fsgnjn` flips.
                let r = self.fp_src(*k, src)?;
                let code = if matches!(inst, Inst::FNeg { .. }) {
                    fsel(*k, Opcode::FSGNJNS, Opcode::FSGNJND)
                } else {
                    fsel(*k, Opcode::FSGNJXS, Opcode::FSGNJXD)
                };
                self.e(code, &[f(*dst), f(r), f(r)]);
                none
            }
            Inst::FBit { or, k, dst, src } => {
                self.e_fbit(*or, *k, *dst, src)?;
                none
            }
            Inst::CvtFI { k, w, dst, src } => {
                self.e_cvtfi(*k, *w, *dst, src)?;
                none
            }
            Inst::CvtIF {
                signed,
                from,
                k,
                dst,
                src,
            } => {
                self.e_cvtif(*signed, *from, *k, *dst, src)?;
                none
            }
            Inst::CvtFF { from, to, dst, src } => {
                self.e_cvtff(*from, *to, *dst, src)?;
                none
            }
            Inst::Bitcast { dir, dst, src } => {
                self.e_bitcast(*dir, dst, src)?;
                none
            }
            Inst::BranchF {
                cc,
                k,
                lhs,
                rhs,
                target,
                patch,
            } => self.e_branchf(*cc, *k, lhs, rhs, *target, *patch),
            Inst::FSet {
                cc,
                k,
                dst,
                lhs,
                rhs,
            } => {
                self.e_fset(*cc, *k, dst, lhs, rhs)?;
                none
            }
            Inst::Fence { full: _ } => {
                // RISC-V has one barrier instruction (`fence iorw, iorw`).
                self.asm.fence(0, 15, 15, 0, 0);
                none
            }
            Inst::Pause => {
                self.asm.pause();
                none
            }
            Inst::TlsLoad { w, dst, idx } => {
                self.e_tls(*w, *dst, *idx, true)?;
                none
            }
            Inst::TlsStore { w, src, idx } => {
                self.e_tls(*w, *src, *idx, false)?;
                none
            }
            Inst::TlsLea { dst, idx } => {
                self.e_tls_lea(*dst, *idx)?;
                none
            }
            Inst::AtomicRmw { op, w, a, b } => {
                self.e_rmw(*op, *w, a, b)?;
                none
            }
            Inst::AtomicCas {
                w,
                mem,
                src,
                branch,
            } => {
                self.e_cas(*w, mem, *src, *branch)?;
                none
            }
            Inst::LoadLinked { w, mem, dst } => {
                self.e_loadlinked(*w, mem, *dst)?;
                none
            }
            Inst::StoreCond {
                w,
                status,
                src,
                mem,
            } => {
                self.e_storecond(*w, *status, *src, mem)?;
                none
            }
            Inst::PairLoad { w, dst1, dst2, mem } => {
                self.e_pair(*w, dst1, dst2, mem, true)?;
                none
            }
            Inst::PairStore { w, src1, src2, mem } => {
                self.e_pair(*w, src1, src2, mem, false)?;
                none
            }
        }
    }
}

/// A float compare.
#[derive(Clone, Copy)]
enum FCmp {
    Eq,
    Lt,
    Le,
}
