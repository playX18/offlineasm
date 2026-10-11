//! Expands mnemonic invocations into [`Inst`] sequences.

use super::inst::*;
use super::mnemonic::Mnemonic;
use super::*;

/// Lowers one mnemonic invocation to the [`Inst`] sequence that implements it.
///
/// `sc` supplies the scratch registers that multi-instruction expansions
/// and the destination-aliasing fixup may need. It must not alias any
/// operand in `ops`.
/// When `patch` is set, the mnemonic must be a [`patch_kind`] site, and the
/// returned sequence is shaped so a backend can patch it after emission
/// (a fixed instruction count, no operand folding).
///
/// # Errors
///
/// - [`ExpandError::NotPatchable`] if `patch` is set and `mn` has no
///   [`patch_kind`].
/// - [`ExpandError::BadOperand`] if `ops` has the wrong count or kind for
///   `mn`.
pub fn expand(
    mn: Mnemonic,
    ops: &[Op],
    sc: &Scratch,
    patch: bool,
) -> Result<Vec<Inst>, ExpandError> {
    if patch && patch_kind(mn).is_none() {
        return Err(ExpandError::NotPatchable(mn.as_str().to_string()));
    }
    check_extern_operands(mn, ops, patch)?;
    let mut insts = expand_inner(mn, ops, sc, patch)?;
    stage_aliasing_mem(&mut insts, sc);
    Ok(insts)
}

/// Rejects external symbols outside the shapes that take one: the target of
/// `jmp`/`call`, the source of `move`, and the source of a 64-bit `lea`
/// (`leap`, `globaladdr`, `la`). None of them is a patch site.
fn check_extern_operands(mn: Mnemonic, ops: &[Op], patch: bool) -> Result<(), ExpandError> {
    let Some(at) = ops.iter().position(|o| matches!(o, Op::Extern(_))) else {
        return Ok(());
    };
    if patch {
        return Err(bad(mn, "an external symbol cannot be a patch site"));
    }
    let ok = match mn {
        Mnemonic::Jmp | Mnemonic::Call => at == 0,
        Mnemonic::Move => at == 1 && matches!(ops[0], Op::Gpr(_)),
        Mnemonic::Lea {
            w: Width::B64,
            form: LeaForm::Plain | LeaForm::Global | LeaForm::La,
        } => at == 1,
        _ => false,
    };
    if ok {
        Ok(())
    } else {
        Err(bad(
            mn,
            "an external symbol is only a `jmp`/`call` target or the source of \
             `move`/`leap`/`globaladdr`/`la`",
        ))
    }
}

/// Stages aliased memory operands through the scratch registers.
///
/// `addis t1, t0, 8[t1]` reads `8[t1]` with the *old* `t1`: all operands are
/// evaluated before the destination is written. A backend that first lowers
/// `dst = lhs` into `t1` and then reuses `t1` as the memory base (the
/// natural 2-operand sequence on every target) reads `8[t1]` after the move
/// instead and dereferences the wrong address. The fused `Alu3`/op-branch
/// nodes hand that ordering choice to each backend, so the fix is pinned
/// down in the front half both assemblers share: the load happens before
/// the operation, through the expansion scratch register.
///
/// The oracle interprets this same sequence, and scratch is clobberable by
/// design (it is never in the portable register pool, so it cannot alias
/// `dst` or the operand bases).
fn stage_aliasing_mem(insts: &mut Vec<Inst>, sc: &Scratch) {
    let old = std::mem::take(insts);
    let mut out = Vec::with_capacity(old.len() + 2);
    for mut inst in old {
        let loads = stage_one(&mut inst, sc);
        if let Some(loads) = loads {
            out.extend(loads);
        }
        out.push(inst);
    }
    *insts = out;
}

/// Collects the staging loads for `inst` and rewrites its aliased operands.
///
/// Returns `None` when `inst` needs no staging.
fn stage_one(inst: &mut Inst, sc: &Scratch) -> Option<Vec<Inst>> {
    let (w, operands, dst) = match inst {
        Inst::Add { w, op }
        | Inst::Sub { w, op }
        | Inst::Mul { w, op }
        | Inst::And { w, op }
        | Inst::Or { w, op }
        | Inst::Xor { w, op } => (*w, vec![&mut op.lhs, &mut op.rhs], &mut op.dst),
        Inst::AluS { w, alu, .. } => (*w, vec![&mut alu.lhs, &mut alu.rhs], &mut alu.dst),
        Inst::OpBranch { w, args, .. } => {
            let (last, init) = args.split_last_mut()?;
            (*w, init.iter_mut().collect(), last)
        }
        _ => return None,
    };
    let Op::Gpr(g) = *dst else {
        return None;
    };
    let slots = [sc.gpr, sc.gpr2];
    let mut loads = Vec::new();
    let mut slot = 0usize;
    for operand in operands {
        let Op::Mem(m) = operand else {
            continue;
        };
        let aliases = m.base == Some(g) || matches!(m.index, Some((idx, _)) if idx == g);
        if !aliases {
            continue;
        }
        // At most two memory operands can alias `dst` (op-branch takes
        // `[lhs, rhs, dst]`), and both scratch GPRs are available.
        let &s = slots.get(slot)?;
        slot += 1;
        loads.push(Inst::Load {
            w,
            sx: Sx::Zero,
            dst: s,
            addr: *m,
            acquire: false,
        });
        *operand = Op::Gpr(s);
    }
    (!loads.is_empty()).then_some(loads)
}

/// Returns the patch shape for `mn`.
pub fn patch_kind(mn: Mnemonic) -> Option<PatchKind> {
    Some(match mn {
        Mnemonic::Jmp => PatchKind::JumpSite,
        Mnemonic::Call => PatchKind::CallSite,
        Mnemonic::Move => PatchKind::MovBlock,
        Mnemonic::FlagBranch(_)
        | Mnemonic::OpBranch { .. }
        | Mnemonic::RiscAluS { .. }
        | Mnemonic::TestBranch { .. }
        | Mnemonic::IntBranch { .. }
        | Mnemonic::BranchF { .. } => PatchKind::CondJumpSite,
        _ => return None,
    })
}

/// Describes what a `#[patch]` site patches.
///
/// Jump shapes become jump handles (in onlineasm, retargeted after
/// emission); [`MovBlock`](PatchKind::MovBlock) becomes a 64-bit immediate
/// slot (rewritten after emission).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PatchKind {
    /// Patches an unconditional jump target (`jmp` to a label).
    JumpSite,
    /// Patches a conditional branch target (a single-branch expansion).
    CondJumpSite,
    /// Patches a call target (`call` to a label).
    CallSite,
    /// Patches a 64-bit move slot (`move` of an immediate into a register).
    MovBlock,
}

fn float_cc(cc: FCc) -> (FCc, bool) {
    match cc {
        FCc::Lt => (FCc::Gt, true),
        FCc::Le => (FCc::Ge, true),
        FCc::GtUn => (FCc::GtUn, false),
        FCc::GeUn => (FCc::GeUn, false),
        FCc::LtUn => (FCc::GtUn, true),
        FCc::LeUn => (FCc::GeUn, true),
        other => (other, false),
    }
}

fn test_set_node(
    mn: Mnemonic,
    ops: &[Op],
    w: Width,
    test: TestKind,
) -> Result<Vec<Inst>, ExpandError> {
    if ops.len() != 2 && ops.len() != 3 {
        return Err(bad(mn, "test-set takes 2 or 3 operands"));
    }
    let mask = if ops.len() == 3 { Some(ops[2]) } else { None };
    Ok(vec![Inst::TestSet {
        w,
        value: ops[1],
        mask,
        test,
        dst: ops[0],
    }])
}

fn test_branch_node(
    mn: Mnemonic,
    ops: &[Op],
    w: Width,
    test: TestKind,
    patch: bool,
) -> Result<Vec<Inst>, ExpandError> {
    if ops.len() != 2 && ops.len() != 3 {
        return Err(bad(mn, "test-branch takes 2 or 3 operands"));
    }
    let mask = if ops.len() == 3 { Some(ops[1]) } else { None };
    let target = label_op(
        mn,
        ops.last()
            .ok_or_else(|| bad(mn, "test-branch takes 2 or 3 operands"))?,
    )?;
    Ok(vec![Inst::TestBranch {
        w,
        value: ops[0],
        mask,
        test,
        target,
        patch,
    }])
}

fn div_rem_node(
    mn: Mnemonic,
    ops: &[Op],
    signed: bool,
    w: Width,
    rem: bool,
) -> Result<Vec<Inst>, ExpandError> {
    let (dvd, dvs, dst) = match ops {
        [dst, dvs] => (*dst, *dvs, gpr_op(mn, dst)?),
        [dst, dvd, dvs] => (*dvd, *dvs, gpr_op(mn, dst)?),
        _ => return Err(bad(mn, "divide takes 2 or 3 operands")),
    };
    Ok(vec![if rem {
        Inst::Rem3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        }
    } else {
        Inst::Div3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        }
    }])
}

fn shift_mem_canon(
    mn: Mnemonic,
    w: Width,
    op: ShiftOp,
    cnt: &Op,
    dst: &Mem,
    sc: &Scratch,
) -> Result<Vec<Inst>, ExpandError> {
    let shift_cnt = match cnt {
        Op::Imm(v) => ShiftCnt::Imm(*v),
        Op::Gpr(g) => ShiftCnt::Reg(*g),
        _ => return Err(bad(mn, "shift count must be an immediate or register")),
    };
    Ok(vec![
        Inst::Load {
            w,
            sx: Sx::Zero,
            dst: sc.gpr,
            addr: *dst,
            acquire: false,
        },
        Inst::Shift {
            w,
            op,
            dst: sc.gpr,
            cnt: shift_cnt,
        },
        Inst::Store {
            w,
            src: Op::Gpr(sc.gpr),
            addr: *dst,
        },
    ])
}

fn shift_node(
    mn: Mnemonic,
    w: Width,
    op: ShiftOp,
    ops: &[Op],
    sc: &Scratch,
) -> Result<Vec<Inst>, ExpandError> {
    if ops.len() != 2 {
        return Err(bad(mn, "shift takes 2 operands"));
    }
    if let Op::Mem(a) = &ops[0] {
        return shift_mem_canon(mn, w, op, &ops[1], a, sc);
    }
    let dst = gpr_op(mn, &ops[0])?;
    let cnt = match &ops[1] {
        Op::Imm(v) => ShiftCnt::Imm(*v),
        Op::Gpr(g) => ShiftCnt::Reg(*g),
        _ => return Err(bad(mn, "shift count must be an immediate or register")),
    };
    Ok(vec![Inst::Shift { w, op, dst, cnt }])
}

fn alu3(mn: Mnemonic, ops: &[Op]) -> Result<Alu3, ExpandError> {
    Alu3::from_operands(mn, ops)
}

fn op_branch_args(mn: Mnemonic, ops: &[Op]) -> Result<Vec<Op>, ExpandError> {
    match ops {
        [dst, rhs] => Ok(vec![*rhs, *dst]),
        [dst, lhs, rhs] => Ok(vec![*lhs, *rhs, *dst]),
        _ => Err(bad(mn, "op-branch takes 3 or 4 operands")),
    }
}

fn jump_target(mn: Mnemonic, op: &Op) -> Result<Target, ExpandError> {
    match op {
        Op::Label(l) => Ok(Target::Label(*l)),
        Op::Gpr(g) => Ok(Target::Reg(*g)),
        Op::Mem(a) => Ok(Target::Mem(*a)),
        Op::Imm(v) => Ok(Target::Abs(*v)),
        Op::Extern(e) => Ok(Target::Extern(*e)),
        _ => Err(bad(
            mn,
            "jump/call needs a label, register, memory, or immediate",
        )),
    }
}

#[allow(clippy::too_many_lines)]
fn expand_inner(
    mn: Mnemonic,
    ops: &[Op],
    sc: &Scratch,
    patch: bool,
) -> Result<Vec<Inst>, ExpandError> {
    let one = |mn: Mnemonic, ops: &[Op]| -> Result<Op, ExpandError> {
        expect_len(mn, ops, 1)?;
        Ok(ops[0])
    };
    match mn {
        Mnemonic::Move => Ok(vec![mov_node(mn, ops, Width::B64, patch)?]),
        Mnemonic::Load(w) => Ok(vec![mov_node(mn, ops, w, patch)?]),
        Mnemonic::AtomicLoad(w) => Ok(vec![atomic_load_node(mn, ops, w)?]),
        Mnemonic::Store(w) => Ok(vec![store_node(mn, ops, w)?]),
        Mnemonic::Extend { from, to, sx } => Ok(vec![extend_node(mn, ops, from, to, sx)?]),
        Mnemonic::MovZero32 => Ok(vec![movzero_node(mn, ops)?]),
        Mnemonic::Transfer(w) => transfer_node(mn, ops, sc, w),
        Mnemonic::FMove(k) => Ok(vec![fmove_node(mn, ops, k)?]),
        Mnemonic::VMove { store } => Ok(vec![vmove_node(mn, ops, store)?]),
        Mnemonic::Lea { w, .. } => Ok(vec![lea_node(mn, ops, w)?]),
        Mnemonic::LoadQInc => loadqinc_node(mn, ops),
        Mnemonic::LoadPair(w) => Ok(vec![pair_node(mn, ops, w, true)?]),
        Mnemonic::StorePair(w) => Ok(vec![pair_node(mn, ops, w, false)?]),
        Mnemonic::Push => stack_nodes(mn, ops, true, false),
        Mnemonic::Pop => stack_nodes(mn, ops, false, false),
        Mnemonic::PushV => stack_nodes(mn, ops, true, true),
        Mnemonic::PopV => stack_nodes(mn, ops, false, true),
        Mnemonic::PushCalleeSaves => stack_nodes(mn, ops, true, false),
        Mnemonic::PopCalleeSaves => stack_nodes(mn, ops, false, false),
        Mnemonic::Peek => Ok(vec![peek_node(mn, ops, true)?]),
        Mnemonic::Poke => Ok(vec![peek_node(mn, ops, false)?]),
        Mnemonic::TlsLoad(w) => Ok(vec![tls_node(mn, ops, w, true)?]),
        Mnemonic::TlsStore(w) => Ok(vec![tls_node(mn, ops, w, false)?]),
        Mnemonic::TlsLea => Ok(vec![tls_lea_node(mn, ops)?]),

        Mnemonic::Add(w) => Ok(vec![Inst::Add {
            w,
            op: alu3(mn, ops)?,
        }]),
        Mnemonic::Sub(w) => Ok(vec![Inst::Sub {
            w,
            op: alu3(mn, ops)?,
        }]),
        Mnemonic::Mul(w) => Ok(vec![mul_node(mn, w, ops)?]),
        Mnemonic::And(w) => Ok(vec![Inst::And {
            w,
            op: alu3(mn, ops)?,
        }]),
        Mnemonic::Or(w) => Ok(vec![Inst::Or {
            w,
            op: alu3(mn, ops)?,
        }]),
        Mnemonic::Xor(w) => Ok(vec![Inst::Xor {
            w,
            op: alu3(mn, ops)?,
        }]),
        Mnemonic::FBit { or, k } => fbit_node(mn, ops, k, or),
        Mnemonic::Not(w) => Ok(vec![Inst::Not {
            w,
            dst: one(mn, ops)?,
        }]),
        Mnemonic::Neg(w) => Ok(vec![Inst::Neg {
            w,
            dst: one(mn, ops)?,
        }]),
        Mnemonic::Shift { w, op } => shift_node(mn, w, op, ops, sc),
        Mnemonic::Bswap(w) => Ok(vec![bswap_node(mn, ops, w)?]),
        Mnemonic::Adc => Ok(vec![adc_node(mn, ops, false)?]),
        Mnemonic::Sbb => Ok(vec![adc_node(mn, ops, true)?]),
        Mnemonic::MulHigh { signed } => Ok(vec![Inst::MulHigh {
            signed,
            rhs: one(mn, ops)?,
        }]),
        Mnemonic::MulWide { signed } => Ok(vec![mulwide_node(mn, ops, signed)?]),
        Mnemonic::AluS { op, w } => Ok(vec![Inst::AluS {
            op,
            w,
            alu: alu3(mn, ops)?,
        }]),
        Mnemonic::RiscAluS { op, w } => {
            let has_label =
                matches!(ops.last(), Some(Op::Label(_))) && (ops.len() == 3 || ops.len() == 4);
            if has_label {
                let flag_op = match op {
                    AluOp::Add => FlagAlu::Add,
                    AluOp::Sub => FlagAlu::Sub,
                    AluOp::Or => FlagAlu::Or,
                };
                return Ok(vec![Inst::OpBranch {
                    op: flag_op,
                    w,
                    flag: PredFlag::S,
                    args: op_branch_args(mn, &ops[..ops.len() - 1])?,
                    target: label_op(
                        mn,
                        ops.last()
                            .ok_or_else(|| bad(mn, "op-branch takes 3 or 4 operands"))?,
                    )?,
                    patch,
                }]);
            }
            Ok(vec![Inst::AluS {
                op,
                w,
                alu: alu3(mn, ops)?,
            }])
        }
        Mnemonic::AddShifted => Ok(vec![addshifted_node(mn, ops)?]),
        Mnemonic::Cqo { quad } => Ok(vec![Inst::Cqo { quad }]),
        Mnemonic::DivMod1 { signed, w } => Ok(vec![Inst::DivMod1 {
            signed,
            w,
            divisor: one(mn, ops)?,
        }]),
        Mnemonic::Div { signed, w } => div_rem_node(mn, ops, signed, w, false),
        Mnemonic::Rem { signed, w } => div_rem_node(mn, ops, signed, w, true),
        Mnemonic::IntSet { w, cc } => {
            expect_len(mn, ops, 3)?;
            Ok(vec![Inst::IntSet {
                cc,
                w,
                dst: ops[0],
                lhs: ops[1],
                rhs: ops[2],
            }])
        }
        Mnemonic::TestSet { w, test } => test_set_node(mn, ops, w, test),
        Mnemonic::Cmov { zero } => Ok(vec![cmov_node(mn, ops, zero)?]),
        Mnemonic::BitCount { w, trailing } => Ok(vec![cz_node(mn, ops, w, trailing)?]),
        Mnemonic::Popcnt(w) => Ok(vec![popcnt_node(mn, ops, w)?]),
        Mnemonic::Bfi => bfi_node(mn, ops, sc),
        Mnemonic::IntBranch { w, cc } => {
            expect_len(mn, ops, 3)?;
            Ok(vec![Inst::Branch {
                cc,
                w,
                lhs: ops[0],
                rhs: ops[1],
                target: label_op(mn, &ops[2])?,
                patch,
            }])
        }
        Mnemonic::TestBranch { w, test } => test_branch_node(mn, ops, w, test, patch),
        Mnemonic::OpBranch { op, w, flag } => {
            if ops.len() != 3 && ops.len() != 4 {
                return Err(bad(mn, "op-branch takes 3 or 4 operands"));
            }
            Ok(vec![Inst::OpBranch {
                op,
                w,
                flag,
                args: op_branch_args(mn, &ops[..ops.len() - 1])?,
                target: label_op(
                    mn,
                    ops.last()
                        .ok_or_else(|| bad(mn, "op-branch takes 3 or 4 operands"))?,
                )?,
                patch,
            }])
        }
        Mnemonic::FlagBranch(flag) => Ok(vec![flag_branch_node(mn, ops, flag, patch)?]),
        Mnemonic::BranchF { cc, k } => {
            expect_len(mn, ops, 3)?;
            let (cc, reverse) = float_cc(cc);
            let (lhs, rhs) = if reverse {
                (ops[1], ops[0])
            } else {
                (ops[0], ops[1])
            };
            Ok(vec![Inst::BranchF {
                cc,
                k,
                lhs,
                rhs,
                target: label_op(mn, &ops[2])?,
                patch,
            }])
        }
        Mnemonic::Jmp => {
            expect_len(mn, ops, 1)?;
            Ok(vec![Inst::Jump {
                target: jump_target(mn, &ops[0])?,
                patch,
            }])
        }
        Mnemonic::Call => {
            expect_len(mn, ops, 1)?;
            Ok(vec![Inst::Call {
                target: jump_target(mn, &ops[0])?,
                patch,
            }])
        }
        Mnemonic::Ret => {
            expect_len(mn, ops, 0)?;
            Ok(vec![Inst::Ret])
        }
        Mnemonic::Break => {
            expect_len(mn, ops, 0)?;
            Ok(vec![Inst::Break])
        }
        Mnemonic::Nop => {
            expect_len(mn, ops, 0)?;
            Ok(vec![Inst::Nop])
        }
        Mnemonic::FArith { op, k } => farith_node(mn, ops, k, op),
        Mnemonic::Fma { op, k } => Ok(vec![fma_node(mn, ops, k, op)?]),
        Mnemonic::FSqrt(k) => Ok(vec![fsqrt_node(mn, ops, k)?]),
        Mnemonic::FRound { k, mode } => Ok(vec![fround_node(mn, ops, k, mode)?]),
        Mnemonic::FAbs { k, negate } => Ok(vec![fabs_node(mn, ops, k, negate)?]),
        Mnemonic::FSet { cc, k } => {
            expect_len(mn, ops, 3)?;
            let (cc, reverse) = float_cc(cc);
            let (lhs, rhs) = if reverse {
                (ops[2], ops[1])
            } else {
                (ops[1], ops[2])
            };
            Ok(vec![Inst::FSet {
                cc,
                k,
                dst: ops[0],
                lhs,
                rhs,
            }])
        }
        Mnemonic::CvtFI { k, w } => Ok(vec![cvtfi_node(mn, ops, k, w)?]),
        Mnemonic::CvtQuad(k) => quad_to_fp(mn, ops, sc, k),
        Mnemonic::CvtIF { signed, from, k } => Ok(vec![cvtif_node(mn, ops, signed, from, k)?]),
        Mnemonic::CvtFF { from, to } => Ok(vec![cvtff_node(mn, ops, from, to)?]),
        Mnemonic::Bitcast(dir) => Ok(vec![bitcast_node(mn, ops, dir)?]),
        Mnemonic::MovDZ => Ok(vec![movdz_node(mn, ops)?]),
        Mnemonic::TruncQSlow(k) => trunc_q_slow(mn, ops, sc, k),
        Mnemonic::Btd2i => btd2i_node(mn, ops),
        Mnemonic::Bcd2i => bcd2i_node(mn, ops, sc),
        Mnemonic::VecExtract(w) => Ok(vec![umov_node(mn, ops, w)?]),
        Mnemonic::AtomicRmw { op, w } => Ok(vec![rmw_node(mn, ops, w, op)?]),
        Mnemonic::AtomicRmwNot(w) => rmw_not_node(mn, ops, sc, w, AtomicOp::And),
        Mnemonic::AtomicCas { w, branch } => Ok(vec![cas_node(mn, ops, w, branch)?]),
        Mnemonic::LoadLinked(w) => Ok(vec![ll_node(mn, ops, w)?]),
        Mnemonic::StoreCond(w) => Ok(vec![sc_node(mn, ops, w)?]),
        Mnemonic::Fence { full } => Ok(vec![Inst::Fence { full }]),
        Mnemonic::Pause => Ok(vec![Inst::Pause]),
        Mnemonic::TagCodePtr
        | Mnemonic::TagReturnAddress
        | Mnemonic::UntagReturnAddress
        | Mnemonic::RemoveCodePtrTag
        | Mnemonic::UntagArrayPtr
        | Mnemonic::RemoveArrayPtrTag => Ok(vec![]),
    }
}

fn flag_branch_node(
    mn: Mnemonic,
    ops: &[Op],
    flag: PredFlag,
    patch: bool,
) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 1)?;
    Ok(Inst::FlagBranch {
        flag,
        target: label_op(mn, &ops[0])?,
        patch,
    })
}

fn popcnt_node(mn: Mnemonic, ops: &[Op], w: Width) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::Popcnt {
        w,
        dst: gpr_op(mn, &ops[0])?,
        src: ops[1],
    })
}

fn cz_node(mn: Mnemonic, ops: &[Op], w: Width, trailing: bool) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    let dst = gpr_op(mn, &ops[0])?;
    let inst = if trailing {
        Inst::Ctz {
            w,
            dst,
            src: ops[1],
        }
    } else {
        Inst::Clz {
            w,
            dst,
            src: ops[1],
        }
    };
    Ok(inst)
}

fn tls_node(mn: Mnemonic, ops: &[Op], w: Width, load: bool) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    if load {
        let idx = imm_op(mn, &ops[1])?;
        Ok(Inst::TlsLoad {
            w,
            dst: gpr_op(mn, &ops[0])?,
            idx,
        })
    } else {
        let idx = imm_op(mn, &ops[0])?;
        Ok(Inst::TlsStore {
            w,
            src: gpr_op(mn, &ops[1])?,
            idx,
        })
    }
}

fn tls_lea_node(mn: Mnemonic, ops: &[Op]) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::TlsLea {
        dst: gpr_op(mn, &ops[0])?,
        idx: imm_op(mn, &ops[1])?,
    })
}

fn rmw_node(mn: Mnemonic, ops: &[Op], w: Width, op: AtomicOp) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;

    Ok(Inst::AtomicRmw {
        op,
        w,
        a: ops[1],
        b: ops[0],
    })
}

fn rmw_not_node(
    mn: Mnemonic,
    ops: &[Op],
    sc: &Scratch,
    w: Width,
    op: AtomicOp,
) -> Result<Vec<Inst>, ExpandError> {
    expect_len(mn, ops, 2)?;
    let mut out = Vec::new();
    // `mem` is ops[0] and `src` is ops[1].
    let a = match &ops[1] {
        Op::Imm(v) => Op::Imm(!v),
        Op::Gpr(g) => {
            out.push(Inst::Mov {
                w: Width::B64,
                dst: Op::Gpr(sc.gpr),
                src: Op::Gpr(*g),
                patch: false,
            });
            out.push(Inst::Not {
                w,
                dst: Op::Gpr(sc.gpr),
            });
            Op::Gpr(sc.gpr)
        }
        Op::Mem(addr) => {
            let lw = if w == Width::B64 {
                Width::B64
            } else {
                Width::B32
            };
            out.push(Inst::Load {
                w: lw,
                sx: Sx::Zero,
                dst: sc.gpr,
                addr: *addr,
                acquire: false,
            });
            out.push(Inst::Not {
                w,
                dst: Op::Gpr(sc.gpr),
            });
            Op::Gpr(sc.gpr)
        }
        _ => {
            return Err(bad(
                mn,
                "atomic clear needs an immediate, register, or memory operand",
            ))
        }
    };
    out.push(Inst::AtomicRmw {
        op,
        w,
        a,
        b: ops[0],
    });
    Ok(out)
}

fn cas_node(mn: Mnemonic, ops: &[Op], w: Width, branch: bool) -> Result<Inst, ExpandError> {
    let n = if branch { 4 } else { 3 };
    expect_len(mn, ops, n)?;

    Ok(Inst::AtomicCas {
        w,
        mem: mem_op(mn, &ops[0])?,
        src: gpr_op(mn, &ops[2])?,
        branch: if branch {
            Some(label_op(mn, &ops[3])?)
        } else {
            None
        },
    })
}

fn ll_node(mn: Mnemonic, ops: &[Op], w: Width) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::LoadLinked {
        w,
        mem: mem_op(mn, &ops[1])?,
        dst: gpr_op(mn, &ops[0])?,
    })
}

fn sc_node(mn: Mnemonic, ops: &[Op], w: Width) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 3)?;
    Ok(Inst::StoreCond {
        w,
        status: gpr_op(mn, &ops[1])?,
        src: gpr_op(mn, &ops[2])?,
        mem: mem_op(mn, &ops[0])?,
    })
}

/// Expands `bfiq` to a mask, shift, and OR sequence.
///
/// Computes `dst = (dst & ~mask) | ((src & wmask) << lsb)`.
fn bfi_node(mn: Mnemonic, ops: &[Op], sc: &Scratch) -> Result<Vec<Inst>, ExpandError> {
    expect_len(mn, ops, 4)?;
    let lsb = imm_op(mn, &ops[2])?;
    let width = imm_op(mn, &ops[3])?;
    if !(1..=64).contains(&width) || lsb < 0 || lsb + width > 64 {
        return Err(bad(mn, "bitfield out of range"));
    }
    let wmask: u64 = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let mask: i64 = (wmask << lsb) as i64;
    let s = sc.gpr;
    let dst = gpr_op(mn, &ops[0])?;

    Ok(vec![
        Inst::Mov {
            w: Width::B64,
            dst: Op::Gpr(s),
            src: ops[1],
            patch: false,
        },
        Inst::And {
            w: Width::B64,
            op: Alu3 {
                dst: Op::Gpr(s),
                lhs: Op::Gpr(s),
                rhs: Op::Imm(wmask as i64),
            },
        },
        Inst::Shift {
            w: Width::B64,
            op: ShiftOp::Shl,
            dst: s,
            cnt: ShiftCnt::Imm(lsb),
        },
        Inst::And {
            w: Width::B64,
            op: Alu3 {
                dst: Op::Gpr(dst),
                lhs: Op::Gpr(dst),
                rhs: Op::Imm(!mask),
            },
        },
        Inst::Or {
            w: Width::B64,
            op: Alu3 {
                dst: Op::Gpr(dst),
                lhs: Op::Gpr(dst),
                rhs: Op::Gpr(s),
            },
        },
    ])
}

fn cmov_node(mn: Mnemonic, ops: &[Op], zero: bool) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 3)?;
    Ok(Inst::Cmov {
        w: Width::B64,
        zero,
        dst: gpr_op(mn, &ops[0])?,
        src: ops[1],
        test: gpr_op(mn, &ops[2])?,
    })
}

/// Expands `peek dst, off` and `poke off, src`, with the destination first
/// in both. The offset counts quad slots and is scaled here.
fn peek_node(mn: Mnemonic, ops: &[Op], peek: bool) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    if peek {
        let disp = slot_disp(mn, &ops[1])?;
        return Ok(Inst::Peek {
            disp,
            dst: gpr_op(mn, &ops[0])?,
        });
    }
    Ok(Inst::Poke {
        disp: slot_disp(mn, &ops[0])?,
        src: gpr_op(mn, &ops[1])?,
    })
}

fn slot_disp(mn: Mnemonic, op: &Op) -> Result<i32, ExpandError> {
    let idx = imm_op(mn, op)?;
    let off = idx
        .checked_mul(8)
        .ok_or_else(|| bad(mn, "stack offset overflow"))?;
    if off < i32::MIN as i64 || off > i32::MAX as i64 {
        return Err(bad(mn, "stack offset out of range"));
    }
    Ok(off as i32)
}

fn loadqinc_node(mn: Mnemonic, ops: &[Op]) -> Result<Vec<Inst>, ExpandError> {
    expect_len(mn, ops, 3)?;
    let dst = gpr_op(mn, &ops[0])?;
    let base = gpr_op(mn, &ops[1])?;
    let inc = imm_op(mn, &ops[2])?;
    Ok(vec![
        Inst::Load {
            w: Width::B64,
            sx: Sx::Zero,
            dst,
            addr: Mem::base(base, 0),
            acquire: false,
        },
        Inst::Add {
            w: Width::B64,
            op: Alu3 {
                dst: Op::Gpr(base),
                lhs: Op::Gpr(base),
                rhs: Op::Imm(inc),
            },
        },
    ])
}

fn pair_node(mn: Mnemonic, ops: &[Op], w: PairW, load: bool) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 3)?;
    if load {
        Ok(Inst::PairLoad {
            w,
            dst1: ops[0],
            dst2: ops[1],
            mem: mem_op(mn, &ops[2])?,
        })
    } else {
        Ok(Inst::PairStore {
            w,
            src1: ops[1],
            src2: ops[2],
            mem: mem_op(mn, &ops[0])?,
        })
    }
}

fn lea_node(mn: Mnemonic, ops: &[Op], w: Width) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    let dst = gpr_op(mn, &ops[0])?;
    let src = match &ops[1] {
        Op::Mem(a) => LeaSrc::Mem(*a),
        Op::Label(l) => LeaSrc::Label(*l),
        Op::Extern(e) => LeaSrc::Extern(*e),
        _ => return Err(bad(mn, "lea needs an address or label source")),
    };
    Ok(Inst::Lea { w, dst, src })
}

fn mov_node(mn: Mnemonic, ops: &[Op], w: Width, patch: bool) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    // `move reg, extern` takes the symbol's address, like `leap`.
    if let (Op::Gpr(dst), Op::Extern(e)) = (&ops[0], &ops[1]) {
        return Ok(Inst::Lea {
            w: Width::B64,
            dst: *dst,
            src: LeaSrc::Extern(*e),
        });
    }
    Ok(Inst::Mov {
        w,
        dst: ops[0],
        src: ops[1],
        patch,
    })
}

fn movzero_node(mn: Mnemonic, ops: &[Op]) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::MovZero32 {
        dst: ops[0],
        src: ops[1],
    })
}

fn atomic_load_node(mn: Mnemonic, ops: &[Op], w: Width) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::Load {
        w,
        sx: Sx::Zero,
        dst: gpr_op(mn, &ops[0])?,
        addr: mem_op(mn, &ops[1])?,
        acquire: true,
    })
}

fn store_node(mn: Mnemonic, ops: &[Op], w: Width) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    let addr = mem_op(mn, &ops[0])?;
    Ok(Inst::Store {
        w,
        src: ops[1],
        addr,
    })
}

fn extend_node(
    mn: Mnemonic,
    ops: &[Op],
    from: Width,
    to: Width,
    sx: Sx,
) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::Extend {
        from,
        to,
        sx,
        dst: gpr_op(mn, &ops[0])?,
        src: ops[1],
    })
}

fn transfer_node(
    mn: Mnemonic,
    ops: &[Op],
    sc: &Scratch,
    w: Width,
) -> Result<Vec<Inst>, ExpandError> {
    expect_len(mn, ops, 2)?;
    let mut out = Vec::new();
    match &ops[1] {
        Op::Gpr(_) => {}
        Op::Mem(a) => {
            out.push(Inst::Load {
                w,
                sx: Sx::Zero,
                dst: sc.gpr,
                addr: *a,
                acquire: false,
            });
        }
        Op::Imm(v) => {
            out.push(Inst::Mov {
                w,
                dst: Op::Gpr(sc.gpr),
                src: Op::Imm(*v),
                patch: false,
            });
        }
        Op::Label(l) => {
            out.push(Inst::Lea {
                w: Width::B64,
                dst: sc.gpr,
                src: LeaSrc::Label(*l),
            });
            let addr = Mem::base(sc.gpr, 0);
            out.push(Inst::Load {
                w,
                sx: Sx::Zero,
                dst: sc.gpr,
                addr,
                acquire: false,
            });
        }
        Op::Fpr(_) => return Err(bad(mn, "cannot transfer from an FPR")),
        Op::Sym(_) => return Err(bad(mn, "cannot transfer from a symbolic operand")),
        Op::Extern(_) => return Err(bad(mn, "cannot transfer from an external symbol")),
    }
    let src = if out.is_empty() {
        ops[1]
    } else {
        Op::Gpr(sc.gpr)
    };
    out.push(Inst::Mov {
        w,
        dst: ops[0],
        src,
        patch: false,
    });
    Ok(out)
}

fn fmove_node(mn: Mnemonic, ops: &[Op], k: FKind) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    match (&ops[0], &ops[1]) {
        (Op::Fpr(d), Op::Fpr(s)) => Ok(Inst::FMov {
            k,
            dst: *d,
            src: *s,
        }),
        (Op::Fpr(d), Op::Mem(a)) => Ok(Inst::LoadF {
            k,
            dst: *d,
            addr: *a,
        }),
        (Op::Mem(a), Op::Fpr(s)) => Ok(Inst::StoreF {
            k,
            src: *s,
            addr: *a,
        }),
        _ => Err(bad(mn, "float move needs FPR/memory operands")),
    }
}

fn vmove_node(mn: Mnemonic, ops: &[Op], store: bool) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    if !store {
        match (&ops[0], &ops[1]) {
            (Op::Fpr(d), Op::Fpr(s)) => Ok(Inst::VMov { dst: *d, src: *s }),
            (Op::Fpr(d), Op::Mem(a)) => Ok(Inst::LoadV { dst: *d, addr: *a }),
            (Op::Fpr(d), Op::Gpr(s)) => Ok(Inst::LoadV {
                dst: *d,
                addr: Mem::base(*s, 0),
            }),
            _ => Err(bad(mn, "vector move needs FPR/memory operands")),
        }
    } else {
        match (&ops[0], &ops[1]) {
            (Op::Fpr(d), Op::Fpr(s)) => Ok(Inst::VMov { dst: *d, src: *s }),
            (Op::Fpr(d), Op::Mem(a)) => Ok(Inst::LoadV { dst: *d, addr: *a }),
            (Op::Fpr(d), Op::Gpr(s)) => Ok(Inst::LoadV {
                dst: *d,
                addr: Mem::base(*s, 0),
            }),
            (Op::Mem(a), Op::Fpr(s)) => Ok(Inst::StoreV { src: *s, addr: *a }),
            _ => Err(bad(mn, "vector move needs FPR/memory operands")),
        }
    }
}

/// Checks that every callee-save operand is a GPR in `saved`.
///
/// Does nothing for every other mnemonic.
///
/// # Errors
///
/// [`ExpandError::BadOperand`] if `mnemonic` is `PushCalleeSaves` or
/// `PopCalleeSaves` and `ops` contains a non-GPR operand or a GPR whose
/// number is not in `saved`.
pub fn check_callee_saved(mnemonic: Mnemonic, ops: &[Op], saved: &[u8]) -> Result<(), ExpandError> {
    if !matches!(
        mnemonic,
        Mnemonic::PushCalleeSaves | Mnemonic::PopCalleeSaves
    ) {
        return Ok(());
    }
    for op in ops {
        match op {
            Op::Gpr(g) if saved.contains(&g.0) => {}
            _ => return Err(bad(mnemonic, "needs callee-saved GPRs")),
        }
    }
    Ok(())
}

/// Bytes one AArch64 `push`/`pop` of `n` quads moves `sp` by: `8 * n`
/// rounded up to 16, because `sp` must stay 16-byte aligned whenever it is
/// used as a base address.
///
/// The operands keep the layout they have on the targets with 8-byte slots
/// (see [`aligned_push_offset`]), and an odd count leaves one padding word
/// above them. A `pop` must name as many operands as the `push` it undoes.
pub fn aligned_push_bytes(n: usize) -> i32 {
    ((8 * n + 15) & !15) as i32
}

/// Offset from the lowered `sp` of operand `i` in an `n`-operand AArch64
/// `push`/`pop` group. The last operand sits at `[sp]`, as it would after
/// `n` separate 8-byte pushes.
pub fn aligned_push_offset(n: usize, i: usize) -> i32 {
    8 * (n - 1 - i) as i32
}

fn stack_nodes(
    mn: Mnemonic,
    ops: &[Op],
    push: bool,
    vector: bool,
) -> Result<Vec<Inst>, ExpandError> {
    if ops.is_empty() {
        return Err(bad(mn, "needs at least one operand"));
    }
    let mut out = Vec::with_capacity(ops.len());
    // `push a, b` stores `a` then `b`, leaving `b` on top; `pop a, b` must
    // unwind LIFO, so it reads `b` before `a` - the reverse of the operand
    // list order that `push` uses.
    let ordered: Box<dyn Iterator<Item = &Op>> = if push {
        Box::new(ops.iter())
    } else {
        Box::new(ops.iter().rev())
    };
    for op in ordered {
        if vector {
            let x = fpr_op(mn, op)?;
            out.push(if push {
                Inst::PushV { src: x }
            } else {
                Inst::PopV { dst: x }
            });
        } else {
            match op {
                Op::Gpr(_) | Op::Mem(_) | Op::Imm(_) => {
                    out.push(if push {
                        Inst::Push { op: *op }
                    } else {
                        Inst::Pop { op: *op }
                    });
                }
                _ => return Err(bad(mn, "push/pop needs registers, memory, or immediates")),
            }
        }
    }
    Ok(out)
}

fn mul_node(mn: Mnemonic, w: Width, ops: &[Op]) -> Result<Inst, ExpandError> {
    if ops.len() == 3 {
        if let (Op::Imm(v), Ok(lhs)) = (&ops[1], gpr_op(mn, &ops[2])) {
            return Ok(Inst::MulImm {
                w,
                dst: gpr_op(mn, &ops[0])?,
                lhs,
                imm: *v,
            });
        }
        if let (Ok(lhs), Op::Imm(v)) = (gpr_op(mn, &ops[1]), &ops[2]) {
            return Ok(Inst::MulImm {
                w,
                dst: gpr_op(mn, &ops[0])?,
                lhs,
                imm: *v,
            });
        }
    }
    Ok(Inst::Mul {
        w,
        op: Alu3::from_operands(mn, ops)?,
    })
}

fn mulwide_node(mn: Mnemonic, ops: &[Op], signed: bool) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 3)?;
    Ok(Inst::MulWide {
        signed,
        dst: gpr_op(mn, &ops[0])?,
        lhs: gpr_op(mn, &ops[1])?,
        rhs: gpr_op(mn, &ops[2])?,
    })
}

fn addshifted_node(mn: Mnemonic, ops: &[Op]) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 4)?;
    let amount = imm_op(mn, &ops[3])?;
    if !(0..=63).contains(&amount) {
        return Err(bad(mn, "shift amount out of range"));
    }
    Ok(Inst::AddShifted {
        dst: gpr_op(mn, &ops[0])?,
        lhs: gpr_op(mn, &ops[1])?,
        rhs: gpr_op(mn, &ops[2])?,
        amount: amount as u8,
    })
}

fn adc_node(mn: Mnemonic, ops: &[Op], borrow: bool) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    let inst = if borrow {
        Inst::Sbb {
            dst: ops[0],
            src: ops[1],
        }
    } else {
        Inst::Adc {
            dst: ops[0],
            src: ops[1],
        }
    };
    Ok(inst)
}

fn fbit_node(mn: Mnemonic, ops: &[Op], k: FKind, or: bool) -> Result<Vec<Inst>, ExpandError> {
    if ops.len() != 2 && ops.len() != 3 {
        return Err(bad(mn, "fp bitwise takes 2 or 3 operands"));
    }
    let mut out = Vec::new();
    let (src, dst) = if ops.len() == 3 {
        let d = fpr_op(mn, &ops[0])?;
        if op_eq(&ops[2], &ops[0]) && !op_eq(&ops[1], &ops[0]) {
            // `O1 = O2 op O1`: and/or commute, so fold `O2` into `O1`.
            (ops[1], d)
        } else {
            if !op_eq(&ops[1], &ops[0]) {
                match &ops[1] {
                    Op::Fpr(s) => out.push(Inst::FMov { k, dst: d, src: *s }),
                    Op::Mem(a) => out.push(Inst::LoadF {
                        k,
                        dst: d,
                        addr: *a,
                    }),
                    _ => return Err(bad(mn, "fp bitwise needs FPR/memory operands")),
                }
            }
            (ops[2], d)
        }
    } else {
        (ops[1], fpr_op(mn, &ops[0])?)
    };
    out.push(Inst::FBit { or, k, dst, src });
    Ok(out)
}

fn farith_node(mn: Mnemonic, ops: &[Op], k: FKind, op: FAlu) -> Result<Vec<Inst>, ExpandError> {
    if ops.len() == 3 {
        return Ok(vec![Inst::FArith {
            op,
            k,
            arith: FArith3 {
                dst: fpr_op(mn, &ops[0])?,
                lhs: ops[1],
                rhs: Some(ops[2]),
            },
        }]);
    }
    Ok(vec![Inst::FArith {
        op,
        k,
        arith: FArith3::from_operands(mn, ops)?,
    }])
}

fn fsqrt_node(mn: Mnemonic, ops: &[Op], k: FKind) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::FSqrt {
        k,
        dst: fpr_op(mn, &ops[0])?,
        src: ops[1],
    })
}

fn fma_node(mn: Mnemonic, ops: &[Op], k: FKind, op: FmaOp) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 4)?;
    Ok(Inst::Fma {
        op,
        k,
        a: ops[1],
        b: ops[2],
        c: ops[3],
        dst: fpr_op(mn, &ops[0])?,
    })
}

/// Reverses the bytes of `src` into `dst`.
fn bswap_node(mn: Mnemonic, ops: &[Op], w: Width) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::Bswap {
        w,
        dst: ops[0],
        src: ops[1],
    })
}

fn fround_node(mn: Mnemonic, ops: &[Op], k: FKind, mode: RoundMode) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::FRound {
        k,
        mode,
        dst: fpr_op(mn, &ops[0])?,
        src: ops[1],
    })
}

fn cvtfi_node(mn: Mnemonic, ops: &[Op], k: FKind, w: Width) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::CvtFI {
        k,
        w,
        dst: gpr_op(mn, &ops[0])?,
        src: ops[1],
    })
}

fn cvtif_node(
    mn: Mnemonic,
    ops: &[Op],
    signed: bool,
    from: Width,
    k: FKind,
) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::CvtIF {
        signed,
        from,
        k,
        dst: fpr_op(mn, &ops[0])?,
        src: ops[1],
    })
}

fn cvtff_node(mn: Mnemonic, ops: &[Op], from: FKind, to: FKind) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::CvtFF {
        from,
        to,
        dst: fpr_op(mn, &ops[0])?,
        src: ops[1],
    })
}

fn bitcast_node(mn: Mnemonic, ops: &[Op], dir: BitcastDir) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    Ok(Inst::Bitcast {
        dir,
        dst: ops[0],
        src: ops[1],
    })
}

fn fabs_node(mn: Mnemonic, ops: &[Op], k: FKind, negate: bool) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 2)?;
    let dst = fpr_op(mn, &ops[0])?;
    let inst = if negate {
        Inst::FNeg {
            k,
            dst,
            src: ops[1],
        }
    } else {
        Inst::FAbs {
            k,
            dst,
            src: ops[1],
        }
    };
    Ok(inst)
}

fn umov_node(mn: Mnemonic, ops: &[Op], w: Width) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 3)?;
    let lane = imm_op(mn, &ops[2])?;
    let lanes: i64 = 128 / w.bytes() as i64;
    if lane < 0 || lane >= lanes {
        return Err(bad(mn, "lane out of range"));
    }
    Ok(Inst::VecExtract {
        w,
        dst: gpr_op(mn, &ops[0])?,
        src: fpr_op(mn, &ops[1])?,
        lane: lane as u8,
    })
}

fn trunc_q_slow(
    mn: Mnemonic,
    ops: &[Op],
    sc: &Scratch,
    k: FKind,
) -> Result<Vec<Inst>, ExpandError> {
    expect_len(mn, ops, 2)?;
    let (dst, src) = (ops[0], ops[1]);
    let slow = Lbl::Fresh(0);
    let done = Lbl::Fresh(1);
    let gs = Op::Gpr(sc.gpr);
    let fs = Op::Fpr(sc.fpr);
    let (int64_min, neg_min) = match k {
        FKind::F32 => (0xdf000000i64, 0x5f000000i64),
        FKind::F64 => (0xc3e0000000000000u64 as i64, 0x43e0000000000000u64 as i64),
    };
    let dst_gpr = gpr_op(mn, &dst)?;
    Ok(vec![
        Inst::Mov {
            w: Width::B64,
            dst: gs,
            src: Op::Imm(neg_min),
            patch: false,
        },
        Inst::Bitcast {
            dir: if k == FKind::F32 {
                BitcastDir::I2F
            } else {
                BitcastDir::Q2D
            },
            dst: fs,
            src: gs,
        },
        Inst::BranchF {
            cc: FCc::Ge,
            k,
            lhs: src,
            rhs: fs,
            target: slow,
            patch: false,
        },
        Inst::CvtFI {
            k,
            w: Width::B64,
            dst: dst_gpr,
            src,
        },
        Inst::Jump {
            target: Target::Label(done),
            patch: false,
        },
        Inst::Bind(slow),
        Inst::Mov {
            w: Width::B64,
            dst: gs,
            src: Op::Imm(int64_min),
            patch: false,
        },
        Inst::Bitcast {
            dir: if k == FKind::F32 {
                BitcastDir::I2F
            } else {
                BitcastDir::Q2D
            },
            dst: fs,
            src: gs,
        },
        Inst::FArith {
            op: FAlu::Add,
            k,
            arith: FArith3 {
                dst: sc.fpr,
                lhs: src,
                rhs: None,
            },
        },
        Inst::CvtFI {
            k,
            w: Width::B64,
            dst: dst_gpr,
            src: fs,
        },
        Inst::Mov {
            w: Width::B64,
            dst: gs,
            src: Op::Imm(0x8000000000000000u64 as i64),
            patch: false,
        },
        Inst::Or {
            w: Width::B64,
            op: Alu3 {
                dst,
                lhs: dst,
                rhs: gs,
            },
        },
        Inst::Bind(done),
    ])
}

fn quad_to_fp(mn: Mnemonic, ops: &[Op], sc: &Scratch, k: FKind) -> Result<Vec<Inst>, ExpandError> {
    expect_len(mn, ops, 3)?;
    let (src, dst) = (ops[1], ops[0]);
    let slow = Lbl::Fresh(0);
    let done = Lbl::Fresh(1);
    let s1 = gpr_op(mn, &ops[2])?;
    let s2 = sc.gpr;
    let dst_fpr = fpr_op(mn, &dst)?;
    Ok(vec![
        Inst::TestBranch {
            w: Width::B64,
            value: src,
            mask: None,
            test: TestKind::Sign,
            target: slow,
            patch: false,
        },
        Inst::CvtIF {
            signed: true,
            from: Width::B64,
            k,
            dst: dst_fpr,
            src,
        },
        Inst::Jump {
            target: Target::Label(done),
            patch: false,
        },
        Inst::Bind(slow),
        Inst::Mov {
            w: Width::B64,
            dst: Op::Gpr(s1),
            src,
            patch: false,
        },
        Inst::Mov {
            w: Width::B64,
            dst: Op::Gpr(s2),
            src,
            patch: false,
        },
        Inst::Shift {
            w: Width::B64,
            op: ShiftOp::Shr,
            dst: s1,
            cnt: ShiftCnt::Imm(1),
        },
        Inst::And {
            w: Width::B64,
            op: Alu3 {
                dst: Op::Gpr(s2),
                lhs: Op::Gpr(s2),
                rhs: Op::Imm(1),
            },
        },
        Inst::Or {
            w: Width::B64,
            op: Alu3 {
                dst: Op::Gpr(s2),
                lhs: Op::Gpr(s2),
                rhs: Op::Gpr(s1),
            },
        },
        Inst::CvtIF {
            signed: true,
            from: Width::B64,
            k,
            dst: dst_fpr,
            src: Op::Gpr(s2),
        },
        Inst::FArith {
            op: FAlu::Add,
            k,
            arith: FArith3 {
                dst: dst_fpr,
                lhs: Op::Fpr(dst_fpr),
                rhs: None,
            },
        },
        Inst::Bind(done),
    ])
}

/// Expands `btd2i` to a convert plus an overflow-sentinel branch.
///
/// Takes the branch when the low 32 bits equal `0x80000000`.
fn btd2i_node(mn: Mnemonic, ops: &[Op]) -> Result<Vec<Inst>, ExpandError> {
    expect_len(mn, ops, 3)?;
    Ok(vec![
        Inst::CvtFI {
            k: FKind::F64,
            w: Width::B64,
            dst: gpr_op(mn, &ops[0])?,
            src: ops[1],
        },
        Inst::Branch {
            cc: IntCc::Eq,
            w: Width::B32,
            lhs: ops[0],
            rhs: Op::Imm(-0x8000_0000i64),
            target: label_op(mn, &ops[2])?,
            patch: false,
        },
    ])
}

fn bcd2i_node(mn: Mnemonic, ops: &[Op], sc: &Scratch) -> Result<Vec<Inst>, ExpandError> {
    expect_len(mn, ops, 3)?;
    let target = label_op(mn, &ops[2])?;
    Ok(vec![
        Inst::CvtFI {
            k: FKind::F64,
            w: Width::B64,
            dst: gpr_op(mn, &ops[0])?,
            src: ops[1],
        },
        Inst::TestBranch {
            w: Width::B64,
            value: ops[0],
            mask: None,
            test: TestKind::Zero,
            target,
            patch: false,
        },
        Inst::CvtIF {
            signed: true,
            from: Width::B64,
            k: FKind::F64,
            dst: sc.fpr,
            src: ops[0],
        },
        Inst::BranchF {
            cc: FCc::NeUn,
            k: FKind::F64,
            lhs: ops[1],
            rhs: Op::Fpr(sc.fpr),
            target,
            patch: false,
        },
    ])
}

/// Zeros a double by computing `dst -= dst`.
fn movdz_node(mn: Mnemonic, ops: &[Op]) -> Result<Inst, ExpandError> {
    expect_len(mn, ops, 1)?;
    let dst = fpr_op(mn, &ops[0])?;
    Ok(Inst::FArith {
        op: FAlu::Sub,
        k: FKind::F64,
        arith: FArith3 {
            dst,
            lhs: Op::Fpr(dst),
            rhs: None,
        },
    })
}
