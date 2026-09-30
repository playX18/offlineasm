use super::text::{self, TextTarget};
use super::LowerCtx;
use crate::ast::Node;
use offlineasm_ir::{expand, Extern, Inst, Lbl, Mem, Mnemonic, Op, SymId};

type LabelFlags<'a> = &'a dyn Fn(&str) -> (bool, bool, bool, bool, Option<String>);

type Printer = fn(&mut LowerCtx, &Inst) -> Result<(), String>;

fn printer(target: TextTarget) -> Printer {
    match target {
        TextTarget::X86_64 => super::text_x86::emit,
        TextTarget::Aarch64 => super::text_arm64::emit,
        TextTarget::Riscv64 => super::text_riscv64::emit,
    }
}

/// Lowers one `Node::Instruction` for a text target.
///
/// # Errors
///
/// Returns an error if `node` is not an instruction, the mnemonic is unknown,
/// an operand does not lower for `target`, or the printer rejects the
/// expansion.
pub fn lower_instruction(
    node: &Node,
    ctx: &mut LowerCtx,
    flags: LabelFlags,
    target: TextTarget,
    arm64e: bool,
) -> Result<(), String> {
    let (opcode, operands) = match node {
        Node::Instruction {
            opcode, operands, ..
        } => (opcode.as_str(), operands.as_slice()),
        other => return Err(format!("not an instruction: {}", other.dump())),
    };

    match opcode {
        "localAnnotation" => {
            ctx.emitter.put_local_annotation();
            return Ok(());
        }
        "globalAnnotation" => {
            ctx.emitter.put_global_annotation();
            return Ok(());
        }
        "emit" => return emit_raw_text(operands, ctx, flags),
        _ => {}
    }

    let mnemonic = Mnemonic::from_str(opcode).map_err(|e| e.to_string())?;

    if arm64e && super::text_arm64::lower_arm64e(mnemonic, operands, ctx, flags)?.is_some() {
        return Ok(());
    }

    let mut ops = Vec::with_capacity(operands.len());
    for operand in operands {
        ops.push(operand_to_op(operand, ctx, flags, target)?);
    }
    lower_spelled(ctx, target, mnemonic, opcode, &ops)
}

/// Lowers one mnemonic whose operands are already IR [`Op`]s.
///
/// # Errors
///
/// Returns an error if the operands do not fit the mnemonic or the printer
/// rejects the expansion.
pub fn lower_ops(
    ctx: &mut LowerCtx,
    target: TextTarget,
    mnemonic: Mnemonic,
    ops: &[Op],
) -> Result<(), String> {
    lower_spelled(ctx, target, mnemonic, mnemonic.as_str(), ops)
}

fn lower_spelled(
    ctx: &mut LowerCtx,
    target: TextTarget,
    mnemonic: Mnemonic,
    spelling: &str,
    ops: &[Op],
) -> Result<(), String> {
    let scratch = target.scratch();

    let abi = if ctx.setting("WINDOWS") || ctx.is_win {
        crate::registers::Abi::Windows
    } else {
        crate::registers::Abi::SysV
    };
    let saved = crate::registers::callee_saved_gpr_ids(target.name(), abi);
    offlineasm_ir::check_callee_saved(mnemonic, ops, &saved).map_err(|e| e.to_string())?;
    if target == TextTarget::Aarch64
        && matches!(
            mnemonic,
            Mnemonic::Push | Mnemonic::Pop | Mnemonic::PushCalleeSaves | Mnemonic::PopCalleeSaves
        )
    {
        return super::text_arm64::stack_group(ctx, mnemonic, ops);
    }
    let expanded =
        expand(mnemonic, ops, &scratch, false).map_err(|e| e.renamed(spelling).to_string())?;
    intern_expansion_labels(ctx, &expanded);

    let print = printer(target);
    for inst in &expanded {
        print(ctx, inst)?;
    }
    Ok(())
}

fn emit_raw_text(operands: &[Node], ctx: &mut LowerCtx, flags: LabelFlags) -> Result<(), String> {
    let mut s = String::new();
    for operand in operands {
        if let Node::LocalLabelReference { .. } = operand {
            s.push_str(&super::local_ref_name(operand, ctx)?);
        } else {
            s.push_str(&operand.dump());
        }
    }
    let _ = flags;
    ctx.emitter.puts(&s);
    Ok(())
}

fn intern_expansion_labels(ctx: &mut LowerCtx, insts: &[Inst]) {
    ctx.ir_fresh.clear();
    for inst in insts {
        inst.visit_labels(&mut |l: Lbl| {
            if let Lbl::Fresh(i) = l {
                if !ctx.ir_fresh.contains_key(&i) {
                    let name = text::synth_name(ctx, "l", i);
                    ctx.ir_fresh.insert(i, name);
                }
            }
        });
    }
}

/// Converts one source operand to an IR [`Op`].
///
/// # Errors
///
/// Returns an error if the operand shape is unsupported, names an unusable
/// register, or carries an out-of-range scale or displacement.
pub fn operand_to_op(
    node: &Node,
    ctx: &mut LowerCtx,
    flags: LabelFlags,
    target: TextTarget,
) -> Result<Op, String> {
    let regs = target.regs();
    match node {
        Node::Immediate { value, .. } => Ok(Op::Imm(imm_of(node, *value)?)),
        Node::Register { name, .. } => regs
            .resolve_gpr_name(name)
            .map(Op::Gpr)
            .ok_or_else(|| format!("cannot use register {} on {}", name, target.name())),
        Node::FpRegister { name, .. } | Node::VecRegister { name, .. } => regs
            .resolve_fpr_name(name)
            .map(Op::Fpr)
            .ok_or_else(|| format!("cannot use register {} on {}", name, target.name())),
        Node::SpecialRegister { name } => special_register(name, target),
        Node::Address { base, offset, .. } => {
            let base = match operand_to_op(base, ctx, flags, target)? {
                Op::Gpr(g) => g,
                other => {
                    return Err(format!("address base must be a GPR, got {:?}", other));
                }
            };
            Ok(Op::Mem(Mem {
                base: Some(base),
                index: None,
                disp: disp_of(offset, ctx)?,
            }))
        }
        Node::BaseIndex {
            base,
            index,
            scale,
            offset,
            ..
        } => {
            let base = match operand_to_op(base, ctx, flags, target)? {
                Op::Gpr(g) => g,
                other => {
                    return Err(format!("address base must be a GPR, got {:?}", other));
                }
            };
            let index = match operand_to_op(index, ctx, flags, target)? {
                Op::Gpr(g) => g,
                other => {
                    return Err(format!("address index must be a GPR, got {:?}", other));
                }
            };
            let scale = match scale.as_ref() {
                Node::Immediate { value, .. } => u8::try_from(*value)
                    .ok()
                    .filter(|s| matches!(s, 1 | 2 | 4 | 8))
                    .ok_or_else(|| format!("bad index scale {}", value))?,
                other => return Err(format!("bad index scale {}", other.dump())),
            };
            Ok(Op::Mem(Mem {
                base: Some(base),
                index: Some((index, scale)),
                disp: disp_of(offset, ctx)?,
            }))
        }
        Node::AbsoluteAddress { address, .. } => Ok(Op::Mem(Mem::absolute(disp_of(address, ctx)?))),
        Node::LabelReference { label, .. } => {
            let (global, _export, _aligned, is_extern, _align_to) = flags(label);
            ctx.mark_used(label, is_extern);
            let raw = label.strip_prefix('_').unwrap_or(label);
            if let Some(&reach) = ctx.declared_externs.get(label) {
                // Position-independent code reaches every extern through the
                // GOT, as onlineasm does with its PIC option.
                let reach = if ctx.setting("PIC") {
                    offlineasm_ir::Reach::Far
                } else {
                    reach
                };
                let id = ctx.intern_extern(ctx.global_symbol(raw));
                return Ok(Op::Extern(Extern { id, reach }));
            }
            let symbol = if global || is_extern {
                ctx.global_symbol(raw)
            } else {
                ctx.local_symbol(raw)
            };
            Ok(Op::Label(Lbl::Bound(ctx.intern_label(symbol))))
        }
        Node::LocalLabelReference { .. } => {
            let text = super::local_ref_name(node, ctx)?;
            Ok(Op::Label(Lbl::Bound(ctx.intern_label(text))))
        }
        Node::RustConst { ident, .. } => {
            Ok(Op::Sym(SymId(ctx.intern_sym(format!("{{{}}}", ident)))))
        }
        other => Err(format!("cannot lower operand {}", other.dump())),
    }
}

/// Returns the displacement for an address offset: a folded constant, or a
/// `{IDENT}` splice.
///
/// # Errors
///
/// Returns an error if `node` is not an immediate or a `RustConst`, or if an
/// immediate offset does not fit a 32-bit displacement.
pub fn disp_of(node: &Node, ctx: &mut LowerCtx) -> Result<offlineasm_ir::Disp, String> {
    match node {
        Node::Immediate { value, .. } => {
            let v = i64::try_from(*value).map_err(|_| format!("offset {} out of range", value))?;
            i32::try_from(v)
                .map(offlineasm_ir::Disp::Const)
                .map_err(|_| format!("offset {} does not fit a displacement", v))
        }
        Node::RustConst { ident, .. } => {
            let id = ctx.intern_sym(format!("{{{}}}", ident));
            Ok(offlineasm_ir::Disp::Sym(SymId(id)))
        }
        other => Err(format!("bad address offset {}", other.dump())),
    }
}

fn imm_of(node: &Node, value: i128) -> Result<i64, String> {
    i64::try_from(value)
        .or_else(|_| u64::try_from(value).map(|u| u as i64))
        .map_err(|_| {
            format!(
                "immediate {} at {} does not fit 64 bits",
                value,
                node.origin_string()
            )
        })
}

fn special_register(name: &str, target: TextTarget) -> Result<Op, String> {
    let base = name.strip_prefix('%').unwrap_or(name);
    let bad = || format!("bad special register {}", name);
    let _reserved = |base: &str| {
        format!(
            "{} is a reserved register on {} and cannot be named directly",
            base,
            target.name()
        )
    };
    match target {
        TextTarget::X86_64 => {
            if let Some(i) = indexed(base, "r").or_else(|| x86_abi_gpr(base)) {
                return (i < 16)
                    .then_some(Op::Gpr(offlineasm_ir::Gpr(i)))
                    .ok_or_else(bad);
            }
            if let Some(i) = indexed(base, "xmm") {
                return (i < 16)
                    .then_some(Op::Fpr(offlineasm_ir::Fpr(i)))
                    .ok_or_else(bad);
            }
            Err(bad())
        }
        TextTarget::Aarch64 => {
            if base == "sp" {
                return Ok(Op::Gpr(offlineasm_ir::Gpr(31)));
            }
            if base == "fp" {
                return Ok(Op::Gpr(offlineasm_ir::Gpr(29)));
            }
            if base == "lr" {
                return Ok(Op::Gpr(offlineasm_ir::Gpr(30)));
            }

            if let Some(i) = indexed(base, "x").or_else(|| indexed(base, "w")) {
                return (i < 31)
                    .then_some(Op::Gpr(offlineasm_ir::Gpr(i)))
                    .ok_or_else(bad);
            }
            if base == "xzr" || base == "wzr" {
                return Ok(Op::Gpr(offlineasm_ir::Gpr(63)));
            }

            for prefix in ["q", "d", "s", "v"] {
                if let Some(i) = indexed(base, prefix) {
                    return (i < 32)
                        .then_some(Op::Fpr(offlineasm_ir::Fpr(i)))
                        .ok_or_else(bad);
                }
            }
            Err(bad())
        }
        TextTarget::Riscv64 => {
            if let Some(i) = indexed(base, "x").or_else(|| riscv_abi_gpr(base)) {
                return (i < 32)
                    .then_some(Op::Gpr(offlineasm_ir::Gpr(i)))
                    .ok_or_else(bad);
            }

            if let Some(i) = indexed(base, "f").or_else(|| riscv_abi_fpr(base)) {
                return (i < 32)
                    .then_some(Op::Fpr(offlineasm_ir::Fpr(i)))
                    .ok_or_else(bad);
            }
            Err(bad())
        }
    }
}

fn x86_abi_gpr(name: &str) -> Option<u8> {
    Some(match name {
        "rax" | "eax" | "ax" | "al" | "ah" => 0,
        "rcx" | "ecx" | "cx" | "cl" | "ch" => 1,
        "rdx" | "edx" | "dx" | "dl" | "dh" => 2,
        "rbx" | "ebx" | "bx" | "bl" | "bh" => 3,
        "rsp" | "esp" | "spl" => 4,
        "rbp" | "ebp" | "bpl" => 5,
        "rsi" | "esi" | "sil" => 6,
        "rdi" | "edi" | "dil" => 7,
        "r8d" | "r8w" | "r8b" => 8,
        "r9d" | "r9w" | "r9b" => 9,
        "r10d" | "r10w" | "r10b" => 10,
        "r11d" | "r11w" | "r11b" => 11,
        "r12d" | "r12w" | "r12b" => 12,
        "r13d" | "r13w" | "r13b" => 13,
        "r14d" | "r14w" | "r14b" => 14,
        "r15d" | "r15w" | "r15b" => 15,
        _ => return None,
    })
}

fn riscv_abi_gpr(name: &str) -> Option<u8> {
    Some(match name {
        "zero" => 0,
        "ra" => 1,
        "sp" => 2,
        "gp" => 3,
        "tp" => 4,
        "t0" => 5,
        "t1" => 6,
        "t2" => 7,
        "s0" | "fp" => 8,
        "s1" => 9,
        "a0" => 10,
        "a1" => 11,
        "a2" => 12,
        "a3" => 13,
        "a4" => 14,
        "a5" => 15,
        "a6" => 16,
        "a7" => 17,
        "s2" => 18,
        "s3" => 19,
        "s4" => 20,
        "s5" => 21,
        "s6" => 22,
        "s7" => 23,
        "s8" => 24,
        "s9" => 25,
        "s10" => 26,
        "s11" => 27,
        "t3" => 28,
        "t4" => 29,
        "t5" => 30,
        "t6" => 31,
        _ => return None,
    })
}

fn riscv_abi_fpr(name: &str) -> Option<u8> {
    Some(match name {
        "ft0" => 0,
        "ft1" => 1,
        "ft2" => 2,
        "ft3" => 3,
        "ft4" => 4,
        "ft5" => 5,
        "ft6" => 6,
        "ft7" => 7,
        "fs0" => 8,
        "fs1" => 9,
        "fa0" => 10,
        "fa1" => 11,
        "fa2" => 12,
        "fa3" => 13,
        "fa4" => 14,
        "fa5" => 15,
        "fa6" => 16,
        "fa7" => 17,
        "fs2" => 18,
        "fs3" => 19,
        "fs4" => 20,
        "fs5" => 21,
        "fs6" => 22,
        "fs7" => 23,
        "fs8" => 24,
        "fs9" => 25,
        "fs10" => 26,
        "fs11" => 27,
        "ft8" => 28,
        "ft9" => 29,
        "ft10" => 30,
        "ft11" => 31,
        _ => return None,
    })
}

fn indexed(name: &str, prefix: &str) -> Option<u8> {
    let rest = name.strip_prefix(prefix)?;
    if rest.is_empty() {
        return None;
    }
    rest.parse().ok()
}
