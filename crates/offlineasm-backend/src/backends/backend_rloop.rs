//! Lowers offlineasm to Rust for the portable `rloop` interpreter.

use crate::ast::Node;
use crate::backends::{LabelFlags, LowerCtx};
use offlineasm_ir::regs::{self, VReg};
use std::collections::HashMap;

pub fn normalize_op(opcode: &str) -> &str {
    opcode
}

fn rust_ident(name: &str) -> String {
    let raw = name.strip_prefix('_').unwrap_or(name);
    raw.replace(|c: char| !(c.is_ascii_alphanumeric() || c == '_'), "_")
}

const RLOOP_GPRS: &[(VReg, &str)] = &[
    (regs::t0, "regs.t0"),
    (regs::t1, "regs.t1"),
    (regs::t2, "regs.t2"),
    (regs::t3, "regs.t3"),
    (regs::t4, "regs.pc"),
    (regs::t5, "regs.t5"),
    (regs::t6, "regs.t6"),
    (regs::t7, "regs.t7"),
    (regs::csr0, "regs.t9"),
    (regs::csr1, "regs.t8"),
    (regs::csr2, "regs.t10"),
    (regs::csr3, "regs.t11"),
    (regs::cfr, "regs.cfr"),
    (regs::lr, "regs.lr"),
    (regs::sp, "regs.sp"),
];

const RLOOP_FPRS: &[(VReg, &str)] = &[
    (regs::ft0, "regs.d0"),
    (regs::ft1, "regs.d1"),
    (regs::ft2, "regs.d2"),
    (regs::ft3, "regs.d3"),
    (regs::ft4, "regs.d4"),
    (regs::ft5, "regs.d5"),
];

fn reg_canon(name: &str) -> Result<&'static str, String> {
    let bad = || format!("Bad register {} for RLOOP", name);
    let id = regs::gpr_id(name).ok_or_else(bad)?;
    RLOOP_GPRS
        .iter()
        .find(|(r, _)| r.id() == id)
        .map(|&(_, field)| field)
        .ok_or_else(bad)
}

fn fpr_canon(name: &str) -> Result<&'static str, String> {
    let bad = || format!("Bad FP register {} for RLOOP", name);
    let id = regs::fpr_id(name).ok_or_else(bad)?;
    RLOOP_FPRS
        .iter()
        .find(|(r, _)| r.id() == id)
        .map(|&(_, field)| field)
        .ok_or_else(bad)
}

/// Returns the lvalue identifier for a register-like node, or `None` when
/// the node has no nameable location.
fn as_reg_ident(node: &Node) -> Option<Result<String, String>> {
    match node {
        Node::Register { name, .. } => Some(reg_canon(name).map(|s| s.to_string())),
        Node::FpRegister { name, .. } => Some(fpr_canon(name).map(|s| s.to_string())),
        Node::SpecialRegister { name } => Some(Err(format!(
            "rloop has no physical registers: {} cannot be used here",
            name
        ))),
        Node::Variable { name, .. } => Some(Ok(name.clone())),
        _ => None,
    }
}
/// Value types the generated interpreter code distinguishes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RTy {
    Intptr,
    Uintptr,
    Int32,
    Uint32,
    Int16,
    Uint16,
    Int64,
    Uint64,
    Int8,
    Uint8,
    VoidPtr,
    NativeFunc,
    Double,
    BitsAsDouble,
    BitsAsInt64,
    Opcode,
}
use RTy::*;

fn rust_prim(ty: RTy) -> &'static str {
    match ty {
        Intptr | Int64 | BitsAsInt64 => "i64",
        Uintptr | Uint64 => "u64",
        Int32 => "i32",
        Uint32 => "u32",
        Int16 => "i16",
        Uint16 => "u16",
        Int8 => "i8",
        Uint8 => "u8",
        VoidPtr | NativeFunc | Opcode => "u64",
        Double | BitsAsDouble => "f64",
    }
}

fn accessor_expr(reg: &str, ty: RTy) -> String {
    match ty {
        Intptr => format!("(({}) as i64)", reg),
        Uintptr => format!("(({}) as u64)", reg),
        Uint64 => reg.to_string(),
        Int64 | BitsAsInt64 => format!("(({}) as i64)", reg),
        Int32 => format!("(({}) as u32 as i32)", reg),
        Uint32 => format!("(({}) as u32)", reg),
        Int16 => format!("(({}) as u16 as i16)", reg),
        Uint16 => format!("(({}) as u16)", reg),
        Int8 => format!("(({}) as u8 as i8)", reg),
        Uint8 => format!("(({}) as u8)", reg),
        VoidPtr | NativeFunc | Opcode => reg.to_string(),
        Double | BitsAsDouble => format!("f64::from_bits({})", reg),
    }
}

fn store_expr(value_expr: &str, ty: RTy) -> String {
    match ty {
        Uint8 => format!("((({}) as u8) as u64)", value_expr),
        Int8 => format!("((({}) as i8) as i64 as u64)", value_expr),
        Uint16 => format!("((({}) as u16) as u64)", value_expr),
        Int16 => format!("((({}) as i16) as i64 as u64)", value_expr),
        Uint32 => format!("((({}) as u32) as u64)", value_expr),
        Int32 => format!("((({}) as i32) as i64 as u64)", value_expr),
        Uint64 | Uintptr => format!("(({}) as u64)", value_expr),
        Int64 | Intptr | BitsAsInt64 => format!("((({}) as i64) as u64)", value_expr),
        Double | BitsAsDouble => format!("(({}) as f64).to_bits()", value_expr),
        VoidPtr | NativeFunc | Opcode => format!("(({}) as u64)", value_expr),
    }
}

fn literal_cast(value: i128, ty: RTy) -> String {
    format!("(({}i64) as {})", value, rust_prim(ty))
}

fn pointer_expr(node: &Node) -> Result<String, String> {
    match node {
        Node::Address { base, offset, .. } => {
            let b = render_value(base, VoidPtr)?;
            let off = match offset.as_ref() {
                Node::Immediate { value, .. } => *value,
                other => {
                    return Err(format!(
                        "Address offset must be an immediate in rloop, got {}",
                        other.dump()
                    ))
                }
            };
            Ok(format!("(((({}) as i64) + ({})) as usize)", b, off))
        }
        Node::BaseIndex {
            base,
            index,
            offset,
            ..
        } => {
            let b = render_value(base, VoidPtr)?;
            let idx = render_value(index, Intptr)?;
            let shift = node.scale_shift()?;
            let off = match offset.as_ref() {
                Node::Immediate { value, .. } => *value,
                other => {
                    return Err(format!(
                        "BaseIndex offset must be an immediate in rloop, got {}",
                        other.dump()
                    ))
                }
            };
            Ok(format!(
                "(((({}) as i64) + (({}) << {}) + ({})) as usize)",
                b, idx, shift, off
            ))
        }
        other => Err(format!("not an address in rloop: {}", other.dump())),
    }
}

fn mem_read(node: &Node, ty: RTy) -> Result<String, String> {
    let ptr = pointer_expr(node)?;
    Ok(format!(
        "unsafe {{ *(({}) as *const {}) }}",
        ptr,
        rust_prim(ty)
    ))
}

/// Renders `node` as a Rust expression of type `ty`.
///
/// The expression splices into the generated `rloop` interpreter body.
///
/// # Errors
///
/// Returns an error if `node` is not an operand form the RLoop backend can
/// render (an unresolved offset, a label the interpreter cannot address).
pub fn render_value(node: &Node, ty: RTy) -> Result<String, String> {
    match node {
        Node::Immediate { value, .. } => Ok(literal_cast(*value, ty)),
        Node::RustConst { expr, .. } => Ok(format!(
            "(({}) as {})",
            quote::quote!(#expr),
            rust_prim(ty)
        )),
        Node::Register { name, .. } => Ok(accessor_expr(reg_canon(name)?, ty)),
        Node::FpRegister { name, .. } => Ok(accessor_expr(fpr_canon(name)?, ty)),
        Node::SpecialRegister { name } => Err(format!(
            "rloop has no physical registers: {} cannot be used here",
            name
        )),
        Node::Variable { name, .. } => Ok(accessor_expr(name, ty)),
        Node::VecRegister { name, .. } => {
            Err(format!("vector registers are not supported by rloop: {}", name))
        }
        Node::Address { .. } | Node::BaseIndex { .. } => mem_read(node, ty),
        Node::AbsoluteAddress { .. } => {
            Err("rloop: absolute-address operands have no value to interpret".to_string())
        }
        Node::LabelReference { .. } | Node::LocalLabelReference { .. } => {
            Err("label references cannot be used as general rloop value operands (only as branch/jmp/lea targets)".to_string())
        }
        other => Err(format!("cannot render {} as an rloop value operand", other.dump())),
    }
}

fn emit_store(
    dst: &Node,
    value_expr: String,
    ty: RTy,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if let Some(ident) = as_reg_ident(dst) {
        emit(format!("{} = {};", ident?, store_expr(&value_expr, ty)));
        return Ok(());
    }
    match dst {
        Node::Address { .. } | Node::BaseIndex { .. } => {
            let ptr = pointer_expr(dst)?;
            let t = rust_prim(ty);
            emit(format!(
                "unsafe {{ *(({}) as *mut {}) = ({}) as {}; }}",
                ptr, t, value_expr, t
            ));
            Ok(())
        }
        other => Err(format!("cannot store to {} in rloop", other.dump())),
    }
}

fn emit_store_bool(
    dst: &Node,
    cond_expr: String,
    ty: RTy,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if let Some(ident) = as_reg_ident(dst) {
        emit(format!(
            "{} = if {} {{ 1u64 }} else {{ 0u64 }};",
            ident?, cond_expr
        ));
        return Ok(());
    }
    emit_store(
        dst,
        format!("(if {} {{ 1 }} else {{ 0 }})", cond_expr),
        ty,
        emit,
    )
}

fn branch_target(node: &Node, local_strings: &HashMap<String, String>) -> Result<String, String> {
    match node {
        Node::LabelReference { label, offset, .. } => {
            if *offset != 0 {
                return Err(format!(
                    "label reference with nonzero offset cannot be a branch target: {}",
                    label
                ));
            }
            Ok(format!("Opcode::{}", rust_ident(label)))
        }
        Node::LocalLabelReference { label, .. } => {
            let interned = local_strings
                .get(label)
                .cloned()
                .unwrap_or_else(|| label.clone());
            Ok(format!("Opcode::{}", rust_ident(&interned)))
        }
        other => Err(format!(
            "expected a label reference as an rloop branch target, got {}",
            other.dump()
        )),
    }
}

fn raw_label_ident(node: &Node) -> Result<String, String> {
    match node {
        Node::LabelReference {
            label, offset: 0, ..
        } => Ok(rust_ident(label)),
        other => Err(format!(
            "expected a plain label reference, got {}",
            other.dump()
        )),
    }
}

fn canon_dump(node: &Node) -> Result<String, String> {
    as_reg_ident(node)
        .unwrap_or_else(|| Err(format!("expected a register operand, got {}", node.dump())))
}

fn opcode_to_u64(variant: &str) -> String {
    format!("(Opcode::{} as u64)", variant)
}

fn u64_to_opcode(expr: &str) -> String {
    format!("Opcode::from_u64({})", expr)
}

fn threaded_return(target: &str) -> String {
    format!("return ({}, regs);", target)
}

fn emit_synced_call(emit: &mut dyn FnMut(String), stmt: String) {
    emit("m.regs = regs;".to_string());
    emit(stmt);
    emit("regs = m.regs;".to_string());
}

fn wrapping_binop(a: &str, op: &str, b: &str, ty: RTy) -> String {
    if matches!(ty, Double | BitsAsDouble) {
        return format!("({} {} {})", a, op, b);
    }
    match op {
        "+" => format!("({}).wrapping_add({})", a, b),
        "-" => format!("({}).wrapping_sub({})", a, b),
        "*" => format!("({}).wrapping_mul({})", a, b),
        _ => format!("({} {} {})", a, op, b),
    }
}

fn emit_operation(
    operands: &[Node],
    ty: RTy,
    op: &str,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    let (op1, op2, dst) = match operands.len() {
        3 => (&operands[0], &operands[1], &operands[2]),
        2 => (&operands[1], &operands[0], &operands[1]),
        n => return Err(format!("expected 2 or 3 operands, got {}", n)),
    };
    let a = render_value(op1, ty)?;
    let b = render_value(op2, ty)?;
    let expr = wrapping_binop(&a, op, &b, ty);
    emit_store(dst, expr, ty, emit)
}

fn emit_unary_operation(
    operands: &[Node],
    ty: RTy,
    op: &str,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() != 1 {
        return Err(format!("expected 1 operand, got {}", operands.len()));
    }
    let v = render_value(&operands[0], ty)?;
    let expr = match op {
        "-" if matches!(ty, Double | BitsAsDouble) => format!("(-({}))", v),
        "-" => format!("({}).wrapping_neg()", v),
        "~" => format!("(!({}))", v),
        _ => return Err(format!("unknown unary operator {}", op)),
    };
    emit_store(&operands[0], expr, ty, emit)
}

fn emit_shift_operation(
    operands: &[Node],
    ty: RTy,
    op: &str,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() != 2 && operands.len() != 3 {
        return Err(format!("expected 2 or 3 operands, got {}", operands.len()));
    }
    let dst = if operands.len() == 3 {
        &operands[2]
    } else {
        &operands[1]
    };
    let value = render_value(&operands[1], ty)?;
    let amount = render_value(&operands[0], Intptr)?;
    let mask = match ty {
        Int32 | Uint32 => 0x1f,
        _ => 0x3f,
    };
    let masked = format!("(({}) & {})", amount, mask);
    let shifted = if op == "<<" {
        format!("(({}) << ({}))", value, masked)
    } else {
        format!("(({}) >> ({}))", value, masked)
    };
    emit_store(dst, shifted, ty, emit)
}

fn emit_compare_and_branch(
    operands: &[Node],
    ty: RTy,
    cmp: &str,
    local_strings: &HashMap<String, String>,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() != 3 {
        return Err(format!("expected 3 operands, got {}", operands.len()));
    }
    let a = render_value(&operands[0], ty)?;
    let b = render_value(&operands[1], ty)?;
    let target = branch_target(&operands[2], local_strings)?;
    emit(format!(
        "if {} {} {} {{ {} }}",
        a,
        cmp,
        b,
        threaded_return(&target)
    ));
    Ok(())
}

fn emit_compare_double_nan_branch(
    operands: &[Node],
    cmp: &str,
    local_strings: &HashMap<String, String>,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() != 3 {
        return Err(format!("expected 3 operands, got {}", operands.len()));
    }
    let a = render_value(&operands[0], Double)?;
    let b = render_value(&operands[1], Double)?;
    let target = branch_target(&operands[2], local_strings)?;
    emit(format!(
        "if ({}).is_nan() || ({}).is_nan() || ({} {} {}) {{ {} }}",
        a,
        b,
        a,
        cmp,
        b,
        threaded_return(&target)
    ));
    Ok(())
}

fn emit_compare_and_set(
    operands: &[Node],
    ty: RTy,
    cmp: &str,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() != 3 {
        return Err(format!("expected 3 operands, got {}", operands.len()));
    }
    let a = render_value(&operands[0], ty)?;
    let b = render_value(&operands[1], ty)?;
    let cond = format!("({} {} {})", a, cmp, b);
    emit_store_bool(&operands[2], cond, ty, emit)
}

fn condition_expr(operands: &[Node], ty: RTy, tail: &str) -> Result<String, String> {
    let op1 = render_value(&operands[0], ty)?;
    match operands.len() {
        2 => Ok(format!("({} {})", op1, tail)),
        3 => {
            let mask = render_value(&operands[1], ty)?;
            Ok(format!("(({} & {}) {})", op1, mask, tail))
        }
        n => Err(format!("expected 2 or 3 operands, got {}", n)),
    }
}

fn emit_test_and_branch_if(
    operands: &[Node],
    ty: RTy,
    tail: &str,
    local_strings: &HashMap<String, String>,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() < 2 {
        return Err(format!(
            "expected at least 2 operands, got {}",
            operands.len()
        ));
    }
    let target = branch_target(&operands[operands.len() - 1], local_strings)?;

    let cond = condition_expr(operands, ty, tail)?;
    emit(format!("if {} {{ {} }}", cond, threaded_return(&target)));
    Ok(())
}

fn emit_test_set(
    operands: &[Node],
    ty: RTy,
    tail: &str,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() < 2 {
        return Err(format!(
            "expected at least 2 operands, got {}",
            operands.len()
        ));
    }
    let dst_idx = operands.len() - 1;

    let cond = condition_expr(operands, ty, tail)?;
    emit_store_bool(&operands[dst_idx], cond, ty, emit)
}

fn emit_op_and_branch(
    operands: &[Node],
    op: &str,
    ty: RTy,
    tail: &str,
    local_strings: &HashMap<String, String>,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() != 3 {
        return Err(format!("expected 3 operands, got {}", operands.len()));
    }
    let a = render_value(&operands[1], ty)?;
    let b = render_value(&operands[0], ty)?;
    let temp = wrapping_binop(&a, op, &b, ty);
    let target = branch_target(&operands[2], local_strings)?;
    let prim = rust_prim(ty);
    emit("{".to_string());
    emit(format!("let __t: {} = {};", prim, temp));
    emit_store(&operands[1], "__t".to_string(), ty, emit)?;
    emit(format!(
        "if __t {} {{ {} }}",
        tail,
        threaded_return(&target)
    ));
    emit("}".to_string());
    Ok(())
}

fn emit_op_and_branch_if_overflow(
    operands: &[Node],
    op: &str,
    local_strings: &HashMap<String, String>,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() != 3 {
        return Err(format!("expected 3 operands, got {}", operands.len()));
    }
    let a = render_value(&operands[1], Int32)?;
    let b = render_value(&operands[0], Int32)?;
    let method = match op {
        "+" => "overflowing_add",
        "-" => "overflowing_sub",
        "*" => "overflowing_mul",
        _ => return Err(format!("unimplemented overflow operator {}", op)),
    };
    let target = branch_target(&operands[2], local_strings)?;
    emit("{".to_string());
    emit(format!(
        "let (__v, __of): (i32, bool) = ({}).{}({});",
        a, method, b
    ));
    emit_store(&operands[1], "__v".to_string(), Int32, emit)?;
    emit(format!("if __of {{ {} }}", threaded_return(&target)));
    emit("}".to_string());
    Ok(())
}

fn emit_call_slow_path(
    operands: &[Node],
    void_result: bool,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.is_empty() {
        return Err("rloopCallSlowPath* needs a target operand".to_string());
    }
    let target = raw_label_ident(&operands[0])?;
    let args: Vec<String> = operands[1..]
        .iter()
        .map(canon_dump)
        .collect::<Result<Vec<_>, _>>()?;
    emit("{".to_string());
    emit_synced_call(emit, "self.stack_set_sp(&mut *m);".to_string());
    if void_result {
        emit(format!("{}({});", target, args.join(", ")));
    } else {
        emit(format!("let __result = {}({});", target, args.join(", ")));
        emit_synced_call(
            emit,
            "let (__t0, __t1) = self.native_result(&mut *m, __result);".to_string(),
        );
        emit("regs.t0 = __t0;".to_string());
        emit("regs.t1 = __t1;".to_string());
    }
    emit("}".to_string());
    Ok(())
}

fn emit_lea(source: &Node, dest: &Node, emit: &mut dyn FnMut(String)) -> Result<(), String> {
    match source {
        Node::Address { base, offset, .. } => {
            let off = match offset.as_ref() {
                Node::Immediate { value, .. } => *value,
                other => {
                    return Err(format!(
                        "lea offset must be an immediate, got {}",
                        other.dump()
                    ))
                }
            };
            let b = render_value(base, VoidPtr)?;
            let expr = format!("(((({}) as i64) + ({})) as u64)", b, off);
            emit_store(dest, expr, Uintptr, emit)
        }
        Node::BaseIndex {
            base,
            index,
            offset,
            ..
        } => {
            if !matches!(offset.as_ref(), Node::Immediate { value: 0, .. }) {
                return Err(format!(
                    "malformed BaseIndex for lea, offset should be zero at {}",
                    source.origin_string()
                ));
            }
            let shift = source.scale_shift()?;
            let b = render_value(base, VoidPtr)?;
            let idx = render_value(index, Intptr)?;
            let expr = format!("(((({}) as i64) + (({}) << {})) as u64)", b, idx, shift);
            emit_store(dest, expr, Uintptr, emit)
        }
        Node::LabelReference { label, offset, .. } => {
            let fname = rust_ident(label);
            emit_store(dest, opcode_to_u64(&fname), Uintptr, emit)?;
            if *offset != 0 {
                match as_reg_ident(dest) {
                    Some(ident) => {
                        let ident = ident?;
                        emit(format!(
                            "{} = ((({} as i64) + ({})) as u64);",
                            ident, ident, offset
                        ));
                        Ok(())
                    }
                    None => {
                        Err("lea destination with a label + offset must be a register".to_string())
                    }
                }
            } else {
                Ok(())
            }
        }
        other => Err(format!(
            "cannot take the address of {} in rloop",
            other.dump()
        )),
    }
}

const ARITH_OP: &[(&str, RTy, &str)] = &[
    ("addi", Int32, "+"),
    ("addq", Int64, "+"),
    ("addp", Intptr, "+"),
    ("andi", Int32, "&"),
    ("andq", Int64, "&"),
    ("andp", Intptr, "&"),
    ("ori", Int32, "|"),
    ("orq", Int64, "|"),
    ("orp", Intptr, "|"),
    ("orh", Int16, "|"),
    ("xori", Int32, "^"),
    ("xorq", Int64, "^"),
    ("xorp", Intptr, "^"),
    ("muli", Int32, "*"),
    ("mulq", Int64, "*"),
    ("mulp", Intptr, "*"),
    ("subi", Int32, "-"),
    ("subq", Int64, "-"),
    ("subp", Intptr, "-"),
    ("addd", Double, "+"),
    ("divd", Double, "/"),
    ("subd", Double, "-"),
    ("muld", Double, "*"),
];

const UNARY_OP: &[(&str, RTy, &str)] = &[
    ("negi", Int32, "-"),
    ("negq", Int64, "-"),
    ("negp", Intptr, "-"),
    ("noti", Int32, "~"),
];

const SHIFT_OP: &[(&str, RTy, &str)] = &[
    ("lshifti", Int32, "<<"),
    ("lshiftq", Int64, "<<"),
    ("lshiftp", Intptr, "<<"),
    ("rshifti", Int32, ">>"),
    ("rshiftq", Int64, ">>"),
    ("rshiftp", Intptr, ">>"),
    ("urshifti", Uint32, ">>"),
    ("urshiftq", Uint64, ">>"),
    ("urshiftp", Uintptr, ">>"),
];

const CMP_BRANCH: &[(&str, RTy, &str)] = &[
    ("bbeq", Int8, "=="),
    ("bieq", Int32, "=="),
    ("bqeq", Int64, "=="),
    ("bpeq", Intptr, "=="),
    ("bbneq", Int8, "!="),
    ("bineq", Int32, "!="),
    ("bqneq", Int64, "!="),
    ("bpneq", Intptr, "!="),
    ("bba", Uint8, ">"),
    ("bia", Uint32, ">"),
    ("bqa", Uint64, ">"),
    ("bpa", Uintptr, ">"),
    ("bbaeq", Uint8, ">="),
    ("biaeq", Uint32, ">="),
    ("bqaeq", Uint64, ">="),
    ("bpaeq", Uintptr, ">="),
    ("bbb", Uint8, "<"),
    ("bib", Uint32, "<"),
    ("bqb", Uint64, "<"),
    ("bpb", Uintptr, "<"),
    ("bbbeq", Uint8, "<="),
    ("bibeq", Uint32, "<="),
    ("bqbeq", Uint64, "<="),
    ("bpbeq", Uintptr, "<="),
    ("bbgt", Int8, ">"),
    ("bigt", Int32, ">"),
    ("bqgt", Int64, ">"),
    ("bpgt", Intptr, ">"),
    ("bbgteq", Int8, ">="),
    ("bigteq", Int32, ">="),
    ("bqgteq", Int64, ">="),
    ("bpgteq", Intptr, ">="),
    ("bblt", Int8, "<"),
    ("bilt", Int32, "<"),
    ("bqlt", Int64, "<"),
    ("bplt", Intptr, "<"),
    ("bblteq", Int8, "<="),
    ("bilteq", Int32, "<="),
    ("bqlteq", Int64, "<="),
    ("bplteq", Intptr, "<="),
];

const DBL_BRANCH: &[(&str, &str)] = &[
    ("bdeq", "=="),
    ("bdneq", "!="),
    ("bdgt", ">"),
    ("bdgteq", ">="),
    ("bdlt", "<"),
    ("bdlteq", "<="),
];

const DBL_NAN_BRANCH: &[(&str, &str)] = &[
    ("bdequn", "=="),
    ("bdnequn", "!="),
    ("bdgtun", ">"),
    ("bdgtequn", ">="),
    ("bdltun", "<"),
    ("bdltequn", "<="),
];

const TEST_BRANCH: &[(&str, RTy, &str)] = &[
    ("btbz", Int8, "== 0"),
    ("btiz", Int32, "== 0"),
    ("btqz", Int64, "== 0"),
    ("btpz", Intptr, "== 0"),
    ("btbnz", Int8, "!= 0"),
    ("btinz", Int32, "!= 0"),
    ("btqnz", Int64, "!= 0"),
    ("btpnz", Intptr, "!= 0"),
    ("btbs", Int8, "< 0"),
    ("btis", Int32, "< 0"),
    ("btqs", Int64, "< 0"),
    ("btps", Intptr, "< 0"),
];

const CMP_SET: &[(&str, RTy, &str)] = &[
    ("cbeq", Uint8, "=="),
    ("cieq", Uint32, "=="),
    ("cqeq", Uint64, "=="),
    ("cpeq", Uintptr, "=="),
    ("cbneq", Uint8, "!="),
    ("cineq", Uint32, "!="),
    ("cqneq", Uint64, "!="),
    ("cpneq", Uintptr, "!="),
    ("cba", Uint8, ">"),
    ("cia", Uint32, ">"),
    ("cqa", Uint64, ">"),
    ("cpa", Uintptr, ">"),
    ("cbaeq", Uint8, ">="),
    ("ciaeq", Uint32, ">="),
    ("cqaeq", Uint64, ">="),
    ("cpaeq", Uintptr, ">="),
    ("cbb", Uint8, "<"),
    ("cib", Uint32, "<"),
    ("cqb", Uint64, "<"),
    ("cpb", Uintptr, "<"),
    ("cbbeq", Uint8, "<="),
    ("cibeq", Uint32, "<="),
    ("cqbeq", Uint64, "<="),
    ("cpbeq", Uintptr, "<="),
    ("cbgt", Int8, ">"),
    ("cigt", Int32, ">"),
    ("cqgt", Int64, ">"),
    ("cpgt", Intptr, ">"),
    ("cdgt", Double, ">"),
    ("cbgteq", Int8, ">="),
    ("cigteq", Int32, ">="),
    ("cqgteq", Int64, ">="),
    ("cpgteq", Intptr, ">="),
    ("cdgteq", Double, ">="),
    ("cblt", Int8, "<"),
    ("cilt", Int32, "<"),
    ("cqlt", Int64, "<"),
    ("cplt", Intptr, "<"),
    ("cdlt", Double, "<"),
    ("cblteq", Int8, "<="),
    ("cilteq", Int32, "<="),
    ("cqlteq", Int64, "<="),
    ("cplteq", Intptr, "<="),
    ("cdlteq", Double, "<="),
];

const TEST_SET: &[(&str, RTy, &str)] = &[
    ("tbs", Int8, "< 0"),
    ("tis", Int32, "< 0"),
    ("tqs", Int64, "< 0"),
    ("tps", Intptr, "< 0"),
    ("tbz", Int8, "== 0"),
    ("tiz", Int32, "== 0"),
    ("tqz", Int64, "== 0"),
    ("tpz", Intptr, "== 0"),
    ("tbnz", Int8, "!= 0"),
    ("tinz", Int32, "!= 0"),
    ("tqnz", Int64, "!= 0"),
    ("tpnz", Intptr, "!= 0"),
];

const OP_BRANCH: &[(&str, &str, RTy, &str)] = &[
    ("baddis", "+", Int32, "< 0"),
    ("baddiz", "+", Int32, "== 0"),
    ("baddinz", "+", Int32, "!= 0"),
    ("baddqs", "+", Int64, "< 0"),
    ("baddqz", "+", Int64, "== 0"),
    ("baddqnz", "+", Int64, "!= 0"),
    ("baddps", "+", Intptr, "< 0"),
    ("baddpz", "+", Intptr, "== 0"),
    ("baddpnz", "+", Intptr, "!= 0"),
    ("bsubqs", "-", Int64, "< 0"),
    ("borqs", "|", Int64, "< 0"),
    ("bsubqz", "-", Int64, "== 0"),
    ("borqz", "|", Int64, "== 0"),
    ("bsubqnz", "-", Int64, "!= 0"),
    ("borqnz", "|", Int64, "!= 0"),
    ("bsubps", "-", Intptr, "< 0"),
    ("borps", "|", Intptr, "< 0"),
    ("bsubpz", "-", Intptr, "== 0"),
    ("borpz", "|", Intptr, "== 0"),
    ("bsubpnz", "-", Intptr, "!= 0"),
    ("borpnz", "|", Intptr, "!= 0"),
    ("bsubis", "-", Int32, "< 0"),
    ("bsubiz", "-", Int32, "== 0"),
    ("bsubinz", "-", Int32, "!= 0"),
    ("borris", "|", Int32, "< 0"),
    ("borriz", "|", Int32, "== 0"),
    ("borrinz", "|", Int32, "!= 0"),
];

const OVERFLOW_BRANCH: &[(&str, &str)] = &[("baddio", "+"), ("bsubio", "-"), ("bmulio", "*")];

fn to_dest_last(op: &str, operands: &[Node]) -> Option<Vec<Node>> {
    let lookup =
        |table: &'_ [(&'static str, RTy, &'static str)]| table.iter().any(|(o, _, _)| *o == op);

    if lookup(ARITH_OP) {
        return match operands {
            [dst, rhs] => Some(vec![rhs.clone(), dst.clone()]),
            [dst, lhs, rhs] => Some(vec![lhs.clone(), rhs.clone(), dst.clone()]),
            _ => None,
        };
    }

    if lookup(SHIFT_OP) {
        return match operands {
            [dst, cnt] => Some(vec![cnt.clone(), dst.clone()]),
            [dst, cnt, value] => Some(vec![cnt.clone(), value.clone(), dst.clone()]),
            _ => None,
        };
    }

    if lookup(CMP_SET) {
        return match operands {
            [dst, lhs, rhs] => Some(vec![lhs.clone(), rhs.clone(), dst.clone()]),
            _ => None,
        };
    }

    if lookup(TEST_SET) {
        return match operands {
            [dst, value] => Some(vec![value.clone(), dst.clone()]),
            [dst, value, mask] => Some(vec![value.clone(), mask.clone(), dst.clone()]),
            _ => None,
        };
    }

    let is_op_branch = OP_BRANCH.iter().any(|(o, _, _, _)| *o == op)
        || OVERFLOW_BRANCH.iter().any(|(o, _)| *o == op);
    if is_op_branch {
        return match operands {
            [dst, rhs, lbl] => Some(vec![rhs.clone(), dst.clone(), lbl.clone()]),
            [dst, lhs, rhs, lbl] => Some(vec![lhs.clone(), rhs.clone(), dst.clone(), lbl.clone()]),
            _ => None,
        };
    }

    let two_op = matches!(
        op,
        "move"
            | "sxi2q"
            | "zxi2q"
            | "sxb2i"
            | "sxh2i"
            | "sxb2q"
            | "sxb2p"
            | "sxh2q"
            | "zxb2i"
            | "zxh2i"
            | "zxb2q"
            | "zxh2q"
            | "loadi"
            | "loadis"
            | "loadq"
            | "loadp"
            | "loadb"
            | "loadbsi"
            | "loadbsq"
            | "loadh"
            | "loadhsi"
            | "loadhsq"
            | "loadd"
            | "storei"
            | "storeq"
            | "storep"
            | "storeb"
            | "storeh"
            | "stored"
            | "transferi"
            | "transferq"
            | "transferp"
            | "ci2ds"
            | "td2i"
            | "fq2d"
            | "fd2q"
            | "leai"
            | "leap"
    );
    if two_op && operands.len() == 2 {
        return Some(vec![operands[1].clone(), operands[0].clone()]);
    }

    if matches!(op, "cmov" | "cmovz" | "movz" | "movn") && operands.len() == 3 {
        return Some(vec![
            operands[2].clone(),
            operands[1].clone(),
            operands[0].clone(),
        ]);
    }

    if matches!(op, "bcd2i" | "btd2i") && operands.len() == 3 {
        return Some(vec![
            operands[1].clone(),
            operands[0].clone(),
            operands[2].clone(),
        ]);
    }
    None
}

fn is_block_terminal(op: &str) -> bool {
    matches!(
        op,
        "ret" | "jmp" | "rloopCrash" | "break" | "call" | "rloopCallNativeFunction"
    )
}

fn emit_call_js_function(
    operands: &[Node],
    cont_name: &str,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() != 1 {
        return Err(format!(
            "rloopCallNativeFunction expects 1 operand, got {}",
            operands.len()
        ));
    }
    let target = render_value(&operands[0], Opcode)?;
    emit(format!("regs.lr = {};", opcode_to_u64(cont_name)));
    emit(threaded_return(&u64_to_opcode(&target)));
    Ok(())
}

/// Lowers `call target` with `cont_name` as the return point.
///
/// A label target is an interpreted call: `lr` gets the continuation and
/// control moves to the label, and the callee's `ret` comes back. A
/// register or memory target is checked at run time. An `Opcode` number
/// (what `leap` of a label yields) is an interpreted call as well; anything
/// else is a native function address, called through the host's
/// `call_native` thunk with `t0`/`t1` as arguments and its result split into
/// `t0`/`t1` by `native_result`.
fn emit_call(
    operands: &[Node],
    cont_name: &str,
    local_strings: &HashMap<String, String>,
    emit: &mut dyn FnMut(String),
) -> Result<(), String> {
    if operands.len() != 1 {
        return Err(format!("call expects 1 operand, got {}", operands.len()));
    }
    let cont = opcode_to_u64(cont_name);
    match &operands[0] {
        Node::LabelReference { .. } | Node::LocalLabelReference { .. } => {
            let target = branch_target(&operands[0], local_strings)?;
            emit(format!("regs.lr = {};", cont));
            emit(threaded_return(&target));
        }
        other => {
            let target = render_value(other, Uintptr)?;
            emit(format!("let __target: u64 = {};", target));
            emit(format!("match {} {{", u64_to_opcode("__target")));
            emit("Opcode::Done => {".to_string());
            emit_synced_call(emit, "self.stack_set_sp(&mut *m);".to_string());
            emit("let (__a0, __a1): (u64, u64) = (regs.t0, regs.t1);".to_string());
            emit_synced_call(
                emit,
                "let __r: u64 = unsafe { self.call_native(&mut *m, __target, __a0, __a1) };"
                    .to_string(),
            );
            emit_synced_call(
                emit,
                "let (__t0, __t1) = self.native_result(&mut *m, __r);".to_string(),
            );
            emit("regs.t0 = __t0;".to_string());
            emit("regs.t1 = __t1;".to_string());
            emit(threaded_return(&format!("Opcode::{}", cont_name)));
            emit("}".to_string());
            emit("__callee => {".to_string());
            emit(format!("regs.lr = {};", cont));
            emit(threaded_return("__callee"));
            emit("}".to_string());
            emit("}".to_string());
        }
    }
    Ok(())
}

struct Segment {
    name: String,
    doc: String,
    body: Vec<Node>,
}

impl Segment {
    fn mnemonics(&self) -> Vec<&str> {
        let mut names: Vec<&str> = Vec::new();
        for node in &self.body {
            if let Node::Instruction { opcode, .. } = node {
                let name = opcode.as_str();
                if !names.contains(&name) {
                    names.push(name);
                }
            }
        }
        names
    }

    fn doc_tail(&self) -> Vec<String> {
        let names = self.mnemonics();
        if names.is_empty() {
            return Vec::new();
        }
        let list = names
            .iter()
            .map(|name| format!("`{}`", name))
            .collect::<Vec<String>>()
            .join(", ");
        vec![
            String::new(),
            format!("Emitted mnemonics: {}.", list),
            "Per-mnemonic syntax and semantics: see the instruction reference in the `offlineasm` crate's `reference` module.".to_string(),
        ]
    }
}

pub fn lower_sequence(
    list: &[Node],
    ctx: &mut LowerCtx,
    label_flags: LabelFlags<'_>,
) -> Result<(), String> {
    let mut segments: Vec<Segment> = Vec::new();
    let mut cur_body: Vec<Node> = Vec::new();
    let mut cur_name = "__rloop_init".to_string();
    let mut cur_doc = "Init segment: label-less prologue statements.".to_string();
    let mut uid = 0usize;

    for node in list {
        match node {
            Node::Label { name, .. } => {
                segments.push(Segment {
                    name: cur_name.clone(),
                    doc: cur_doc.clone(),
                    body: std::mem::take(&mut cur_body),
                });
                let (_global, export, _aligned, _extern, _align_to) = label_flags(name);
                cur_name = rust_ident(name);
                cur_doc = format!(
                    "Global label `{}`{}.",
                    name,
                    if export { " (exported)" } else { "" }
                );
            }
            Node::LocalLabel { name, origin } => {
                segments.push(Segment {
                    name: cur_name.clone(),
                    doc: cur_doc.clone(),
                    body: std::mem::take(&mut cur_body),
                });
                let interned = ctx
                    .local_strings
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| LowerCtx::local_label_string(name, origin));
                cur_name = rust_ident(&interned);
                cur_doc = format!("Local label `{}`.", name);
            }
            Node::Skip { .. } => {}
            Node::Instruction { opcode, .. } => {
                cur_body.push(node.clone());
                if matches!(normalize_op(opcode), "rloopCallNativeFunction" | "call") {
                    segments.push(Segment {
                        name: cur_name.clone(),
                        doc: cur_doc.clone(),
                        body: std::mem::take(&mut cur_body),
                    });
                    uid += 1;
                    cur_name = format!("rloop_resume_after_call_{}", uid);
                    cur_doc = format!("Continuation after host call #{}.", uid);
                }
            }
            other => {
                return Err(format!(
                    "Unexpected {} at {} (validate first)",
                    other.dump(),
                    other.origin_string()
                ))
            }
        }
    }
    segments.push(Segment {
        name: cur_name,
        doc: cur_doc,
        body: cur_body,
    });

    let start = if segments[0].name == "__rloop_init" && segments[0].body.is_empty() {
        1
    } else {
        0
    };
    if start >= segments.len() {
        return Err("rloop: program has no code".to_string());
    }

    emit_opcode_enum(ctx, &segments[start..]);
    emit_trait_header(ctx, &segments[start..]);
    emit_run_method(ctx, &segments[start..]);

    for i in start..segments.len() {
        let next_name = segments.get(i + 1).map(|s| s.name.clone());
        let seg = &segments[i];
        ctx.emitter.put_rust(&format!("    /// {}", seg.doc));
        for line in seg.doc_tail() {
            if line.is_empty() {
                ctx.emitter.put_rust("    ///");
            } else {
                ctx.emitter.put_rust(&format!("    /// {}", line));
            }
        }
        ctx.emitter.put_rust("    #[allow(non_snake_case)]");
        ctx.emitter.put_rust(&format!(
            "    extern \"rust-preserve-none\" fn {}(&mut self, m: &mut Machine, mut regs: Registers) -> (Opcode, Registers) {{",
            seg.name
        ));

        let mut terminal = false;
        for instr in &seg.body {
            match instr {
                Node::Instruction {
                    opcode, operands, ..
                } => {
                    let normalized = normalize_op(opcode);
                    if matches!(normalized, "rloopCallNativeFunction" | "call") {
                        let cont = next_name
                            .clone()
                            .ok_or_else(|| format!("{normalized} with no continuation segment"))?;
                        let mut lines: Vec<String> = Vec::new();
                        if normalized == "call" {
                            emit_call(operands, &cont, &ctx.local_strings, &mut |s| lines.push(s))?;
                        } else {
                            emit_call_js_function(operands, &cont, &mut |s| lines.push(s))?;
                        }
                        for l in lines {
                            ctx.emitter.put_rust(&format!("            {}", l));
                        }
                    } else {
                        lower_instruction(instr, ctx, label_flags)?;
                    }
                    terminal = is_block_terminal(normalized);
                }
                other => return Err(format!("unexpected {} in rloop segment body", other.dump())),
            }
        }
        if !terminal {
            match &next_name {
                Some(n) => ctx
                    .emitter
                    .put_rust(&format!("            return (Opcode::{}, regs);", n)),
                None => ctx
                    .emitter
                    .put_rust("            return (Opcode::Done, regs);"),
            }
        }
        ctx.emitter.put_rust("    }");
    }

    ctx.emitter.put_rust("}");
    Ok(())
}

fn emit_opcode_enum(ctx: &mut LowerCtx, segments: &[Segment]) {
    ctx.emitter
        .put_rust("/// Every label the generated program can dispatch to.");
    ctx.emitter.put_rust("///");
    ctx.emitter
        .put_rust("/// `Done` is the value a label reference never has: it is what `ret`");
    ctx.emitter
        .put_rust("/// dispatches to when `lr` is unset, i.e. \"return to the caller\".");
    ctx.emitter
        .put_rust("#[derive(Clone, Copy, Debug, PartialEq, Eq)]");
    ctx.emitter.put_rust("#[allow(non_camel_case_types)]");
    ctx.emitter.put_rust("pub enum Opcode {");
    ctx.emitter.put_rust("    Done = 0,");
    for (index, seg) in segments.iter().enumerate() {
        ctx.emitter.put_rust(&format!("    /// {}", seg.doc));
        for line in seg.doc_tail() {
            if line.is_empty() {
                ctx.emitter.put_rust("    ///");
            } else {
                ctx.emitter.put_rust(&format!("    /// {}", line));
            }
        }
        ctx.emitter
            .put_rust(&format!("    {} = {},", seg.name, index + 1));
    }
    ctx.emitter.put_rust("}");
    ctx.emitter.put_rust("");
    ctx.emitter.put_rust("impl Opcode {");
    ctx.emitter
        .put_rust("    /// The raw value stored in `lr`/`pc`.");
    ctx.emitter.put_rust("    pub fn as_u64(self) -> u64 {");
    ctx.emitter.put_rust("        self as u64");
    ctx.emitter.put_rust("    }");
    ctx.emitter.put_rust("");
    ctx.emitter
        .put_rust("    /// Reverses `Opcode::as_u64`. An unknown value (including 0) is");
    ctx.emitter
        .put_rust("    /// `Done`, i.e. return to the caller.");
    ctx.emitter
        .put_rust("    pub fn from_u64(value: u64) -> Opcode {");
    ctx.emitter.put_rust("        match value {");
    for (index, seg) in segments.iter().enumerate() {
        ctx.emitter.put_rust(&format!(
            "            {} => Opcode::{},",
            index + 1,
            seg.name
        ));
    }
    ctx.emitter.put_rust("            _ => Opcode::Done,");
    ctx.emitter.put_rust("        }");
    ctx.emitter.put_rust("    }");
    ctx.emitter.put_rust("}");
    ctx.emitter.put_rust("");
}

fn emit_trait_header(ctx: &mut LowerCtx, _segments: &[Segment]) {
    ctx.emitter.put_rust("/// A compiled offlineasm program.");
    ctx.emitter.put_rust("///");
    ctx.emitter
        .put_rust("/// The generated program is the *provided* half of this trait: one method");
    ctx.emitter
        .put_rust("/// per label plus `InterpretedCode::run`. Implement the hooks for");
    ctx.emitter
        .put_rust("/// whatever the program is embedded in: a JS engine, a bytecode VM, or");
    ctx.emitter
        .put_rust("/// an ordinary Rust program. Nothing here assumes a host calling");
    ctx.emitter
        .put_rust("/// convention: every method takes the owned machine state as");
    ctx.emitter
        .put_rust("/// `m: &mut Machine`, so an implementation can inline the hooks instead");
    ctx.emitter
        .put_rust("/// of looking interpreter state up indirectly.");
    ctx.emitter.put_rust("///");
    ctx.emitter
        .put_rust("/// Only `call_native` must be implemented: the other hooks have default");
    ctx.emitter
        .put_rust("/// bodies that serve the machine's own value stack.");
    ctx.emitter.put_rust("///");
    ctx.emitter
        .put_rust("/// The `Ctx` parameter is free for the implementor, so one generated");
    ctx.emitter
        .put_rust("/// program can be shared by differently-parameterised interpreters.");
    ctx.emitter.put_rust("#[allow(non_snake_case)]");
    ctx.emitter
        .put_rust("pub trait InterpretedCode<Ctx = ()> {");
    ctx.emitter
        .put_rust("    /// Records the frame the program is running on. The default is a");
    ctx.emitter
        .put_rust("    /// no-op: the portable backend keeps the frame in `m.regs.sp`, so");
    ctx.emitter
        .put_rust("    /// there is nothing else to record.");
    ctx.emitter
        .put_rust("    fn stack_set_sp(&mut self, _m: &mut Machine) {}");
    ctx.emitter
        .put_rust("    /// Calls the native function at `target` with the two arguments the");
    ctx.emitter
        .put_rust("    /// calling sequence left in `t0`/`t1`, returning its result. The");
    ctx.emitter
        .put_rust("    /// machine is passed mutably: a hook that arranges a return address");
    ctx.emitter
        .put_rust("    /// or resumes elsewhere can update `m.regs` in place.");
    ctx.emitter.put_rust("    ///");
    ctx.emitter.put_rust("    /// # Safety");
    ctx.emitter
        .put_rust("    /// `target` must be a valid `extern \"C\" fn(u64, u64) -> u64`.");
    ctx.emitter.put_rust("    unsafe fn call_native(");
    ctx.emitter.put_rust("        &mut self,");
    ctx.emitter.put_rust("        m: &mut Machine,");
    ctx.emitter.put_rust("        target: u64,");
    ctx.emitter.put_rust("        arg0: u64,");
    ctx.emitter.put_rust("        arg1: u64,");
    ctx.emitter.put_rust("    ) -> u64;");
    ctx.emitter
        .put_rust("    /// Splits a native call's return value across the `(t0, t1)` register");
    ctx.emitter
        .put_rust("    /// pair the program expects. A host with a two-word value");
    ctx.emitter
        .put_rust("    /// representation (a JS engine, say) decodes it here. A plain Rust");
    ctx.emitter
        .put_rust("    /// program can keep the default `(value, 0)`.");
    ctx.emitter
        .put_rust("    fn native_result(&mut self, _m: &mut Machine, value: u64) -> (u64, u64) {");
    ctx.emitter.put_rust("        (value, 0)");
    ctx.emitter.put_rust("    }");
    ctx.emitter.put_rust("");
}

/// Emits the generated dispatch loop as a provided method.
fn emit_run_method(ctx: &mut LowerCtx, segments: &[Segment]) {
    ctx.emitter
        .put_rust("    /// Runs the program from its first label until it returns to the");
    ctx.emitter
        .put_rust("    /// caller (`ret` with no return address). The register file is");
    ctx.emitter
        .put_rust("    /// cached in a local at entry and written back on exit. Each label");
    ctx.emitter
        .put_rust("    /// takes the cache as an argument and threads it through its return,");
    ctx.emitter
        .put_rust("    /// so inter-label calls preserve nothing. The machine is owned by");
    ctx.emitter
        .put_rust("    /// the caller and passed in. Running the same program on two");
    ctx.emitter.put_rust("    /// machines shares nothing.");
    ctx.emitter.put_rust(
        "    extern \"rust-preserve-none\" fn run(&mut self, m: &mut Machine) -> Opcode {",
    );
    ctx.emitter.put_rust("        let mut regs = m.regs;");
    ctx.emitter.put_rust(&format!(
        "        let mut opcode = Opcode::{};",
        segments[0].name
    ));
    ctx.emitter.put_rust("        loop {");
    ctx.emitter.put_rust("            opcode = match opcode {");
    ctx.emitter.put_rust("                Opcode::Done => {");
    ctx.emitter.put_rust("                    m.regs = regs;");
    ctx.emitter.put_rust("                    return opcode;");
    ctx.emitter.put_rust("                }");
    for seg in segments {
        ctx.emitter
            .put_rust(&format!("                Opcode::{} => {{", seg.name));
        ctx.emitter.put_rust(&format!(
            "                    let (op, nr) = self.{}(&mut *m, regs);",
            seg.name
        ));
        ctx.emitter.put_rust("                    regs = nr;");
        ctx.emitter.put_rust("                    op");
        ctx.emitter.put_rust("                }");
    }
    ctx.emitter.put_rust("            };");
    ctx.emitter.put_rust("        }");
    ctx.emitter.put_rust("    }");
    ctx.emitter.put_rust("");
}

pub fn lower_instruction(
    node: &Node,
    ctx: &mut LowerCtx,
    _flags: LabelFlags<'_>,
) -> Result<(), String> {
    let (opcode, operands) = match node {
        Node::Instruction {
            opcode, operands, ..
        } => (opcode.as_str(), operands.as_slice()),
        _ => return Err("not an instruction".to_string()),
    };

    for operand in operands {
        if let Node::LabelReference { label, .. } = operand {
            if ctx.declared_externs.contains_key(label) {
                ctx.emitter.put_rust(&format!(
                    "    ::core::compile_error!(\"offlineasm: rloop does not support external symbol `{}` (in `{}`)\");",
                    label, opcode
                ));
                return Ok(());
            }
        }
    }
    let op = normalize_op(opcode);
    let reordered = to_dest_last(op, operands);
    let operands: &[Node] = match &reordered {
        Some(v) => v.as_slice(),
        None => operands,
    };

    let local_strings = ctx.local_strings.clone();
    let mut emit = |s: String| ctx.emitter.put_rust(&format!("    {}", s));

    if let Some((_, ty, sym)) = ARITH_OP.iter().find(|(o, _, _)| *o == op) {
        return emit_operation(operands, *ty, sym, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }
    if let Some((_, ty, sym)) = UNARY_OP.iter().find(|(o, _, _)| *o == op) {
        return emit_unary_operation(operands, *ty, sym, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }
    if let Some((_, ty, sym)) = SHIFT_OP.iter().find(|(o, _, _)| *o == op) {
        return emit_shift_operation(operands, *ty, sym, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }
    if let Some((_, ty, cmp)) = CMP_BRANCH.iter().find(|(o, _, _)| *o == op) {
        return emit_compare_and_branch(operands, *ty, cmp, &local_strings, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }
    if let Some((_, cmp)) = DBL_BRANCH.iter().find(|(o, _)| *o == op) {
        return emit_compare_and_branch(operands, Double, cmp, &local_strings, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }
    if let Some((_, cmp)) = DBL_NAN_BRANCH.iter().find(|(o, _)| *o == op) {
        return emit_compare_double_nan_branch(operands, cmp, &local_strings, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }
    if let Some((_, ty, tail)) = TEST_BRANCH.iter().find(|(o, _, _)| *o == op) {
        return emit_test_and_branch_if(operands, *ty, tail, &local_strings, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }
    if let Some((_, ty, cmp)) = CMP_SET.iter().find(|(o, _, _)| *o == op) {
        return emit_compare_and_set(operands, *ty, cmp, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }
    if let Some((_, ty, tail)) = TEST_SET.iter().find(|(o, _, _)| *o == op) {
        return emit_test_set(operands, *ty, tail, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }
    if let Some((_, sym, ty, tail)) = OP_BRANCH.iter().find(|(o, _, _, _)| *o == op) {
        return emit_op_and_branch(operands, sym, *ty, tail, &local_strings, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }
    if let Some((_, sym)) = OVERFLOW_BRANCH.iter().find(|(o, _)| *o == op) {
        return emit_op_and_branch_if_overflow(operands, sym, &local_strings, &mut emit)
            .map_err(|e| format!("{} (in `{}`)", e, opcode));
    }

    match op {
        "localAnnotation" | "globalAnnotation" => Ok(()),
        "emit" => {
            emit(operands.iter().map(|o| o.dump()).collect::<String>());
            Ok(())
        }
        "tagCodePtr" | "tagReturnAddress" | "untagReturnAddress" | "removeCodePtrTag" | "untagArrayPtr" | "removeArrayPtrTag" => {
            Ok(())
        }

        "move" => {
            if operands.len() != 2 {
                return Err(format!("move takes 2 operands, got {}", operands.len()));
            }
            let v = render_value(&operands[0], Int64)?;
            emit_store(&operands[1], v, Int64, &mut emit)
        }
        "sxi2q" => emit_store(&operands[1], render_value(&operands[0], Int32)?, Int64, &mut emit),
        "zxi2q" => emit_store(&operands[1], render_value(&operands[0], Uint32)?, Uint64, &mut emit),
        "sxb2i" => emit_store(&operands[1], render_value(&operands[0], Int8)?, Int32, &mut emit),
        "sxh2i" => emit_store(&operands[1], render_value(&operands[0], Int16)?, Int32, &mut emit),
        "sxb2q" | "sxb2p" => emit_store(&operands[1], render_value(&operands[0], Int8)?, Int64, &mut emit),
        "sxh2q" => emit_store(&operands[1], render_value(&operands[0], Int16)?, Int64, &mut emit),
        "zxb2i" => emit_store(&operands[1], render_value(&operands[0], Uint8)?, Int32, &mut emit),
        "zxh2i" => emit_store(&operands[1], render_value(&operands[0], Uint16)?, Int32, &mut emit),
        "zxb2q" => emit_store(&operands[1], render_value(&operands[0], Uint8)?, Int64, &mut emit),
        "zxh2q" => emit_store(&operands[1], render_value(&operands[0], Uint16)?, Int64, &mut emit),
        "cmov" | "cmovz" => {
            if operands.len() != 3 {
                return Err(format!("{op} needs 3 GPR operands"));
            }
            let cmp = if op == "cmov" { "!=" } else { "==" };
            let t = render_value(&operands[0], Int64)?;
            let s = render_value(&operands[1], Int64)?;
            let d = render_value(&operands[2], Int64)?;
            emit_store(
                &operands[2],
                format!("if {t} {cmp} 0 {{ {s} }} else {{ {d} }}"),
                Int64,
                &mut emit,
            )
        }

        "nop" => {
            emit("// nop".to_string());
            Ok(())
        }

        "memfence" => Ok(()),

        "loadi" => { let v = mem_read(&operands[0], Uint32)?; emit_store(&operands[1], v, Uint32, &mut emit) }
        "loadis" => { let v = mem_read(&operands[0], Int32)?; emit_store(&operands[1], v, Int32, &mut emit) }
        "loadq" => { let v = mem_read(&operands[0], Int64)?; emit_store(&operands[1], v, Int64, &mut emit) }
        "loadp" => { let v = mem_read(&operands[0], Uintptr)?; emit_store(&operands[1], v, Uintptr, &mut emit) }
        "loadb" => { let v = mem_read(&operands[0], Uint8)?; emit_store(&operands[1], v, Uint8, &mut emit) }
        "loadbsi" => {
            let raw = mem_read(&operands[0], Int8)?;
            emit_store(&operands[1], format!("(({}) as i32)", raw), Uint32, &mut emit)
        }
        "loadbsq" => {
            let raw = mem_read(&operands[0], Int8)?;
            emit_store(&operands[1], format!("(({}) as i64)", raw), Uint64, &mut emit)
        }
        "loadh" => { let v = mem_read(&operands[0], Uint16)?; emit_store(&operands[1], v, Uint16, &mut emit) }
        "loadhsi" => {
            let raw = mem_read(&operands[0], Int16)?;
            emit_store(&operands[1], format!("(({}) as i32)", raw), Uint32, &mut emit)
        }
        "loadhsq" => {
            let raw = mem_read(&operands[0], Int16)?;
            emit_store(&operands[1], format!("(({}) as i64)", raw), Uint64, &mut emit)
        }
        "loadd" => { let v = mem_read(&operands[0], Double)?; emit_store(&operands[1], v, Double, &mut emit) }

        "storei" => { let v = render_value(&operands[0], Int32)?; emit_store(&operands[1], v, Int32, &mut emit) }
        "storeq" => { let v = render_value(&operands[0], Int64)?; emit_store(&operands[1], v, Int64, &mut emit) }
        "storep" => { let v = render_value(&operands[0], Intptr)?; emit_store(&operands[1], v, Intptr, &mut emit) }
        "storeb" => { let v = render_value(&operands[0], Int8)?; emit_store(&operands[1], v, Int8, &mut emit) }
        "storeh" => { let v = render_value(&operands[0], Int16)?; emit_store(&operands[1], v, Int16, &mut emit) }
        "stored" => { let v = render_value(&operands[0], Double)?; emit_store(&operands[1], v, Double, &mut emit) }

        "transferi" => { let v = mem_read(&operands[0], Uint32)?; emit_store(&operands[1], v, Uint32, &mut emit) }

        "transferq" => { let v = mem_read(&operands[0], Uint64)?; emit_store(&operands[1], v, Uint64, &mut emit) }
        "transferp" => { let v = mem_read(&operands[0], Uintptr)?; emit_store(&operands[1], v, Uintptr, &mut emit) }

        "ci2ds" => {
            let v = render_value(&operands[0], Int32)?;
            emit_store(&operands[1], format!("(({}) as f64)", v), Double, &mut emit)
        }
        "td2i" => {
            let d = render_value(&operands[0], Double)?;
            emit_store(&operands[1], format!("(({}) as i64)", d), Uint32, &mut emit)
        }
        "bcd2i" => {
            if operands.len() != 3 {
                return Err(format!("bcd2i expects 3 operands, got {}", operands.len()));
            }
            let d = render_value(&operands[0], Double)?;
            let target = branch_target(&operands[2], &local_strings)?;
            emit("{".to_string());
            emit(format!("let __d: f64 = {};", d));
            emit("let __as_i32: i32 = __d as i32;".to_string());
            emit(format!(
                "if (__as_i32 as f64) != __d || (__as_i32 == 0 && __d.is_sign_negative()) {{ {} }}",
                threaded_return(&target)
            ));
            emit_store(&operands[1], "__as_i32".to_string(), Uint32, &mut emit)?;
            emit("}".to_string());
            Ok(())
        }
        "fq2d" => {
            let v = render_value(&operands[0], BitsAsDouble)?;
            emit_store(&operands[1], v, Double, &mut emit)
        }
        "fd2q" => {
            let v = render_value(&operands[0], BitsAsInt64)?;
            emit_store(&operands[1], v, Int64, &mut emit)
        }

        "leai" | "leap" => {
            if operands.len() != 2 {
                return Err(format!("{} expects 2 operands, got {}", op, operands.len()));
            }
            emit_lea(&operands[0], &operands[1], &mut emit)
        }

        "cdqi" => {
            emit("{".to_string());
            emit("let __temp: i64 = ((regs.t0 as u32) as i32) as i64;".to_string());
            emit("regs.t0 = (((__temp as u32) as u64));".to_string());
            emit("regs.t1 = ((((__temp >> 32) as u32) as u64));".to_string());
            emit("}".to_string());
            Ok(())
        }
        "idivi" => {
            if operands.len() != 1 {
                return Err(format!("idivi expects 1 operand, got {}", operands.len()));
            }
            let divisor = render_value(&operands[0], Intptr)?;
            emit("{".to_string());
            emit("let __dividend: i64 = (((((regs.t1 as u32) as u64) << 32) | ((regs.t0 as u32) as u64)) as i64);".to_string());
            emit(format!("let __divisor: i64 = {};", divisor));
            emit("regs.t1 = (((__dividend % __divisor) as u32) as u64);".to_string());
            emit("regs.t0 = (((__dividend / __divisor) as u32) as u64);".to_string());
            emit("}".to_string());
            Ok(())
        }

        "jmp" => {
            if operands.is_empty() {
                return Err("jmp takes at least 1 operand".to_string());
            }
            match &operands[0] {
                Node::LabelReference { .. } | Node::LocalLabelReference { .. } => {
                    let t = branch_target(&operands[0], &local_strings)?;
                    emit(threaded_return(&t));
                    Ok(())
                }
                other => {
                    let v = render_value(other, Opcode)?;
                    emit(threaded_return(&u64_to_opcode(&v)));
                    Ok(())
                }
            }
        }
        "call" => Err(
            "internal: call must be lowered via lower_sequence's segment splitting".to_string(),
        ),
        "break" => {
            emit("panic!(\"rloop: break is not implemented\");".to_string());
            Ok(())
        }
        "ret" => {
            emit(threaded_return(&u64_to_opcode("regs.lr")));
            Ok(())
        }

        "push" => {
            for o in operands {
                let v = render_value(o, Uintptr)?;
                emit(format!("let __push_value: u64 = {};", v));
                emit("regs.sp = regs.sp.wrapping_sub(8);".to_string());
                emit("unsafe { *(regs.sp as *mut u64) = __push_value; }".to_string());
            }
            Ok(())
        }
        "pushCalleeSaves" | "popCalleeSaves" => {
            for o in operands {
                if !matches!(o, Node::Register { .. }) {
                    return Err(format!("{op} takes GPRs only"));
                }
            }
            if op == "pushCalleeSaves" {
                for o in operands {
                    let v = render_value(o, Uintptr)?;
                    emit(format!("let __push_value: u64 = {};", v));
                    emit("regs.sp = regs.sp.wrapping_sub(8);".to_string());
                    emit("unsafe { *(regs.sp as *mut u64) = __push_value; }".to_string());
                }
            } else {
                // Unwinds in the reverse of `pushCalleeSaves`'s order.
                for o in operands.iter().rev() {
                    emit("let __pop_value: u64 = unsafe { *(regs.sp as *const u64) };".to_string());
                    emit("regs.sp = regs.sp.wrapping_add(8);".to_string());
                    emit_store(o, "__pop_value".to_string(), Uintptr, &mut emit)?;
                }
            }
            Ok(())
        }
        "pop" => {
            for o in operands.iter().rev() {
                emit("let __pop_value: u64 = unsafe { *(regs.sp as *const u64) };".to_string());
                emit("regs.sp = regs.sp.wrapping_add(8);".to_string());
                emit_store(o, "__pop_value".to_string(), Uintptr, &mut emit)?;
            }
            Ok(())
        }

        "rloopCrash" => {
            emit("panic!(\"rloop crash\");".to_string());
            Ok(())
        }
        "rloopCallNativeFunction" => {
            Err("internal: rloopCallNativeFunction must be lowered via lower_sequence's segment splitting".to_string())
        }
        "rloopCallNative" => {
            if operands.len() != 1 {
                return Err(format!("rloopCallNative expects 1 operand, got {}", operands.len()));
            }
            let target = render_value(&operands[0], NativeFunc)?;
            emit("{".to_string());
            emit_synced_call(&mut emit, "self.stack_set_sp(&mut *m);".to_string());
            emit(format!("let __target: u64 = {};", target));
            emit("let __a0: u64 = regs.t0;".to_string());
            emit("let __a1: u64 = regs.t1;".to_string());
            emit_synced_call(
                &mut emit,
                "let __r: u64 = unsafe { self.call_native(&mut *m, __target, __a0, __a1) };".to_string(),
            );
            emit("regs.t0 = __r;".to_string());
            emit("}".to_string());
            Ok(())
        }
        "rloopCallSlowPath" | "rloopCallSlowPath3" | "rloopCallSlowPath4" => emit_call_slow_path(operands, false, &mut emit),
        "rloopCallSlowPathVoid" => emit_call_slow_path(operands, true, &mut emit),
        "rloopDo" => {
            if let Node::Instruction { annotation, .. } = node {
                emit(annotation.clone().unwrap_or_default());
            }
            Ok(())
        }

        _ => Err(format!(
            "Unhandled opcode {} for rloop at {}",
            opcode,
            node.origin_string()
        )),
    }
}
