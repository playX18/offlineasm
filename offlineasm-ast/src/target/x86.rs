use std::cell::LazyCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;
use std::sync::LazyLock;

use proc_macro2::Span;
use syn::Ident;

use crate::instructions::*;
use crate::operands::*;
use crate::registers::*;
use crate::stmt::*;

use super::is_setting_set;
use super::is_windows;
use super::Assembler;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperandKind {
    Byte,
    Half,
    Int,
    Quad,
    Ptr,
    Double,
    Float,
}

fn register(name: impl Display) -> String {
    format!("%{name}")
}

fn x86_gpr_name(name: &str, kind: OperandKind) -> syn::Result<String> {
    let name8;
    let name16;
    match name {
        "eax" | "ebx" | "ecx" | "edx" => {
            name8 = format!("{}l", name.chars().next().unwrap());
            name16 = &name[1..];
        }

        "esi" | "edi" | "ebp" | "esp" => {
            name8 = format!("{}l", name.chars().next().unwrap());
            name16 = &name[1..];
        }

        "rax" | "rbx" | "rcx" | "rdx" => {
            name8 = format!("{}b", name.chars().next().unwrap());
            name16 = &name[1..];
        }

        "r8" | "r9" | "r10" | "r11" | "r12" | "r13" | "r14" | "r15" => {
            return Ok(match kind {
                OperandKind::Byte => format!("{name}b"),
                OperandKind::Half => format!("{name}w"),
                OperandKind::Int => format!("{name}l"),
                OperandKind::Quad => format!("{name}q"),
                OperandKind::Ptr => format!("{name}p"),
                _ => {
                    return Err(syn::Error::new(
                        Span::call_site(),
                        "invalid operand kind for gpr",
                    ))
                }
            })
        }

        _ => return Err(syn::Error::new(Span::call_site(), "invalid gpr name")),
    }

    match kind {
        OperandKind::Byte => Ok(register(name8)),
        OperandKind::Half => Ok(register(name16)),
        OperandKind::Int => Ok(register(format!("e{name}"))),
        OperandKind::Quad => Ok(register(format!("r{name}"))),
        OperandKind::Ptr => Ok(register(format!("r{name}"))),
        _ => unreachable!(),
    }
}

const CALL_PREFIX: &str = "*";

fn offset_register(offset: impl Display, reg: impl Display) -> String {
    format!("{offset}({reg})")
}

fn order_operands(operands: &[String]) -> String {
    operands.join(", ")
}

fn constant(expr: impl Display) -> String {
    format!("${expr}")
}

fn constant0x(expr: impl Display) -> String {
    format!("$0x{expr}")
}

impl SpecialRegister {
    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        match kind {
            OperandKind::Half => Ok(format!("%{}w", self.name)),
            OperandKind::Int => Ok(format!("%{}l", self.name)),
            OperandKind::Quad => Ok(format!("%{}q", self.name)),
            OperandKind::Ptr => Ok(format!("%{}p", self.name)),
            OperandKind::Byte => Ok(format!("%{}b", self.name)),
            _ => unreachable!(),
        }
    }

    pub fn x86_call_operand(&self) -> syn::Result<String> {
        Ok(format!(
            "{CALL_PREFIX}{}",
            self.x86_operand(OperandKind::Quad)?
        ))
    }
}

thread_local! {
    static X64_SCRATCH_REGISTER: LazyCell<SpecialRegister> = LazyCell::new(|| SpecialRegister {
        name: Ident::new("r15", Span::call_site()),
    });

    static GPR_MAP: LazyLock<HashMap<Ident, &'static str>> = LazyLock::new(|| {
        let mut map = HashMap::new();

        if is_setting_set("windows") {
            // Windows ABI
            let mapping: [(&[&str], &str); 15] = [
               (&["t0", "r0", "ws0"], "eax"),
               (&["t6", "a0", "wa0"], "ecx"),
               (&["t1", "a1", "wa1"], "edx"),
               (&["t2", "a2", "wa2"], "r8"),
               (&["t3", "a3", "wa3"], "r9"),
               (&["t4"], "r10"),
               (&["csr0"], "edi"),
               (&["csr1"], "esi"),
               (&["csr2"], "ebx"),
               (&["csr3"], "r12"),
               (&["csr4"], "r13"),
               (&["csr5"], "r14"),
               (&["csr6"], "r15"),
               (&["cfr"], "ebp"),
               (&["sp"], "esp"),
            ];

            for (names, reg) in mapping {
                for name in names {
                    map.insert(Ident::new(name, Span::call_site()), reg);
                }
            }
        } else {
            // SystemV ABI
            let mapping: [(&[&str], &str); 15] = [
                (&["t0", "r0", "ws0"], "eax"),
                (&["t6", "a0", "wa0"], "edi"),
                (&["t1", "a1", "wa1"], "esi"),
                (&["t2", "r1", "a2", "wa2"], "edx"),
                (&["t3", "a3", "wa3"], "ecx"),
                (&["t4", "a4", "wa4"], "r8"),
                (&["t5", "ws1"], "r10"),
                (&["t7", "a5", "wa5"], "r9"),
                (&["csr0"], "ebx"),
                (&["csr1"], "r12"),
                (&["csr2"], "r13"),
                (&["csr3"], "r14"),
                (&["csr4"], "r15"),
                (&["cfr"], "ebp"),
                (&["sp"], "esp"),
            ];

            for (names, reg) in mapping {
                for name in names {
                    map.insert(Ident::new(name, Span::call_site()), reg);
                }
            }
        }

        map
    });
    static FPR_MAP: LazyLock<HashMap<Ident, &'static str>> = LazyLock::new(|| {
        let mut map = HashMap::new();
        if is_setting_set("windows") {
            todo!()
        } else {
            // SystemV ABI
            let mapping: [(&[&str], &str); 8] = [
                (&["ft0", "fa0", "fr"], "xmm0"),
                (&["ft1", "fa1"], "xmm1"),
                (&["ft2", "fa2"], "xmm2"),
                (&["ft3", "fa3"], "xmm3"),
                (&["ft4", "fa4"], "xmm4"),
                (&["ft5", "fa5", "wfa5"], "xmm5"),
                (&["ft6", "fa6", "wfa6"], "xmm6"),
                (&["ft7", "fa7", "wfa7"], "xmm7"),
            ];

            for (names, reg) in mapping {
                for name in names {
                    map.insert(Ident::new(name, Span::call_site()), reg);
                }
            }
        }
        map
    });
}

impl GPRegister {
    pub fn supports_8bit_on_x86(&self) -> syn::Result<bool> {
        match self.x86_gpr()? {
            "eax" | "ebx" | "ecx" | "edx" | "edi" | "esi" | "ebp" | "esp" => Ok(true),
            _ => Ok(false),
        }
    }

    pub fn x86_gpr(&self) -> syn::Result<&'static str> {
        GPR_MAP.with(|map| {
            map.get(&self.0)
                .copied()
                .ok_or(syn::Error::new(self.0.span(), "invalid gpr name"))
        })
    }

    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        x86_gpr_name(self.x86_gpr()?, kind)
    }

    pub fn x86_call_operand(&self) -> syn::Result<String> {
        Ok(format!(
            "{CALL_PREFIX}{}",
            self.x86_operand(OperandKind::Ptr)?
        ))
    }
}

impl FPRegister {
    pub fn x86_fpr(&self) -> syn::Result<&'static str> {
        FPR_MAP.with(|map| {
            map.get(&self.0)
                .copied()
                .ok_or(syn::Error::new(self.0.span(), "invalid fpr name"))
        })
    }

    pub fn x86_operand(&self, _kind: OperandKind) -> syn::Result<String> {
        Ok(register(self.x86_fpr()?))
    }
}

impl Constant {
    pub fn x86_operand(&self) -> syn::Result<String> {
        match &self.value {
            ConstantValue::Immediate(imm) => Ok(format!("${imm}")),
            ConstantValue::Reference(x) => Ok(format!("${{_ref_{x}}}")),
            _ => todo!(),
        }
    }
}

impl Address {
    pub fn supports_8bit_on_x86(&self) -> syn::Result<bool> {
        Ok(true)
    }

    pub fn x86_address_operand(&self, address_kind: OperandKind) -> syn::Result<String> {
        match &self.kind {
            AddressKind::Base { base, offset } => {
                let Some(offset) = offset.try_immediate() else {
                    return Err(syn::Error::new(
                        self.span,
                        &format!("address offset was not resolved: {}", self),
                    ));
                };

                let base = base.x86_operand(address_kind)?;

                Ok(offset_register(offset as i64, base))
            }
            AddressKind::Absolute { value } => Ok(format!("${value}")),
            AddressKind::BaseIndex {
                base,
                index,
                scale,
                offset,
            } => {
                let Some(offset) = offset.try_immediate() else {
                    return Err(syn::Error::new(
                        self.span,
                        &format!("address offset was not resolved: {}", self),
                    ));
                };

                let Some(scale) = scale.try_immediate() else {
                    return Err(syn::Error::new(
                        self.span,
                        &format!("address scale was not resolved: {}", self),
                    ));
                };

                let base = base.x86_operand(address_kind)?;
                let index = index.x86_operand(address_kind)?;

                Ok(format!("{offset}({base}, {index}, {scale})"))
            }
        }
    }

    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        let _ = kind;
        self.x86_address_operand(OperandKind::Ptr)
    }

    pub fn x86_call_operand(&self) -> syn::Result<String> {
        Ok(format!(
            "{CALL_PREFIX}{}",
            self.x86_operand(OperandKind::Ptr)?
        ))
    }
}

impl LabelReference {
    pub fn x86_operand(&self, _: OperandKind) -> syn::Result<String> {
        match &self.label {
            LabelMapping::Global(g) => Ok(Assembler::global_label_reference(&g)),
            LabelMapping::Local(l) => Ok(Assembler::local_label_reference(&l)),
        }
    }

    pub fn x86_call_operand(&self) -> syn::Result<String> {
        Ok(format!(
            "{CALL_PREFIX}{}",
            self.x86_operand(OperandKind::Ptr)?
        ))
    }

    pub fn x86_load_operand(
        &self,
        asm: &mut Assembler,
        kind: OperandKind,
        dst: &Operand,
    ) -> syn::Result<String> {
        let _ = kind;
        if !is_windows() {
            asm.format(format_args!(
                "movq {}@GOTPCREL(%rip), {}\n",
                self.x86_operand(OperandKind::Ptr)?,
                dst.x86_operand(OperandKind::Ptr)?
            ));
        } else {
            asm.format(format_args!(
                "lea {}@GOTPCREL(%rip), {}\n",
                self.x86_operand(OperandKind::Ptr)?,
                dst.x86_operand(OperandKind::Ptr)?
            ));
        }

        Ok(offset_register(0, dst.x86_operand(OperandKind::Ptr)?))
    }
}

impl LocalLabelReference {
    pub fn x86_operand(&self, _: OperandKind) -> syn::Result<String> {
        Ok(Assembler::local_label_reference(&self.name))
    }

    pub fn x86_call_operand(&self) -> syn::Result<String> {
        Ok(format!(
            "{CALL_PREFIX}{}",
            self.x86_operand(OperandKind::Ptr)?
        ))
    }
}

impl Operand {
    pub fn supports_8bit_on_x86(&self) -> syn::Result<bool> {
        match self {
            Operand::Address(addr) => addr.supports_8bit_on_x86(),
            Operand::GPRegister(r) => r.supports_8bit_on_x86(),
            _ => Ok(false),
        }
    }

    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        match self {
            Operand::Address(addr) => addr.x86_operand(kind),
            Operand::Constant(c) => c.x86_operand(),
            Operand::GPRegister(r) => r.x86_operand(kind),
            Operand::FPRegister(r) => r.x86_operand(kind),
            _ => todo!(),
        }
    }

    pub fn x86_load_operand(
        &self,
        asm: &mut Assembler,
        kind: OperandKind,
        dst: &Operand,
    ) -> syn::Result<String> {
        match self {
            Operand::LabelReference(lref) => lref.x86_load_operand(asm, kind, dst),
            _ => self.x86_operand(kind),
        }
    }

    pub fn x86_address_operand(&self, kind: OperandKind) -> syn::Result<String> {
        match self {
            Operand::Address(addr) => addr.x86_address_operand(kind),
            _ => {
                return Err(syn::Error::new(
                    self.span(),
                    &format!("invalid operand kind for address operand: {}", self),
                ))
            }
        }
    }

    pub fn asm_label(&self) -> syn::Result<String> {
        match self {
            Operand::LabelReference(lref) => lref.x86_operand(OperandKind::Ptr),
            Operand::LocalLabelReference(lref) => Ok(Assembler::local_label_reference(&lref.name)),
            _ => unreachable!(),
        }
    }
}

impl Instruction {
    pub fn x86_operands(&self, kinds: &[OperandKind]) -> syn::Result<String> {
        let mut output = Vec::new();
        let mut i = 0;
        self.try_for_each_operand::<_, syn::Error>(|operand| {
            output.push(operand.x86_operand(kinds[i])?);
            i += 1;
            Ok(())
        })?;

        Ok(output.join(", "))
    }

    pub fn x86_load_operands(
        &self,
        asm: &mut Assembler,
        dst_kind: OperandKind,
        src_kind: OperandKind,
    ) -> syn::Result<String> {
        let ops = self.operands();
        Ok(order_operands(&[
            ops[1].x86_load_operand(asm, dst_kind, ops[0])?,
            ops[0].x86_operand(src_kind)?,
        ]))
    }

    pub fn x86_suffix(kind: OperandKind) -> &'static str {
        match kind {
            OperandKind::Byte => "b",
            OperandKind::Half => "w",
            OperandKind::Int => "l",
            OperandKind::Quad => "q",
            OperandKind::Ptr => "q",
            OperandKind::Double => "sd",
            OperandKind::Float => "ss",
        }
    }

    pub fn x86_bytes(kind: OperandKind) -> usize {
        match kind {
            OperandKind::Byte => 1,
            OperandKind::Half => 2,
            OperandKind::Int => 4,
            OperandKind::Quad => 8,
            OperandKind::Ptr => 8,
            OperandKind::Double => 8,
            OperandKind::Float => 4,
        }
    }

    pub fn emit_x86_lea(
        dst: &Operand,
        src: &Operand,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        if let Operand::LabelReference(lref) = src {
            if !is_windows() {
                asm.format(format_args!(
                    "movq {}@GOTPCREL(%rip), {}\n",
                    lref.x86_operand(OperandKind::Ptr)?,
                    dst.x86_operand(OperandKind::Ptr)?
                ));
            } else {
                asm.format(format_args!(
                    "lea {}@GOTPCREL(%rip), {}\n",
                    lref.x86_operand(OperandKind::Ptr)?,
                    dst.x86_operand(OperandKind::Ptr)?
                ));
            }
        } else {
            asm.format(format_args!(
                "lea {}, {}\n",
                src.x86_address_operand(kind)?,
                dst.x86_operand(kind)?
            ));
        }
        Ok(())
    }

    pub fn handle_x86_opn(
        &self,
        opcode: &str,
        kind: OperandKind,
        n: usize,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        let ops = self.operands();
        if n == 3 {
            let dst = ops[0];
            let lhs = ops[1];
            let rhs = ops[2];
            if dst == lhs {
                asm.format(format_args!(
                    "{} {}, {}\n",
                    opcode,
                    rhs.x86_operand(kind)?,
                    dst.x86_operand(kind)?,
                ));
            } else if lhs == rhs {
                asm.format(format_args!(
                    "{} {}, {}\n",
                    opcode,
                    lhs.x86_operand(kind)?,
                    dst.x86_operand(kind)?,
                ));
            } else {
                asm.format(format_args!(
                    "mov{suffix} {lhs}, {dst}\n",
                    suffix = Self::x86_suffix(kind),
                    lhs = lhs.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?,
                ));

                asm.format(format_args!(
                    "{opcode} {rhs}, {dst}\n",
                    opcode = opcode,
                    rhs = rhs.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?,
                ));
            }
        } else {
            if n != 2 {
                return Err(syn::Error::new(
                    self.span(),
                    &format!("invalid operand count for instruction: {}", self),
                ));
            }

            let dst = ops[0];
            let src = ops[1];

            asm.format(format_args!(
                "{opcode} {src}, {dst}\n",
                opcode = opcode,
                src = src.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        }

        Ok(())
    }

    pub fn handle_x86_op(
        &self,
        opcode: &str,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        let ops = self.operands();
        self.handle_x86_opn(opcode, kind, ops.len(), asm)?;
        Ok(())
    }

    pub fn handle_x86_shift(
        &self,
        opcode: &str,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        let ops = self.operands();
        match ops[1] {
            Operand::Constant(c)
                if matches!(
                    c.value,
                    ConstantValue::Immediate(_) | ConstantValue::Reference(_)
                ) =>
            {
                asm.format(format_args!(
                    "{opcode} {src}, {dst}\n",
                    opcode = opcode,
                    src = ops[0].x86_operand(OperandKind::Byte)?,
                    dst = ops[1].x86_operand(kind)?,
                ));

                Ok(())
            }
            Operand::GPRegister(r) if r.x86_gpr()? == "ecx" => {
                asm.format(format_args!(
                    "{opcode} {src}, {dst}\n",
                    opcode = opcode,
                    src = ops[0].x86_operand(OperandKind::Byte)?,
                    dst = r.x86_operand(kind)?,
                ));

                Ok(())
            }

            _ => {
                asm.format(format_args!(
                    "xchgq {dst}, %rcx\n",
                    dst = ops[0].x86_operand(kind)?,
                ));

                asm.format(format_args!(
                    "{opcode} %cl, {dst}\n",
                    opcode = opcode,
                    dst = ops[0].x86_operand(kind)?,
                ));

                asm.format(format_args!(
                    "xchgq %rcx, {dst}\n",
                    dst = ops[0].x86_operand(kind)?,
                ));

                Ok(())
            }
        }
    }

    pub fn handle_x86_fp_branch(
        &self,
        branch_opcode: &str,
        reverse: bool,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        if reverse {
            asm.format(format_args!(
                "ucomisd {rhs}, {lhs}\n",
                lhs = self.operands()[0].x86_operand(OperandKind::Double)?,
                rhs = self.operands()[1].x86_operand(OperandKind::Double)?,
            ));
        } else {
            asm.format(format_args!(
                "ucomisd {lhs}, {rhs}\n",
                lhs = self.operands()[0].x86_operand(OperandKind::Double)?,
                rhs = self.operands()[1].x86_operand(OperandKind::Double)?,
            ));
        }

        asm.format(format_args!(
            "{branch_opcode} {label}\n",
            branch_opcode = branch_opcode,
            label = self.operands()[2].asm_label()?,
        ));

        Ok(())
    }

    pub fn handle_x86_icmp(
        &self,
        src_start: usize,
        opcode_suffix: &str,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        let operands = &self.operands()[src_start..];
        let lhs = operands[0];
        let rhs = operands[1];

        match (lhs, rhs) {
            (Operand::Constant(c), Operand::GPRegister(_))
                if c.value == ConstantValue::Immediate(0)
                    && matches!(opcode_suffix, "e" | "ne") =>
            {
                asm.format(format_args!(
                    "test{suffix} {rhs}, {rhs}\n",
                    suffix = Self::x86_suffix(kind),
                    rhs = rhs.x86_operand(kind)?,
                ));
            }

            (Operand::GPRegister(r), Operand::Constant(c))
                if c.value == ConstantValue::Immediate(0)
                    && matches!(opcode_suffix, "e" | "ne") =>
            {
                asm.format(format_args!(
                    "test{suffix} {lhs}, {lhs}\n",
                    suffix = Self::x86_suffix(kind),
                    lhs = lhs.x86_operand(kind)?,
                ));
            }

            _ => {
                asm.format(format_args!(
                    "cmp{suffix} {rhs}, {lhs}\n",
                    suffix = Self::x86_suffix(kind),
                    lhs = lhs.x86_operand(kind)?,
                    rhs = rhs.x86_operand(kind)?,
                ));
            }
        }

        Ok(())
    }

    pub fn handle_x86_branch(
        &self,
        opcode: &str,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        self.handle_x86_icmp(0, &opcode[opcode.len() - 1..], kind, asm)?;
        asm.format(format_args!(
            "{opcode} {label}\n",
            opcode = opcode,
            label = self.operands()[2].asm_label()?,
        ));
        Ok(())
    }

    pub fn handle_x86_set(
        &self,
        set_opcode: &str,
        operand: &Operand,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        if operand.supports_8bit_on_x86()? {
            asm.format(format_args!(
                "{set_opcode} {operand}\n",
                set_opcode = set_opcode,
                operand = operand.x86_operand(OperandKind::Byte)?,
            ));
            asm.format(format_args!(
                "movzbl {src}, {dst}\n",
                src = operand.x86_operand(OperandKind::Byte)?,
                dst = operand.x86_operand(OperandKind::Int)?,
            ));
        } else {
            asm.format(format_args!(
                "xchgq {operand}, %rax\n",
                operand = operand.x86_operand(OperandKind::Int)?,
            ));
            asm.format(format_args!("{set_opcode} %al\n", set_opcode = set_opcode,));

            asm.format(format_args!("movzbl %al, %rax\n",));

            asm.format(format_args!(
                "xchgq %rax, {operand}\n",
                operand = operand.x86_operand(OperandKind::Ptr)?,
            ));
        }

        Ok(())
    }

    pub fn handle_x86_set_icmp(
        &self,
        set_opcode: &str,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        self.handle_x86_icmp(1, &set_opcode[set_opcode.len() - 1..], kind, asm)?;
        self.handle_x86_set(set_opcode, &self.operands()[0], asm)
    }

    pub fn handle_x86_fp_compare_set(
        &self,
        set_opcode: &str,
        reverse: bool,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        let is_special = set_opcode == "eq" || set_opcode == "nequn";

        let operands = self.operands();
        let left = operands[1];
        let right = operands[2];
        let target = operands[0];

        let compare = |lhs: &Operand, rhs: &Operand, asm: &mut Assembler| -> syn::Result<()> {
            asm.format(format_args!(
                "ucomi{suffix} {lhs}, {rhs}\n",
                suffix = Self::x86_suffix(OperandKind::Double),
                lhs = lhs.x86_operand(OperandKind::Double)?,
                rhs = rhs.x86_operand(OperandKind::Double)?,
            ));

            Ok(())
        };

        if is_special {
            match set_opcode {
                "eq" => {
                    if left == right {
                        compare(right, left, asm)?;
                        self.handle_x86_set("setnp", target, asm)?;
                        return Ok(());
                    }

                    let is_unordered = LocalLabel::unique("isUnordred");
                    asm.format(format_args!(
                        "movq $0, {target}\n",
                        target = target.x86_operand(OperandKind::Quad)?,
                    ));
                    compare(right, left, asm)?;
                    asm.format(format_args!(
                        "jp {label}\n",
                        label = Assembler::local_label_reference(&is_unordered)
                    ));
                    self.handle_x86_set("sete", target, asm)?;
                    is_unordered.lower(asm)?;
                    return Ok(());
                }

                "nequn" => {
                    if left == right {
                        compare(right, left, asm)?;
                        self.handle_x86_set("setp", target, asm)?;
                        return Ok(());
                    }

                    let is_unordered = LocalLabel::unique("isUnordred");
                    asm.format(format_args!(
                        "movq $1, {target}\n",
                        target = target.x86_operand(OperandKind::Quad)?,
                    ));
                    compare(right, left, asm)?;
                    asm.format(format_args!(
                        "jp {label}\n",
                        label = Assembler::local_label_reference(&is_unordered)
                    ));
                    self.handle_x86_set("setne", target, asm)?;
                    is_unordered.lower(asm)?;
                    return Ok(());
                }

                _ => (),
            }
        }

        if !reverse {
            compare(right, left, asm)?;
        } else {
            compare(left, right, asm)?;
        }
        self.handle_x86_set(set_opcode, target, asm)
    }

    pub fn handle_x86_test(
        &self,
        src_start: usize,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        let ops = &self.operands()[src_start..];

        let value = ops[0];
        let mask = ops[1];

        match mask {
            Operand::Constant(c) if c.value == ConstantValue::Immediate((-1i64) as i64) => {
                if matches!(value, Operand::GPRegister(_)) {
                    asm.format(format_args!(
                        "test{suffix} {value}, {value}\n",
                        suffix = Self::x86_suffix(kind),
                        value = value.x86_operand(kind)?,
                    ));
                } else {
                    asm.format(format_args!(
                        "cmp{suffix} $0, {value}\n",
                        suffix = Self::x86_suffix(kind),
                        value = value.x86_operand(kind)?,
                    ));
                }
            }

            _ => {
                asm.format(format_args!(
                    "test{suffix} {mask}, {value}\n",
                    suffix = Self::x86_suffix(kind),
                    mask = mask.x86_operand(kind)?,
                    value = value.x86_operand(kind)?,
                ));
            }
        }

        Ok(())
    }

    pub fn handle_x86_branch_test(
        &self,
        branch_opcode: &str,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        self.handle_x86_test(0, kind, asm)?;
        asm.format(format_args!(
            "{branch_opcode} {label}\n",
            branch_opcode = branch_opcode,
            label = self.operands()[2].asm_label()?,
        ));
        Ok(())
    }

    pub fn handle_x86_set_test(
        &self,
        set_opcode: &str,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        self.handle_x86_test(1, kind, asm)?;
        self.handle_x86_set(set_opcode, &self.operands()[0], asm)
    }

    pub fn handle_x86_op_branch(
        &self,
        opcode: &str,
        branch_opcode: &str,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        let operands = self.operands();
        self.handle_x86_opn(opcode, kind, operands.len() - 1, asm)?;
        let jump_target = operands.last().unwrap();

        asm.format(format_args!(
            "{branch_opcode} {label}\n",
            branch_opcode = branch_opcode,
            label = jump_target.asm_label()?,
        ));

        Ok(())
    }

    pub fn handle_x86_add(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let dst = operands[0];
        let lhs = operands[1];
        let rhs = operands[2];

        if lhs == dst {
            match rhs {
                Operand::Constant(c) if c.value == ConstantValue::Immediate(0) => {
                    return Ok(());
                }

                _ => {
                    asm.format(format_args!(
                        "add{suffix} {rhs}, {lhs}\n",
                        suffix = Self::x86_suffix(kind),
                        rhs = rhs.x86_operand(kind)?,
                        lhs = lhs.x86_operand(kind)?
                    ));
                }
            }
        } else if matches!(rhs, Operand::Constant(_)) {
            if !matches!(lhs, Operand::GPRegister(_)) {
                return Err(syn::Error::new(self.span(), "invalid operand"));
            }

            if !matches!(dst, Operand::GPRegister(_)) {
                return Err(syn::Error::new(self.span(), "invalid operand"));
            }

            if matches!(rhs, Operand::Constant(c) if c.value == ConstantValue::Immediate(0)) {
                if lhs != dst {
                    asm.format(format_args!(
                        "mov{suffix} {lhs}, {dst}\n",
                        suffix = Self::x86_suffix(kind),
                        lhs = lhs.x86_operand(kind)?,
                        dst = dst.x86_operand(kind)?
                    ));
                }
            } else {
                asm.format(format_args!(
                    "lea{suffix} {offset}({base}), {dst}",
                    suffix = Self::x86_suffix(kind),
                    offset = rhs.x86_operand(kind)?,
                    base = lhs.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?,
                ));
            }
        } else if matches!(rhs, Operand::GPRegister(_)) {
            if !matches!(lhs, Operand::GPRegister(_)) {
                return Err(syn::Error::new(self.span(), "invalid operand"));
            }

            if !matches!(dst, Operand::GPRegister(_)) {
                return Err(syn::Error::new(self.span(), "invalid operand"));
            }

            if lhs == dst {
                asm.format(format_args!(
                    "add{suffix} {rhs}, {dst}\n",
                    suffix = Self::x86_suffix(kind),
                    rhs = rhs.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?,
                ));
            } else {
                asm.format(format_args!(
                    "lea{suffix} ({lhs}, {rhs}), {dst}",
                    suffix = Self::x86_suffix(kind),
                    lhs = lhs.x86_operand(kind)?,
                    rhs = rhs.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?,
                ));
            }
        } else {
            return Err(syn::Error::new(
                self.span(),
                &format!("invalid x86 add: {}", self),
            ));
        }

        Ok(())
    }

    pub fn handle_x86_sub(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let dst = operands[0];
        let lhs = operands[1];
        let rhs = operands[2];

        if matches!(rhs, Operand::Constant(c) if c.value == ConstantValue::Immediate(0)) {
            if !matches!(lhs, Operand::GPRegister(_)) {
                return Err(syn::Error::new(self.span(), "invalid operand"));
            }

            if !matches!(dst, Operand::GPRegister(_)) {
                return Err(syn::Error::new(self.span(), "invalid operand"));
            }

            if dst != lhs {
                asm.format(format_args!(
                    "mov{suffix} {lhs}, {dst}\n",
                    suffix = Self::x86_suffix(kind),
                    lhs = lhs.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?,
                ));
            }

            return Ok(());
        } else if lhs == dst {
            asm.format(format_args!(
                "neg{suffix} {dst}\n",
                suffix = Self::x86_suffix(kind),
                dst = dst.x86_operand(kind)?,
            ));

            if !matches!(rhs, Operand::Constant(c) if c.value == ConstantValue::Immediate(0)) {
                asm.format(format_args!(
                    "add{suffix} {rhs}, {dst}\n",
                    suffix = Self::x86_suffix(kind),
                    rhs = rhs.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?,
                ));
            }
        } else {
            self.handle_x86_op(
                &format!("sub{suffix}", suffix = Self::x86_suffix(kind)),
                kind,
                asm,
            )?;
        }

        Ok(())
    }

    pub fn handle_x86_mul(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let rhs = operands[2];

        if matches!(rhs, Operand::Constant(c) if matches!(c.value, ConstantValue::Immediate(_) | ConstantValue::Reference(_)))
        {
            asm.format(format_args!(
                "imul{suffix} {operands}",
                suffix = Self::x86_suffix(kind),
                operands = self.x86_operands(&[kind, kind, kind])?
            ));
            return Ok(());
        }

        self.handle_x86_op(
            &format!("imul{suffix}", suffix = Self::x86_suffix(kind)),
            kind,
            asm,
        )
    }

    pub fn handle_x86_add_fp(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let dst = operands[0];
        let lhs = operands[1];
        let rhs = operands[2];

        if lhs == dst {
            asm.format(format_args!(
                "add{suffix} {rhs}, {dst}\n",
                suffix = Self::x86_suffix(kind),
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        } else {
            asm.format(format_args!(
                "vadd{suffix} {lhs}, {rhs}, {dst}\n",
                suffix = Self::x86_suffix(kind),
                lhs = lhs.x86_operand(kind)?,
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        }

        Ok(())
    }

    pub fn handle_x86_sub_fp(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let dst = operands[0];
        let lhs = operands[1];
        let rhs = operands[2];

        if lhs == dst {
            asm.format(format_args!(
                "sub{suffix} {rhs}, {dst}\n",
                suffix = Self::x86_suffix(kind),
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        } else {
            asm.format(format_args!(
                "vsub{suffix} {lhs}, {rhs}, {dst}\n",
                suffix = Self::x86_suffix(kind),
                lhs = lhs.x86_operand(kind)?,
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        }

        Ok(())
    }

    pub fn handle_x86_mul_fp(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let dst = operands[0];
        let lhs = operands[1];
        let rhs = operands[2];

        if lhs == dst {
            asm.format(format_args!(
                "mul{suffix} {rhs}, {dst}\n",
                suffix = Self::x86_suffix(kind),
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        } else {
            asm.format(format_args!(
                "vmul{suffix} {lhs}, {rhs}, {dst}\n",
                suffix = Self::x86_suffix(kind),
                lhs = lhs.x86_operand(kind)?,
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        }

        Ok(())
    }

    pub fn handle_x86_div_fp(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let dst = operands[0];
        let lhs = operands[1];
        let rhs = operands[2];

        if lhs == dst {
            asm.format(format_args!(
                "div{suffix} {rhs}, {dst}\n",
                suffix = Self::x86_suffix(kind),
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        } else {
            asm.format(format_args!(
                "vdiv{suffix} {lhs}, {rhs}, {dst}\n",
                suffix = Self::x86_suffix(kind),
                lhs = lhs.x86_operand(kind)?,
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        }

        Ok(())
    }

    pub fn handle_x86_peek(&self, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let offset = operands[1];
        let dst = operands[0];
        let offset = match offset {
            Operand::Constant(c) => match c.value {
                ConstantValue::Immediate(imm) => {
                    format!("${}", imm.wrapping_mul(size_of::<usize>() as i64))
                }
                ConstantValue::Reference(_ref) => {
                    format!("{}", offset.x86_operand(OperandKind::Ptr)?)
                }
                _ => return Err(syn::Error::new(self.span(), "invalid operand")),
            },

            _ => return Err(syn::Error::new(self.span(), "invalid operand")),
        };

        asm.format(format_args!(
            "movq {offset}(%rsp), {dst}\n",
            offset = offset,
            dst = dst.x86_operand(OperandKind::Ptr)?,
        ));

        Ok(())
    }

    pub fn handle_x86_poke(&self, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let offset = operands[0];
        let src = operands[1];
        let offset = match offset {
            Operand::Constant(c) => match c.value {
                ConstantValue::Immediate(imm) => {
                    format!("${}", imm.wrapping_mul(size_of::<usize>() as i64))
                }
                ConstantValue::Reference(_ref) => {
                    format!("{}", offset.x86_operand(OperandKind::Ptr)?)
                }
                _ => return Err(syn::Error::new(self.span(), "invalid operand")),
            },
            _ => return Err(syn::Error::new(self.span(), "invalid operand")),
        };

        asm.format(format_args!(
            "movq {src}, {offset}(%rsp)\n",
            src = src.x86_operand(OperandKind::Ptr)?,
            offset = offset,
        ));

        Ok(())
    }

    pub fn handle_move(&self, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let dst = operands[0];
        let src = operands[1];

        if let Operand::Constant(c) = &src {
            if let ConstantValue::Immediate(0) = c.value {
                asm.format(format_args!(
                    "xchgq {dst}, {dst}\n",
                    dst = dst.x86_operand(OperandKind::Ptr)?,
                ));
                return Ok(());
            }
        }
        asm.format(format_args!(
            "movq {src}, {dst}\n",
            src = src.x86_operand(OperandKind::Ptr)?,
            dst = dst.x86_operand(OperandKind::Ptr)?,
        ));

        Ok(())
    }

    pub fn count_leading_zeros(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let target = operands[0];
        let src_is_non_zero = LocalLabel::unique("srcIsNonZero");
        let skip_non_zero_case = LocalLabel::unique("skipNonZeroCase");
        let zero_value = Constant::from(8 * Self::x86_bytes(kind) as i64);
        let xor_value = Constant::from(if kind == OperandKind::Quad {
            0x3f
        } else {
            0x1f
        });

        asm.format(format_args!(
            "bsr{suffix} {src}, {target}\n",
            suffix = Self::x86_suffix(kind),
            src = operands[1].x86_operand(kind)?,
            target = operands[0].x86_operand(kind)?
        ));

        let seq: Vec<Stmt> = vec![
            bnz(LocalLabelReference {
                name: src_is_non_zero.clone(),
                span: self.span(),
            })
            .into(),
            mv(target.clone(), zero_value).into(),
            jmp(LocalLabelReference {
                name: skip_non_zero_case.clone(),
                span: self.span(),
            })
            .into(),
            src_is_non_zero.into(),
            if kind == OperandKind::Quad {
                xorq(target.clone(), target.clone(), xor_value).into()
            } else {
                xori(target.clone(), target.clone(), xor_value).into()
            },
            skip_non_zero_case.into(),
        ];

        Stmt::Sequence(Rc::new(Sequence {
            span: self.span(),
            stmts: seq,
        }))
        .lower(asm)?;
        Ok(())
    }

    pub fn count_trailing_zeros(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let target = operands[0];
        let src_is_non_zero = LocalLabel::unique("srcIsNonZero");
        let zero_value = Constant::from(8 * Self::x86_bytes(kind) as i64);

        asm.format(format_args!(
            "bsf{suffix} {src}, {target}\n",
            suffix = Self::x86_suffix(kind),
            src = operands[1].x86_operand(kind)?,
            target = operands[0].x86_operand(kind)?
        ));

        let seq: Vec<Stmt> = vec![
            bnz(LocalLabelReference {
                name: src_is_non_zero.clone(),
                span: self.span(),
            })
            .into(),
            mv(target.clone(), zero_value).into(),
            src_is_non_zero.into(),
        ];

        Stmt::Sequence(Rc::new(Sequence {
            span: self.span(),
            stmts: seq,
        }))
        .lower(asm)?;
        Ok(())
    }

    pub fn truncate_floating_point_to_quad(
        &self,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        let operands = self.operands();
        let src = operands[1];
        let dst = operands[0];

        let slow = LocalLabel::unique("slow");
        let done = LocalLabel::unique("done");

        let gpr_scratch =
            Operand::SpecialRegister(X64_SCRATCH_REGISTER.with(|reg| (**reg).clone()));
        let fpr_scratch = Operand::FPRegister(FPRegister::new(Ident::new("wfa7", self.span())));

        let i64_sign_bit = Constant::from(0x8000000000000000u64 as i64);

        let i64_min;
        let neg_i64_min;
        let i_suffix;
        let f_suffix;

        match kind {
            OperandKind::Float => {
                i64_min = Constant::from(0xdf000000i64);
                neg_i64_min = Constant::from(0x5f000000i64);
                i_suffix = "i";
                f_suffix = "f";
            }

            OperandKind::Double => {
                i64_min = Constant::from(0xc3e0000000000000u64 as i64);
                neg_i64_min = Constant::from(0x43e0000000000000u64 as i64);
                i_suffix = "q";
                f_suffix = "d";
            }
            _ => unreachable!(),
        }

        let seq: Vec<Stmt> = vec![
            mv(gpr_scratch.clone(), neg_i64_min).into(),
            if i_suffix == "i" && f_suffix == "f" {
                fi2f(fpr_scratch.clone(), gpr_scratch.clone()).into()
            } else if i_suffix == "q" && f_suffix == "d" {
                fq2d(fpr_scratch.clone(), gpr_scratch.clone()).into()
            } else {
                unreachable!()
            },
            if f_suffix == "f" {
                bdgteq(
                    src.clone(),
                    fpr_scratch.clone(),
                    LocalLabelReference {
                        name: slow.clone(),
                        span: self.span(),
                    },
                )
                .into()
            } else {
                bfgteq(
                    src.clone(),
                    fpr_scratch.clone(),
                    LocalLabelReference {
                        name: slow.clone(),
                        span: self.span(),
                    },
                )
                .into()
            },
            if f_suffix == "f" {
                truncatef2qs(dst.clone(), src.clone()).into()
            } else {
                truncated2qs(dst.clone(), src.clone()).into()
            },
            jmp(LocalLabelReference {
                name: done.clone(),
                span: self.span(),
            })
            .into(),
            slow.into(),
            mv(gpr_scratch.clone(), i64_min.clone()).into(),
            if i_suffix == "i" && f_suffix == "f" {
                fi2f(fpr_scratch.clone(), gpr_scratch.clone()).into()
            } else if i_suffix == "q" && f_suffix == "d" {
                fq2d(fpr_scratch.clone(), gpr_scratch.clone()).into()
            } else {
                unreachable!()
            },
            if f_suffix == "f" {
                addf(fpr_scratch.clone(), fpr_scratch.clone(), src.clone()).into()
            } else {
                addd(fpr_scratch.clone(), fpr_scratch.clone(), src.clone()).into()
            },
            if f_suffix == "f" {
                truncatef2qs(dst.clone(), fpr_scratch.clone()).into()
            } else {
                truncated2qs(dst.clone(), fpr_scratch.clone()).into()
            },
            mv(gpr_scratch.clone(), i64_sign_bit.clone()).into(),
            orq(dst.clone(), dst.clone(), gpr_scratch.clone()).into(),
            done.into(),
        ];

        Stmt::Sequence(Rc::new(Sequence {
            span: self.span(),
            stmts: seq,
        }))
        .lower(asm)?;

        Ok(())
    }

    pub fn lower_x86(&self, asm: &mut Assembler) -> syn::Result<()> {
        match self {
            Self::Addi(_) => self.handle_x86_add(OperandKind::Int, asm),
            Self::Addp(_) => self.handle_x86_add(OperandKind::Ptr, asm),
            Self::Addq(_) => self.handle_x86_add(OperandKind::Quad, asm),
            Self::Andi(_) => self.handle_x86_op("andl", OperandKind::Int, asm),
            Self::Andp(_) => self.handle_x86_op("andq", OperandKind::Ptr, asm),
            Self::Andq(_) => self.handle_x86_op("andq", OperandKind::Quad, asm),
            Self::Andf(_) => self.handle_x86_op("andps", OperandKind::Float, asm),
            Self::Andd(_) => self.handle_x86_op("andpd", OperandKind::Double, asm),
            Self::Lshifti(_) => self.handle_x86_shift("sall", OperandKind::Int, asm),
            Self::Lshiftp(_) => self.handle_x86_shift("salq", OperandKind::Ptr, asm),
            Self::Lshiftq(_) => self.handle_x86_shift("salq", OperandKind::Quad, asm),
            Self::Muli(_) => self.handle_x86_mul(OperandKind::Int, asm),
            Self::Mulp(_) => self.handle_x86_mul(OperandKind::Ptr, asm),
            Self::Mulq(_) => self.handle_x86_mul(OperandKind::Quad, asm),
            Self::Negi(negi) => {
                asm.format(format_args!(
                    "neg{suffix} {src_dst}",
                    suffix = Self::x86_suffix(OperandKind::Int),
                    src_dst = negi.src_dst.x86_operand(OperandKind::Int)?
                ));
                Ok(())
            }
            Self::Negq(neg) => {
                asm.format(format_args!(
                    "negq {src_dst}",
                    src_dst = neg.src_dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }

            Self::Negp(neg) => {
                asm.format(format_args!(
                    "negq {src_dst}",
                    src_dst = neg.src_dst.x86_operand(OperandKind::Ptr)?
                ));
                Ok(())
            }

            Self::Noti(not) => {
                asm.format(format_args!(
                    "notl {src_dst}",
                    src_dst = not.src_dst.x86_operand(OperandKind::Int)?
                ));
                Ok(())
            }

            Self::Notq(not) => {
                asm.format(format_args!(
                    "notq {src_dst}",
                    src_dst = not.src_dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }

            Self::Ori(_) => self.handle_x86_op("orl", OperandKind::Int, asm),
            Self::Orp(_) => self.handle_x86_op("orq", OperandKind::Ptr, asm),
            Self::Orq(_) => self.handle_x86_op("orq", OperandKind::Quad, asm),
            Self::Orf(_) => self.handle_x86_op("orps", OperandKind::Float, asm),
            Self::Ord(_) => self.handle_x86_op("orpd", OperandKind::Double, asm),
            Self::Orh(_) => self.handle_x86_op("orh", OperandKind::Half, asm),
            Self::Rshifti(_) => self.handle_x86_shift("sarl", OperandKind::Int, asm),
            Self::Rshiftp(_) => self.handle_x86_shift("sarq", OperandKind::Ptr, asm),
            Self::Rshiftq(_) => self.handle_x86_shift("sarq", OperandKind::Quad, asm),
            Self::Urshifti(_) => self.handle_x86_shift("shrl", OperandKind::Int, asm),
            Self::Urshiftp(_) => self.handle_x86_shift("shrl", OperandKind::Ptr, asm),
            Self::Urshiftq(_) => self.handle_x86_shift("shrl", OperandKind::Quad, asm),
            Self::Rrotatei(_) => self.handle_x86_shift("rorl", OperandKind::Int, asm),
            Self::Rrotateq(_) => self.handle_x86_shift("rorq", OperandKind::Quad, asm),
            Self::Lrotatei(_) => self.handle_x86_shift("roll", OperandKind::Int, asm),
            Self::Lrotateq(_) => self.handle_x86_shift("rolq", OperandKind::Quad, asm),

            Self::Subi(_) => self.handle_x86_sub(OperandKind::Int, asm),
            Self::Subp(_) => self.handle_x86_sub(OperandKind::Ptr, asm),
            Self::Subq(_) => self.handle_x86_sub(OperandKind::Quad, asm),
            Self::Xori(_) => self.handle_x86_op("xorl", OperandKind::Int, asm),
            Self::Xorp(_) => self.handle_x86_op("xorq", OperandKind::Ptr, asm),
            Self::Xorq(_) => self.handle_x86_op("xorq", OperandKind::Quad, asm),
            Self::Leap(lea) => Self::emit_x86_lea(&lea.dst, &lea.src, OperandKind::Ptr, asm),
            Self::Leai(lea) => Self::emit_x86_lea(&lea.dst, &lea.src, OperandKind::Int, asm),
            Self::Loadi(_) => {
                let operands = self.x86_load_operands(asm, OperandKind::Int, OperandKind::Int)?;
                asm.format(format_args!("movl {operands}",));

                Ok(())
            }

            Self::Storei(_) => {
                let operands = self.x86_operands(&[OperandKind::Int, OperandKind::Int])?;
                asm.format(format_args!("movl {operands}",));

                Ok(())
            }

            Self::Loadis(_) => {
                let operands = self.x86_load_operands(asm, OperandKind::Int, OperandKind::Int)?;
                asm.format(format_args!("movslq {operands}",));

                Ok(())
            }
            _ => todo!(),
        }
    }
}
