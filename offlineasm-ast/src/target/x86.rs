use std::cell::LazyCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;
use std::sync::LazyLock;

use proc_macro2::Span;
use syn::Ident;

use crate::instructions::*;
use crate::operands::*;
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
    None,
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
        OperandKind::Int => Ok(register(format!("e{name16}"))),
        OperandKind::Quad => Ok(register(format!("r{name16}"))),
        OperandKind::Ptr => Ok(register(format!("r{name16}"))),
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
            ConstantValue::ConstReference(x) => Ok(format!("${{_const_{x}}}")),
            ConstantValue::SymReference(x) => Ok(format!("{{_sym_{x}}}")),
            _ => todo!("constexpr {}", self),
        }
    }

    pub fn x86_call_operand(&self) -> syn::Result<String> {
        Ok(format!("{}", self.x86_operand()?))
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
        Ok(format!("{}", self.x86_operand(OperandKind::Ptr)?))
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
                "movq {}@GOTPCREL(%rip), {}",
                self.x86_operand(OperandKind::Ptr)?,
                dst.x86_operand(OperandKind::Ptr)?
            ));
        } else {
            asm.format(format_args!(
                "lea {}@GOTPCREL(%rip), {}",
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
    pub fn x86_call_operand(&self) -> syn::Result<String> {
        match self {
            Operand::LabelReference(lref) => lref.x86_call_operand(),
            Operand::Address(addr) => addr.x86_call_operand(),
            Operand::Constant(c) => c.x86_call_operand(),
            _ => Err(syn::Error::new(
                self.span(),
                &format!("invalid operand kind for call operand: {}", self),
            )),
        }
    }

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

            _ => todo!("x86 {}", self),
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

impl LocalLabel {
    pub fn asm_label(&self) -> syn::Result<String> {
        Ok(Assembler::local_label_reference(self))
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
            ops[1].x86_load_operand(asm, src_kind, ops[0])?,
            ops[0].x86_operand(dst_kind)?,
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
            OperandKind::None => unreachable!(),
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
            OperandKind::None => unreachable!(),
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
                    "movq {}@GOTPCREL(%rip), {}",
                    lref.x86_operand(OperandKind::Ptr)?,
                    dst.x86_operand(OperandKind::Ptr)?
                ));
            } else {
                asm.format(format_args!(
                    "lea {}@GOTPCREL(%rip), {}",
                    lref.x86_operand(OperandKind::Ptr)?,
                    dst.x86_operand(OperandKind::Ptr)?
                ));
            }
        } else {
            asm.format(format_args!(
                "lea {}, {}",
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
                    "{} {}, {}",
                    opcode,
                    rhs.x86_operand(kind)?,
                    dst.x86_operand(kind)?,
                ));
            } else if lhs == rhs {
                asm.format(format_args!(
                    "{} {}, {}",
                    opcode,
                    lhs.x86_operand(kind)?,
                    dst.x86_operand(kind)?,
                ));
            } else {
                asm.format(format_args!(
                    "mov{suffix} {lhs}, {dst}",
                    suffix = Self::x86_suffix(kind),
                    lhs = lhs.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?,
                ));

                asm.format(format_args!(
                    "{opcode} {rhs}, {dst}",
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
                "{opcode} {src}, {dst}",
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
                    ConstantValue::Immediate(_) | ConstantValue::ConstReference(_)
                ) =>
            {
                asm.format(format_args!(
                    "{opcode} {src}, {dst}",
                    opcode = opcode,
                    src = ops[0].x86_operand(OperandKind::Byte)?,
                    dst = ops[1].x86_operand(kind)?,
                ));

                Ok(())
            }
            Operand::GPRegister(r) if r.x86_gpr()? == "ecx" => {
                asm.format(format_args!(
                    "{opcode} {src}, {dst}",
                    opcode = opcode,
                    src = ops[0].x86_operand(OperandKind::Byte)?,
                    dst = r.x86_operand(kind)?,
                ));

                Ok(())
            }

            _ => {
                asm.format(format_args!(
                    "xchgq {dst}, %rcx",
                    dst = ops[0].x86_operand(kind)?,
                ));

                asm.format(format_args!(
                    "{opcode} %cl, {dst}",
                    opcode = opcode,
                    dst = ops[0].x86_operand(kind)?,
                ));

                asm.format(format_args!(
                    "xchgq %rcx, {dst}",
                    dst = ops[0].x86_operand(kind)?,
                ));

                Ok(())
            }
        }
    }

    pub fn handle_x86_fp_branch(
        &self,
        kind: OperandKind,
        branch_opcode: &str,
        reverse: bool,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        if reverse {
            asm.format(format_args!(
                "ucomi{suffix} {rhs}, {lhs}",
                suffix = Self::x86_suffix(kind),
                lhs = self.operands()[0].x86_operand(OperandKind::Double)?,
                rhs = self.operands()[1].x86_operand(OperandKind::Double)?,
            ));
        } else {
            asm.format(format_args!(
                "ucomi{suffix} {lhs}, {rhs}",
                suffix = Self::x86_suffix(kind),
                lhs = self.operands()[0].x86_operand(OperandKind::Double)?,
                rhs = self.operands()[1].x86_operand(OperandKind::Double)?,
            ));
        }

        asm.format(format_args!(
            "{branch_opcode} {label}",
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
                    "test{suffix} {rhs}, {rhs}",
                    suffix = Self::x86_suffix(kind),
                    rhs = rhs.x86_operand(kind)?,
                ));
            }

            (Operand::GPRegister(_), Operand::Constant(c))
                if c.value == ConstantValue::Immediate(0)
                    && matches!(opcode_suffix, "e" | "ne") =>
            {
                asm.format(format_args!(
                    "test{suffix} {lhs}, {lhs}",
                    suffix = Self::x86_suffix(kind),
                    lhs = lhs.x86_operand(kind)?,
                ));
            }

            _ => {
                asm.format(format_args!(
                    "cmp{suffix} {rhs}, {lhs}",
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
            "{opcode} {label}",
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
                "{set_opcode} {operand}",
                set_opcode = set_opcode,
                operand = operand.x86_operand(OperandKind::Byte)?,
            ));
            asm.format(format_args!(
                "movzbl {src}, {dst}",
                src = operand.x86_operand(OperandKind::Byte)?,
                dst = operand.x86_operand(OperandKind::Int)?,
            ));
        } else {
            asm.format(format_args!(
                "xchgq {operand}, %rax",
                operand = operand.x86_operand(OperandKind::Int)?,
            ));
            asm.format(format_args!("{set_opcode} %al", set_opcode = set_opcode,));

            asm.format(format_args!("movzbl %al, %rax",));

            asm.format(format_args!(
                "xchgq %rax, {operand}",
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
        kind: OperandKind,
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
                "ucomi{suffix} {lhs}, {rhs}",
                suffix = Self::x86_suffix(kind),
                lhs = lhs.x86_operand(kind)?,
                rhs = rhs.x86_operand(kind)?,
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
                        "movq $0, {target}",
                        target = target.x86_operand(OperandKind::Quad)?,
                    ));
                    compare(right, left, asm)?;
                    asm.format(format_args!(
                        "jp {label}",
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
                        "movq $1, {target}",
                        target = target.x86_operand(OperandKind::Quad)?,
                    ));
                    compare(right, left, asm)?;
                    asm.format(format_args!(
                        "jp {label}",
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
                        "test{suffix} {value}, {value}",
                        suffix = Self::x86_suffix(kind),
                        value = value.x86_operand(kind)?,
                    ));
                } else {
                    asm.format(format_args!(
                        "cmp{suffix} $0, {value}",
                        suffix = Self::x86_suffix(kind),
                        value = value.x86_operand(kind)?,
                    ));
                }
            }

            _ => {
                asm.format(format_args!(
                    "test{suffix} {mask}, {value}",
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
            "{branch_opcode} {label}",
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
            "{branch_opcode} {label}",
            branch_opcode = branch_opcode,
            label = jump_target.asm_label()?,
        ));

        Ok(())
    }

    pub fn handle_x86_sub_branch(
        &self,
        branch_opcode: &str,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        let operands = self.operands();
        let dst = operands[0];
        let lhs = operands[1];
        let rhs = operands[2];
        let target = operands[3];

        if dst == lhs {
            asm.format(format_args!(
                "neg{suffix} {dst}",
                suffix = Self::x86_suffix(kind),
                dst = dst.x86_operand(kind)?,
            ));

            asm.format(format_args!(
                "add{suffix} {rhs}, {dst}",
                suffix = Self::x86_suffix(kind),
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        } else {
            self.handle_x86_opn(
                &format!("sub{suffix}", suffix = Self::x86_suffix(kind)),
                kind,
                3,
                asm,
            )?;
        }

        asm.format(format_args!(
            "{branch_opcode} {label}",
            branch_opcode = branch_opcode,
            label = target.asm_label()?,
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
                        "add{suffix} {rhs}, {lhs}",
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
                        "mov{suffix} {lhs}, {dst}",
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
                    "add{suffix} {rhs}, {dst}",
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
                    "mov{suffix} {lhs}, {dst}",
                    suffix = Self::x86_suffix(kind),
                    lhs = lhs.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?,
                ));
            }

            return Ok(());
        } else if rhs == dst {
            asm.format(format_args!(
                "neg{suffix} {dst}",
                suffix = Self::x86_suffix(kind),
                dst = dst.x86_operand(kind)?,
            ));

            if !matches!(rhs, Operand::Constant(c) if c.value == ConstantValue::Immediate(0)) {
                asm.format(format_args!(
                    "add{suffix} {lhs}, {dst}",
                    suffix = Self::x86_suffix(kind),
                    lhs = lhs.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?,
                ));
            }
        } else {
        }

        self.handle_x86_op(
            &format!("sub{suffix}", suffix = Self::x86_suffix(kind)),
            kind,
            asm,
        )?;

        Ok(())
    }

    pub fn handle_x86_mul(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        let operands = self.operands();
        let rhs = operands[2];

        if matches!(rhs, Operand::Constant(c) if matches!(c.value, ConstantValue::Immediate(_) | ConstantValue::ConstReference(_)))
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
                "add{suffix} {rhs}, {dst}",
                suffix = Self::x86_suffix(kind),
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        } else {
            asm.format(format_args!(
                "vadd{suffix} {lhs}, {rhs}, {dst}",
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
                "sub{suffix} {rhs}, {dst}",
                suffix = Self::x86_suffix(kind),
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        } else {
            asm.format(format_args!(
                "vsub{suffix} {lhs}, {rhs}, {dst}",
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
                "mul{suffix} {rhs}, {dst}",
                suffix = Self::x86_suffix(kind),
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        } else {
            asm.format(format_args!(
                "vmul{suffix} {lhs}, {rhs}, {dst}",
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
                "div{suffix} {rhs}, {dst}",
                suffix = Self::x86_suffix(kind),
                rhs = rhs.x86_operand(kind)?,
                dst = dst.x86_operand(kind)?,
            ));
        } else {
            asm.format(format_args!(
                "vdiv{suffix} {lhs}, {rhs}, {dst}",
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
                ConstantValue::ConstReference(_ref) => {
                    format!("{{_const_{}}}", _ref)
                }
                _ => return Err(syn::Error::new(self.span(), "invalid operand")),
            },

            _ => return Err(syn::Error::new(self.span(), "invalid operand")),
        };

        asm.format(format_args!(
            "movq {offset}(%rsp), {dst}",
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
                ConstantValue::ConstReference(_ref) => {
                    format!("{{_const_{}}}", _ref)
                }
                _ => return Err(syn::Error::new(self.span(), "invalid operand")),
            },
            _ => return Err(syn::Error::new(self.span(), "invalid operand")),
        };

        asm.format(format_args!(
            "movq {src}, {offset}(%rsp)",
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
                    "xorq {dst}, {dst}",
                    dst = dst.x86_operand(OperandKind::Ptr)?,
                ));
                return Ok(());
            }
        }
        asm.format(format_args!(
            "movq {src}, {dst}",
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
            "bsr{suffix} {src}, {target}",
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
            "bsf{suffix} {src}, {target}",
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

    pub fn convert_quad_to_floating_point(
        &self,
        kind: OperandKind,
        asm: &mut Assembler,
    ) -> syn::Result<()> {
        let operands = self.operands();
        let scratch1 = operands[2];
        let src = operands[1];
        let dst = operands[0];

        let scratch2 = Operand::SpecialRegister(X64_SCRATCH_REGISTER.with(|reg| (**reg).clone()));

        let slow = LocalLabel::unique("slow");
        let done = LocalLabel::unique("done");

        let seq: Vec<Stmt> = vec![
            btqs(
                src.clone(),
                src.clone(),
                LocalLabelReference::new(slow.clone()),
            )
            .into(),
            if kind == OperandKind::Float {
                cq2fs(dst.clone(), src.clone()).into()
            } else {
                cq2ds(dst.clone(), src.clone()).into()
            },
            jmp(LocalLabelReference::new(done.clone())).into(),
            slow.into(),
            mv(scratch1.clone(), src.clone()).into(),
            mv(scratch2.clone(), src.clone()).into(),
            urshiftq(scratch1.clone(), 1usize).into(),
            andq(scratch1.clone(), scratch1.clone(), 1usize).into(),
            orq(scratch1.clone(), scratch1.clone(), scratch2.clone()).into(),
            if kind == OperandKind::Float {
                cq2fs(dst.clone(), scratch1.clone()).into()
            } else {
                cq2ds(dst.clone(), scratch1.clone()).into()
            },
            if kind == OperandKind::Float {
                addf(dst.clone(), dst.clone(), dst.clone()).into()
            } else {
                addd(dst.clone(), dst.clone(), dst.clone()).into()
            },
            done.into(),
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
            Self::Addi(_) | Self::Addp(_) | Self::Addq(_) => {
                self.handle_x86_add(self.x86_operand_kind(), asm)
            }
            Self::Andi(_) | Self::Andp(_) | Self::Andq(_) | Self::Andf(_) | Self::Andd(_) => {
                self.handle_x86_op("and", self.x86_operand_kind(), asm)
            }
            Self::Lshifti(_) | Self::Lshiftp(_) | Self::Lshiftq(_) => {
                self.handle_x86_shift("sal", self.x86_operand_kind(), asm)
            }
            Self::Muli(_) | Self::Mulp(_) | Self::Mulq(_) => {
                self.handle_x86_mul(self.x86_operand_kind(), asm)
            }
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

            Self::Ori(_) | Self::Orp(_) | Self::Orq(_) | Self::Orh(_) => {
                self.handle_x86_op("or", self.x86_operand_kind(), asm)
            }

            Self::Orf(_) => self.handle_x86_op("orps", OperandKind::Float, asm),
            Self::Ord(_) => self.handle_x86_op("orpd", OperandKind::Double, asm),

            Self::Rshifti(_) | Self::Rshiftp(_) | Self::Rshiftq(_) => {
                self.handle_x86_shift("sar", self.x86_operand_kind(), asm)
            }
            Self::Urshifti(_) | Self::Urshiftp(_) | Self::Urshiftq(_) => {
                self.handle_x86_shift("shrl", self.x86_operand_kind(), asm)
            }
            Self::Rrotatei(_) | Self::Rrotateq(_) => {
                self.handle_x86_shift("ror", self.x86_operand_kind(), asm)
            }

            Self::Lrotatei(_) | Self::Lrotateq(_) => {
                self.handle_x86_shift("rol", self.x86_operand_kind(), asm)
            }

            Self::Subi(_) | Self::Subp(_) | Self::Subq(_) => {
                self.handle_x86_sub(self.x86_operand_kind(), asm)
            }

            Self::Xori(_) | Self::Xorp(_) | Self::Xorq(_) => {
                self.handle_x86_op("xor", self.x86_operand_kind(), asm)
            }

            Self::Leap(lea) => Self::emit_x86_lea(&lea.dst, &lea.src, OperandKind::Ptr, asm),
            Self::Leai(lea) => Self::emit_x86_lea(&lea.dst, &lea.src, OperandKind::Int, asm),
            Self::Loadi(_) => {
                let operands = self.x86_load_operands(asm, OperandKind::Int, OperandKind::Int)?;
                asm.format(format_args!("movl {operands}",));

                Ok(())
            }

            Self::Storei(st) => {
                let src = st.src.x86_operand(OperandKind::Int)?;
                let dst = st.addr.x86_operand(OperandKind::Int)?;

                asm.format(format_args!("movl {src}, {dst}",));

                Ok(())
            }

            Self::Loadis(ld) => {
                let src = ld.addr.x86_load_operand(asm, OperandKind::Int, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Int)?;

                asm.format(format_args!("movslq {src}, {dst}",));

                Ok(())
            }

            Self::Loadp(ld) => {
                let src = ld.addr.x86_load_operand(asm, OperandKind::Ptr, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Ptr)?;

                asm.format(format_args!("movq {src}, {dst}",));

                Ok(())
            }

            Self::Storep(st) => {
                let src = st.src.x86_operand(OperandKind::Ptr)?;
                let dst = st.dst.x86_operand(OperandKind::Ptr)?;

                asm.format(format_args!("movq {src}, {dst}",));

                Ok(())
            }

            Self::Loadq(ld) => {
                let src = ld.src.x86_load_operand(asm, OperandKind::Quad, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Quad)?;

                asm.format(format_args!("movq {src}, {dst}",));

                Ok(())
            }

            Self::Storeq(st) => {
                let src = st.src.x86_operand(OperandKind::Quad)?;
                let dst = st.dst.x86_operand(OperandKind::Quad)?;

                asm.format(format_args!("movq {src}, {dst}",));

                Ok(())
            }

            Self::Loadb(ld) => {
                let src = ld.addr.x86_load_operand(asm, OperandKind::Int, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Int)?;

                asm.format(format_args!("movzbl {src}, {dst}",));

                Ok(())
            }

            Self::Loadbsi(ld) => {
                let src = ld.addr.x86_load_operand(asm, OperandKind::Int, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Int)?;

                asm.format(format_args!("movsbl {src}, {dst}",));

                Ok(())
            }

            Self::Loadbsq(ld) => {
                let src = ld.addr.x86_load_operand(asm, OperandKind::Quad, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Int)?;

                asm.format(format_args!("movsbl {src}, {dst}",));

                Ok(())
            }

            Self::Loadh(ld) => {
                let src = ld.addr.x86_load_operand(asm, OperandKind::Int, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Int)?;

                asm.format(format_args!("movzwl {src}, {dst}",));

                Ok(())
            }

            Self::Loadhsi(ld) => {
                let src = ld.addr.x86_load_operand(asm, OperandKind::Int, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Int)?;

                asm.format(format_args!("movswl {src}, {dst}",));

                Ok(())
            }

            Self::Loadhsq(ld) => {
                let src = ld.addr.x86_load_operand(asm, OperandKind::Quad, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Int)?;

                asm.format(format_args!("movswq {src}, {dst}",));

                Ok(())
            }

            Self::Storeb(st) => {
                let src = st.src.x86_operand(OperandKind::Byte)?;
                let dst = st.addr.x86_operand(OperandKind::Ptr)?;

                asm.format(format_args!("movb {src}, {dst}",));

                Ok(())
            }

            Self::Storeh(st) => {
                let src = st.src.x86_operand(OperandKind::Half)?;
                let dst = st.addr.x86_operand(OperandKind::Half)?;

                asm.format(format_args!("movw {src}, {dst}",));

                Ok(())
            }

            Self::Loadf(ld) => {
                let src = ld.addr.x86_load_operand(asm, OperandKind::Float, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Float)?;

                asm.format(format_args!("movss {src}, {dst}",));

                Ok(())
            }

            Self::Loadd(ld) => {
                let src = ld
                    .addr
                    .x86_load_operand(asm, OperandKind::Double, &ld.dst)?;
                let dst = ld.dst.x86_operand(OperandKind::Double)?;

                asm.format(format_args!("movsd {src}, {dst}",));

                Ok(())
            }

            Self::Loadv(lv) => {
                asm.format(format_args!(
                    "movdqu {src}, {dst}",
                    src = lv.addr.x86_operand(OperandKind::Int)?,
                    dst = lv.dst.x86_operand(OperandKind::Double)?
                ));

                Ok(())
            }

            Self::Storef(sf) => {
                let src = sf.src.x86_operand(OperandKind::Float)?;
                let dst = sf.addr.x86_operand(OperandKind::Float)?;

                asm.format(format_args!("movss {src}, {dst}",));

                Ok(())
            }

            Self::Stored(sd) => {
                let src = sd.src.x86_operand(OperandKind::Double)?;
                let dst = sd.addr.x86_operand(OperandKind::Double)?;

                asm.format(format_args!("movsd {src}, {dst}",));

                Ok(())
            }

            Self::Storev(sv) => {
                asm.format(format_args!(
                    "movdqu {src}, {dst}",
                    src = sv.src.x86_operand(OperandKind::Double)?,
                    dst = sv.addr.x86_operand(OperandKind::Int)?
                ));

                Ok(())
            }

            Self::Moved(mv) => {
                asm.format(format_args!(
                    "movsd {src}, {dst}",
                    src = mv.src.x86_operand(OperandKind::Double)?,
                    dst = mv.dst.x86_operand(OperandKind::Double)?
                ));

                Ok(())
            }

            Self::Addf(_) | Self::Addd(_) => self.handle_x86_add_fp(self.x86_operand_kind(), asm),
            Self::Subf(_) | Self::Subd(_) => self.handle_x86_sub_fp(self.x86_operand_kind(), asm),
            Self::Mulf(_) | Self::Muld(_) => self.handle_x86_mul_fp(self.x86_operand_kind(), asm),
            Self::Divf(_) | Self::Divd(_) => self.handle_x86_div_fp(self.x86_operand_kind(), asm),

            Self::Sqrtf(Sqrtf { dst, src, .. }) | Self::Sqrtd(Sqrtd { dst, src, .. }) => {
                let kind = self.x86_operand_kind();
                asm.format(format_args!(
                    "sqrt{suffix} {src}, {dst}",
                    suffix = Self::x86_suffix(kind),
                    src = src.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?
                ));
                Ok(())
            }

            Self::Roundf(Roundf { dst, src, .. }) | Self::Roundd(Roundd { dst, src, .. }) => {
                let kind = self.x86_operand_kind();
                asm.format(format_args!(
                    "round{suffix} $0, {src}, {dst}",
                    suffix = Self::x86_suffix(kind),
                    src = src.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?
                ));
                Ok(())
            }

            Self::Floorf(Floorf { dst, src, .. }) | Self::Floord(Floord { dst, src, .. }) => {
                let kind = self.x86_operand_kind();
                asm.format(format_args!(
                    "round{suffix} $1, {src}, {dst}",
                    suffix = Self::x86_suffix(kind),
                    src = src.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?
                ));
                Ok(())
            }

            Self::Ceilf(Ceilf { dst, src, .. }) | Self::Ceild(Ceild { dst, src, .. }) => {
                let kind = self.x86_operand_kind();
                asm.format(format_args!(
                    "round{suffix} $2, {src}, {dst}",
                    suffix = Self::x86_suffix(kind),
                    src = src.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?
                ));
                Ok(())
            }

            Self::Truncatef(Truncatef { dst, src, .. })
            | Self::Truncated(Truncated { dst, src, .. }) => {
                let kind = self.x86_operand_kind();
                asm.format(format_args!(
                    "round{suffix} $3, {src}, {dst}",
                    suffix = Self::x86_suffix(kind),
                    src = src.x86_operand(kind)?,
                    dst = dst.x86_operand(kind)?
                ));
                Ok(())
            }

            Self::Truncatef2i(Truncatef2i { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvttss2si {}, {}",
                    src.x86_operand(OperandKind::Float)?,
                    dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }
            Self::Truncated2i(Truncated2i { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvttsd2si {}, {}",
                    src.x86_operand(OperandKind::Double)?,
                    dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }
            Self::Truncatef2q(Truncatef2q { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvttss2si {}, {}",
                    src.x86_operand(OperandKind::Float)?,
                    dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }
            Self::Truncated2q(Truncated2q { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvttsd2si {}, {}",
                    src.x86_operand(OperandKind::Double)?,
                    dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }
            Self::Truncatef2is(Truncatef2is { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvttss2si {}, {}",
                    src.x86_operand(OperandKind::Float)?,
                    dst.x86_operand(OperandKind::Int)?
                ));
                Ok(())
            }
            Self::Truncatef2qs(Truncatef2qs { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvttss2si {}, {}",
                    src.x86_operand(OperandKind::Float)?,
                    dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }
            Self::Truncated2is(Truncated2is { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvttsd2si {}, {}",
                    src.x86_operand(OperandKind::Double)?,
                    dst.x86_operand(OperandKind::Int)?
                ));
                Ok(())
            }
            Self::Truncated2qs(Truncated2qs { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvttsd2si {}, {}",
                    src.x86_operand(OperandKind::Double)?,
                    dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }
            Self::Ci2d(Ci2d { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvtsi2sd {}, {}",
                    src.x86_operand(OperandKind::Quad)?,
                    dst.x86_operand(OperandKind::Double)?
                ));
                Ok(())
            }
            Self::Ci2ds(Ci2ds { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvtsi2sd {}, {}",
                    src.x86_operand(OperandKind::Int)?,
                    dst.x86_operand(OperandKind::Double)?
                ));
                Ok(())
            }
            Self::Ci2fs(Ci2fs { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvtsi2ss {}, {}",
                    src.x86_operand(OperandKind::Int)?,
                    dst.x86_operand(OperandKind::Float)?
                ));
                Ok(())
            }
            Self::Ci2f(Ci2f { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvtsi2ss {}, {}",
                    src.x86_operand(OperandKind::Quad)?,
                    dst.x86_operand(OperandKind::Float)?
                ));
                Ok(())
            }

            Self::Cq2f(_) => self.convert_quad_to_floating_point(OperandKind::Float, asm),
            Self::Cq2d(_) => self.convert_quad_to_floating_point(OperandKind::Double, asm),
            Self::Cq2fs(Cq2fs { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvtsi2ssq {src}, {dst}",
                    src = src.x86_operand(OperandKind::Quad)?,
                    dst = dst.x86_operand(OperandKind::Float)?
                ));
                Ok(())
            }

            Self::Cq2ds(Cq2ds { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvtsi2sdq {src}, {dst}",
                    src = src.x86_operand(OperandKind::Quad)?,
                    dst = dst.x86_operand(OperandKind::Double)?
                ));
                Ok(())
            }

            Self::Cd2f(Cd2f { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvtsd2ss {src}, {dst}",
                    src = src.x86_operand(OperandKind::Double)?,
                    dst = dst.x86_operand(OperandKind::Float)?
                ));
                Ok(())
            }
            Self::Cf2d(Cf2d { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvtss2sd {src}, {dst}",
                    src = src.x86_operand(OperandKind::Float)?,
                    dst = dst.x86_operand(OperandKind::Double)?
                ));
                Ok(())
            }

            Self::Bdeq(Bdeq {
                lhs, rhs, target, ..
            }) => {
                asm.format(format_args!(
                    "ucomisd {lhs}, {rhs}",
                    lhs = lhs.x86_operand(OperandKind::Double)?,
                    rhs = rhs.x86_operand(OperandKind::Double)?
                ));

                if lhs == rhs {
                    // this is just a jump ordered, which is a jnp.
                    asm.format(format_args!("jnp {}", target.asm_label()?));
                } else {
                    let is_unordered = LocalLabel::unique("bdeq");
                    asm.format(format_args!("jp {}", is_unordered.asm_label()?));
                    asm.format(format_args!("je {}", target.asm_label()?));
                    is_unordered.lower(asm)?;
                }

                Ok(())
            }

            Self::Bdneq(_) => self.handle_x86_fp_branch(OperandKind::Double, "jne", false, asm),
            Self::Bdgt(_) => self.handle_x86_fp_branch(OperandKind::Double, "ja", false, asm),
            Self::Bdgteq(_) => self.handle_x86_fp_branch(OperandKind::Double, "jae", false, asm),
            Self::Bdlt(_) => self.handle_x86_fp_branch(OperandKind::Double, "ja", true, asm),
            Self::Bdlteq(_) => self.handle_x86_fp_branch(OperandKind::Double, "jae", true, asm),
            Self::Bdequn(_) => self.handle_x86_fp_branch(OperandKind::Double, "je", false, asm),
            Self::Bdnequn(Bdnequn {
                lhs, rhs, target, ..
            }) => {
                asm.format(format_args!(
                    "ucomisd {lhs}, {rhs}",
                    lhs = lhs.x86_operand(OperandKind::Double)?,
                    rhs = rhs.x86_operand(OperandKind::Double)?
                ));

                if lhs == rhs {
                    // this is just a jump unordered, which is a jp.
                    asm.format(format_args!("jp {}", target.asm_label()?));
                } else {
                    let is_unordered = LocalLabel::unique("bdnequn");
                    let is_equal = LocalLabel::unique("bdnequn");
                    asm.format(format_args!("jp {}", is_unordered.asm_label()?));
                    asm.format(format_args!("je {}", is_equal.asm_label()?));
                    is_unordered.lower(asm)?;
                    asm.format(format_args!("jmp {}", target.asm_label()?));
                    is_equal.lower(asm)?;
                }

                Ok(())
            }

            Self::Bdgtun(_) => self.handle_x86_fp_branch(OperandKind::Double, "jb", true, asm),
            Self::Bdgtequn(_) => self.handle_x86_fp_branch(OperandKind::Double, "jbe", true, asm),
            Self::Bdltun(_) => self.handle_x86_fp_branch(OperandKind::Double, "jb", false, asm),
            Self::Bdltequn(_) => self.handle_x86_fp_branch(OperandKind::Double, "jbe", false, asm),
            Self::Bfeq(Bfeq {
                lhs, rhs, target, ..
            }) => {
                asm.format(format_args!(
                    "ucomiss {lhs}, {rhs}",
                    lhs = lhs.x86_operand(OperandKind::Float)?,
                    rhs = rhs.x86_operand(OperandKind::Float)?
                ));

                if lhs == rhs {
                    // this is just a jump ordered, which is a jnp.
                    asm.format(format_args!("jnp {}", target.asm_label()?));
                } else {
                    let is_unordered = LocalLabel::unique("bfeq");
                    asm.format(format_args!("jp {}", is_unordered.asm_label()?));
                    asm.format(format_args!("je {}", target.asm_label()?));
                    is_unordered.lower(asm)?;
                }

                Ok(())
            }

            Self::Bfgt(_) => self.handle_x86_fp_branch(OperandKind::Float, "ja", false, asm),
            Self::Bfgteq(_) => self.handle_x86_fp_branch(OperandKind::Float, "jae", false, asm),
            Self::Bflt(_) => self.handle_x86_fp_branch(OperandKind::Float, "ja", true, asm),
            Self::Bflteq(_) => self.handle_x86_fp_branch(OperandKind::Float, "jae", true, asm),
            Self::Bfgtun(_) => self.handle_x86_fp_branch(OperandKind::Float, "jb", true, asm),
            Self::Bfgtequn(_) => self.handle_x86_fp_branch(OperandKind::Float, "jbe", true, asm),
            Self::Bfltun(_) => self.handle_x86_fp_branch(OperandKind::Float, "jb", false, asm),
            Self::Bfltequn(_) => self.handle_x86_fp_branch(OperandKind::Float, "jbe", false, asm),

            Self::Btd2i(Btd2i {
                dst, src, target, ..
            }) => {
                asm.format(format_args!(
                    "cvttsd2si {src}, {dst}",
                    src = src.x86_operand(OperandKind::Double)?,
                    dst = dst.x86_operand(OperandKind::Int)?
                ));
                asm.format(format_args!(
                    "cmpl $0x80000000, {dst}",
                    dst = dst.x86_operand(OperandKind::Int)?
                ));
                asm.format(format_args!("je {}", target.asm_label()?));
                Ok(())
            }

            Self::Td2i(Td2i { dst, src, .. }) => {
                asm.format(format_args!(
                    "cvttsd2si {src}, {dst}",
                    src = src.x86_operand(OperandKind::Double)?,
                    dst = dst.x86_operand(OperandKind::Int)?
                ));
                Ok(())
            }

            Self::Bcd2i(Bcd2i {
                dst, src, target, ..
            }) => {
                asm.format(format_args!(
                    "cvttsd2si {src}, {dst}",
                    src = src.x86_operand(OperandKind::Double)?,
                    dst = dst.x86_operand(OperandKind::Int)?
                ));
                asm.format(format_args!(
                    "testl {dst}, {dst}",
                    dst = dst.x86_operand(OperandKind::Int)?
                ));
                asm.format(format_args!("je {}", target.asm_label()?));
                asm.format(format_args!(
                    "cvtsi2sd {dst}, %xmm7",
                    dst = dst.x86_operand(OperandKind::Int)?
                ));
                asm.format(format_args!(
                    "ucomisd {src}, %xmm7",
                    src = src.x86_operand(OperandKind::Double)?
                ));
                asm.format(format_args!("jp {}", target.asm_label()?));
                asm.format(format_args!("jne {}", target.asm_label()?));
                Ok(())
            }

            Self::Movdz(Movdz { dst, .. }) => {
                asm.format(format_args!(
                    "xorpd {dst}, {dst}",
                    dst = dst.x86_operand(OperandKind::Double)?
                ));
                Ok(())
            }

            Self::Pop(Pop { dst, .. }) => {
                asm.format(format_args!(
                    "pop {dst}",
                    dst = dst.x86_operand(OperandKind::Ptr)?
                ));
                Ok(())
            }

            Self::Popv(Popv { dst, .. }) => {
                asm.format(format_args!(
                    "movdqu (%rsp), {dst}",
                    dst = dst.x86_operand(OperandKind::Double)?
                ));
                asm.format(format_args!("add $16, %rsp"));
                Ok(())
            }

            Self::Push(Push { src, .. }) => {
                asm.format(format_args!(
                    "push {src}",
                    src = src.x86_operand(OperandKind::Ptr)?
                ));
                Ok(())
            }

            Self::Pushv(Pushv { src, .. }) => {
                asm.format(format_args!("sub $16, %rsp"));
                asm.format(format_args!(
                    "movdqu {src}, (%rsp)",
                    src = src.x86_operand(OperandKind::Double)?
                ));
                Ok(())
            }

            Self::Mv(_) => {
                self.handle_move(asm)?;
                Ok(())
            }

            Self::Sxi2q(Sxi2q { dst, src, .. }) => {
                asm.format(format_args!(
                    "movslq {src}, {dst}",
                    src = src.x86_operand(OperandKind::Int)?,
                    dst = dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }

            Self::Zxi2q(Zxi2q { dst, src, .. }) => {
                asm.format(format_args!(
                    "movl {src}, {dst}",
                    src = src.x86_operand(OperandKind::Int)?,
                    dst = dst.x86_operand(OperandKind::Int)?
                ));
                Ok(())
            }

            Self::Sxb2i(Sxb2i { dst, src, .. }) => {
                asm.format(format_args!(
                    "movsbl {src}, {dst}",
                    src = src.x86_operand(OperandKind::Byte)?,
                    dst = dst.x86_operand(OperandKind::Int)?
                ));
                Ok(())
            }
            Self::Sxh2i(Sxh2i { dst, src, .. }) => {
                asm.format(format_args!(
                    "movswl {src}, {dst}",
                    src = src.x86_operand(OperandKind::Half)?,
                    dst = dst.x86_operand(OperandKind::Int)?
                ));
                Ok(())
            }

            Self::Sxb2q(Sxb2q { dst, src, .. }) => {
                asm.format(format_args!(
                    "movsbq {src}, {dst}",
                    src = src.x86_operand(OperandKind::Byte)?,
                    dst = dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }

            Self::Sxh2q(Sxh2q { dst, src, .. }) => {
                asm.format(format_args!(
                    "movswq {src}, {dst}",
                    src = src.x86_operand(OperandKind::Half)?,
                    dst = dst.x86_operand(OperandKind::Quad)?
                ));
                Ok(())
            }

            Self::Nop(_) => {
                asm.format(format_args!("nop"));
                Ok(())
            }

            Self::Bieq(_) | Self::Bpeq(_) | Self::Bqeq(_) | Self::Bbeq(_) => {
                self.handle_x86_branch("je", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Bineq(_) | Self::Bpneq(_) | Self::Bqneq(_) | Self::Bbneq(_) => {
                self.handle_x86_branch("jne", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Bia(_) | Self::Bpa(_) | Self::Bqa(_) | Self::Bba(_) => {
                self.handle_x86_branch("ja", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Biaeq(_) | Self::Bpaeq(_) | Self::Bqaeq(_) | Self::Bbaeq(_) => {
                self.handle_x86_branch("jae", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Bib(_) | Self::Bpb(_) | Self::Bqb(_) | Self::Bbb(_) => {
                self.handle_x86_branch("jb", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Bibeq(_) | Self::Bpbeq(_) | Self::Bqbeq(_) | Self::Bbbeq(_) => {
                self.handle_x86_branch("jbe", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Bigt(_) | Self::Bpgt(_) | Self::Bqgt(_) | Self::Bbgt(_) => {
                self.handle_x86_branch("jg", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Bilt(_) | Self::Bplt(_) | Self::Bqlt(_) | Self::Bblt(_) => {
                self.handle_x86_branch("jl", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Bilteq(_) | Self::Bplteq(_) | Self::Bqlteq(_) | Self::Bblteq(_) => {
                self.handle_x86_branch("jle", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Bigteq(_) | Self::Bpgteq(_) | Self::Bqgteq(_) | Self::Bbgteq(_) => {
                self.handle_x86_branch("jge", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Btis(_) | Self::Btps(_) | Self::Btqs(_) | Self::Btbs(_) => {
                self.handle_x86_branch_test("js", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Btiz(_) | Self::Btpz(_) | Self::Btqz(_) | Self::Btbz(_) => {
                self.handle_x86_branch_test("jz", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Btinz(_) | Self::Btpnz(_) | Self::Btqnz(_) | Self::Btbnz(_) => {
                self.handle_x86_branch_test("jnz", self.x86_operand_kind(), asm)?;
                Ok(())
            }

            Self::Jmp(Jmp { target, .. }) => {
                asm.format(format_args!("jmp {}", target.asm_label()?));
                Ok(())
            }

            Self::Baddio(_) | Self::Baddpo(_) | Self::Baddqo(_) => {
                let kind = self.x86_operand_kind();
                let suffix = Self::x86_suffix(kind);
                self.handle_x86_op_branch(&format!("add{suffix}"), "jo", kind, asm)?;
                Ok(())
            }

            Self::Baddis(_) | Self::Baddps(_) | Self::Baddqs(_) => {
                let kind = self.x86_operand_kind();
                let suffix = Self::x86_suffix(kind);
                self.handle_x86_op_branch(&format!("add{suffix}"), "js", kind, asm)?;
                Ok(())
            }

            Self::Baddiz(_) | Self::Baddpz(_) | Self::Baddqz(_) => {
                let kind = self.x86_operand_kind();
                let suffix = Self::x86_suffix(kind);
                self.handle_x86_op_branch(&format!("add{suffix}"), "jz", kind, asm)?;
                Ok(())
            }

            Self::Baddinz(_) | Self::Baddpnz(_) | Self::Baddqnz(_) => {
                let kind = self.x86_operand_kind();
                let suffix = Self::x86_suffix(kind);
                self.handle_x86_op_branch(&format!("add{suffix}"), "jnz", kind, asm)?;
                Ok(())
            }

            Self::Bsubio(_) => self.handle_x86_sub_branch("jo", OperandKind::Int, asm),
            Self::Bsubis(_) => self.handle_x86_sub_branch("js", OperandKind::Int, asm),
            Self::Bsubiz(_) => self.handle_x86_sub_branch("jz", OperandKind::Int, asm),
            Self::Bsubinz(_) => self.handle_x86_sub_branch("jnz", OperandKind::Int, asm),

            Self::Bmulio(_) => self.handle_x86_op_branch("imull", "jo", OperandKind::Int, asm),
            Self::Bmulis(_) => self.handle_x86_op_branch("imull", "js", OperandKind::Int, asm),
            Self::Bmuliz(_) => self.handle_x86_op_branch("imull", "jz", OperandKind::Int, asm),
            Self::Bmulinz(_) => self.handle_x86_op_branch("imull", "jnz", OperandKind::Int, asm),

            Self::Borio(_) => self.handle_x86_op_branch("orl", "jo", OperandKind::Int, asm),
            Self::Boris(_) => self.handle_x86_op_branch("orl", "js", OperandKind::Int, asm),
            Self::Boriz(_) => self.handle_x86_op_branch("orl", "jz", OperandKind::Int, asm),
            Self::Borinz(_) => self.handle_x86_op_branch("orl", "jnz", OperandKind::Int, asm),

            Self::Breakpoint(_) => {
                asm.puts("int $3");
                Ok(())
            }

            Self::Call(Call { target, .. }) => {
                let op = target.x86_call_operand()?;
                asm.format(format_args!("call {op}"));
                Ok(())
            }

            Self::Ret(_) => {
                asm.puts("ret");
                Ok(())
            }

            Self::Cieq(_) | Self::Cbeq(_) | Self::Cpeq(_) | Self::Cqeq(_) => {
                self.handle_x86_set_icmp("sete", self.x86_operand_kind(), asm)
            }

            Self::Cineq(_) | Self::Cbneq(_) | Self::Cpneq(_) | Self::Cqneq(_) => {
                self.handle_x86_set_icmp("setne", self.x86_operand_kind(), asm)
            }

            Self::Cia(_) | Self::Cba(_) | Self::Cpa(_) | Self::Cqa(_) => {
                self.handle_x86_set_icmp("seta", self.x86_operand_kind(), asm)
            }

            Self::Ciaeq(_) | Self::Cbaeq(_) | Self::Cpaeq(_) | Self::Cqaeq(_) => {
                self.handle_x86_set_icmp("setae", self.x86_operand_kind(), asm)
            }

            Self::Cib(_) | Self::Cpb(_) | Self::Cqb(_) | Self::Cbb(_) => {
                self.handle_x86_set_icmp("setb", self.x86_operand_kind(), asm)
            }

            Self::Cibeq(_) | Self::Cpbeq(_) | Self::Cqbeq(_) | Self::Cbbeq(_) => {
                self.handle_x86_set_icmp("setbe", self.x86_operand_kind(), asm)
            }

            Self::Cigt(_) | Self::Cbgt(_) | Self::Cpgt(_) | Self::Cqgt(_) => {
                self.handle_x86_set_icmp("setg", self.x86_operand_kind(), asm)
            }

            Self::Cilt(_) | Self::Cplt(_) | Self::Cqlt(_) | Self::Cblt(_) => {
                self.handle_x86_set_icmp("setl", self.x86_operand_kind(), asm)
            }

            Self::Cigteq(_) | Self::Cbgteq(_) | Self::Cpgteq(_) | Self::Cqgteq(_) => {
                self.handle_x86_set_icmp("setge", self.x86_operand_kind(), asm)
            }

            Self::Cilteq(_) | Self::Cblteq(_) | Self::Cplteq(_) | Self::Cqlteq(_) => {
                self.handle_x86_set_icmp("setle", self.x86_operand_kind(), asm)
            }

            Self::Cfneq(_) | Self::Cdneq(_) => {
                self.handle_x86_fp_compare_set(self.x86_operand_kind(), "setne", false, asm)
            }

            Self::Cfgt(_) | Self::Cdgt(_) => {
                self.handle_x86_fp_compare_set(self.x86_operand_kind(), "seta", false, asm)
            }

            Self::Cfgteq(_) | Self::Cdgteq(_) => {
                self.handle_x86_fp_compare_set(self.x86_operand_kind(), "setae", false, asm)
            }
            Self::Cflt(_) | Self::Cdlt(_) => self.handle_x86_fp_compare_set(
                self.x86_operand_kind(),
                "seta
                ",
                true,
                asm,
            ),

            Self::Cflteq(_) | Self::Cdlteq(_) => {
                self.handle_x86_fp_compare_set(self.x86_operand_kind(), "setae", true, asm)
            }

            Self::Tis(_) | Self::Tps(_) | Self::Tqs(_) | Self::Tbs(_) => {
                self.handle_x86_set_test("sets", self.x86_operand_kind(), asm)
            }

            Self::Tiz(_) | Self::Tpz(_) | Self::Tqz(_) | Self::Tbz(_) => {
                self.handle_x86_set_test("setz", self.x86_operand_kind(), asm)
            }

            Self::Tinz(_) | Self::Tpnz(_) | Self::Tqnz(_) | Self::Tbnz(_) => {
                self.handle_x86_set_test("setnz", self.x86_operand_kind(), asm)
            }

            Self::Peek(_) => self.handle_x86_peek(asm),
            Self::Poke(_) => self.handle_x86_poke(asm),

            Self::Tzcnti(_) | Self::Tzcntq(_) => {
                self.count_trailing_zeros(self.x86_operand_kind(), asm)
            }
            Self::Lzcnti(_) | Self::Lzcntq(_) => {
                self.count_leading_zeros(self.x86_operand_kind(), asm)
            }

            Self::Fii2d(fii2d) => {
                asm.format(format_args!(
                    "movd {lsb}, {dst}",
                    lsb = fii2d.src_lsb.x86_operand(OperandKind::Int)?,
                    dst = fii2d.dst.x86_operand(OperandKind::Double)?
                ));
                asm.format(format_args!(
                    "movsd {msb}, %xmm7",
                    msb = fii2d.src_msb.x86_operand(OperandKind::Int)?
                ));

                asm.puts("psllq $32, %xmm7");

                asm.format(format_args!(
                    "por %xmm7, {dst}",
                    dst = fii2d.dst.x86_operand(OperandKind::Int)?
                ));

                Ok(())
            }

            Self::Fd2ii(fd2ii) => {
                // movd {src}, {dst_lsb}
                // movsd {src}, %xmm7
                // psrlq $32, %xmm7
                // movd %xmm7, {dst_msb}
                asm.format(format_args!(
                    "movd {src}, {dst_lsb}",
                    src = fd2ii.src.x86_operand(OperandKind::Double)?,
                    dst_lsb = fd2ii.dst_lsb.x86_operand(OperandKind::Int)?
                ));
                asm.format(format_args!(
                    "movsd {src}, %xmm7",
                    src = fd2ii.src.x86_operand(OperandKind::Double)?
                ));
                asm.puts("psrlq $32, %xmm7");
                asm.format(format_args!(
                    "movd %xmm7, {dst_msb}",
                    dst_msb = fd2ii.dst_msb.x86_operand(OperandKind::Int)?
                ));

                Ok(())
            }

            Self::Fq2d(fq2d) => {
                asm.format(format_args!(
                    "movq {src}, {dst}",
                    src = fq2d.src.x86_operand(OperandKind::Quad)?,
                    dst = fq2d.dst.x86_operand(OperandKind::Double)?
                ));

                Ok(())
            }

            Self::Fd2q(fd2q) => {
                asm.format(format_args!(
                    "movq {src}, {dst}",
                    src = fd2q.src.x86_operand(OperandKind::Double)?,
                    dst = fd2q.dst.x86_operand(OperandKind::Quad)?
                ));

                Ok(())
            }

            Self::Bo(Bo { target, .. }) => {
                asm.format(format_args!("jo {}", target.asm_label()?));
                Ok(())
            }

            Self::Bs(Bs { target, .. }) => {
                asm.format(format_args!("js {}", target.asm_label()?));
                Ok(())
            }

            Self::Bz(Bz { target, .. }) => {
                asm.format(format_args!("jz {}", target.asm_label()?));
                Ok(())
            }

            Self::Bnz(Bnz { target, .. }) => {
                asm.format(format_args!("jnz {}", target.asm_label()?));
                Ok(())
            }

            Self::Load2ia(_) => {
                return Err(syn::Error::new(
                    self.span(),
                    "load2ia is not implemented for x86",
                ))
            }

            Self::Store2ia(_) => {
                return Err(syn::Error::new(
                    self.span(),
                    "store2ia is not implemented for x86",
                ))
            }

            Self::Emit(emit) => {
                match &emit.raw {
                    Operand::Constant(val) => match &val.value {
                        ConstantValue::String(s) => {
                            asm.puts(&s);
                        }
                        _ => (),
                    },

                    _ => (),
                }

                Ok(())
            }

            Self::Memfence(_) => {
                asm.puts("lock; orl %0, %rsp");
                Ok(())
            }

            Self::Absf(absf) => {
                // movl $0x80000000, %r11
                // movd %r11, ${absf.dst}
                // andnps ${absf.src}, ${absf.dst}

                asm.format(format_args!("movl $0x80000000, %r11d",));
                asm.format(format_args!(
                    "movd %r11d, {dst}",
                    dst = absf.dst.x86_operand(OperandKind::Float)?
                ));
                asm.format(format_args!(
                    "andnps {src}, {dst}",
                    src = absf.src.x86_operand(OperandKind::Float)?,
                    dst = absf.dst.x86_operand(OperandKind::Float)?
                ));

                Ok(())
            }

            Self::Absd(absd) => {
                asm.format(format_args!("movl $0x8000000000000000, %r11d",));
                asm.format(format_args!(
                    "movd %r11d, {dst}",
                    dst = absd.dst.x86_operand(OperandKind::Float)?
                ));
                asm.format(format_args!(
                    "andnps {src}, {dst}",
                    src = absd.src.x86_operand(OperandKind::Float)?,
                    dst = absd.dst.x86_operand(OperandKind::Float)?
                ));

                Ok(())
            }

            Self::Negf(negf) => {
                asm.format(format_args!("movl $0x80000000, %r11d",));
                asm.format(format_args!(
                    "movd %r11d, {dst}",
                    dst = negf.dst.x86_operand(OperandKind::Float)?
                ));
                asm.format(format_args!(
                    "xorps {src}, {dst}",
                    src = negf.src.x86_operand(OperandKind::Float)?,
                    dst = negf.dst.x86_operand(OperandKind::Float)?
                ));

                Ok(())
            }

            Self::Negd(negd) => {
                asm.format(format_args!("movl $0x8000000000000000, %r11d",));
                asm.format(format_args!(
                    "movd %r11d, {dst}",
                    dst = negd.dst.x86_operand(OperandKind::Float)?
                ));
                asm.format(format_args!(
                    "xorpd {src}, {dst}",
                    src = negd.src.x86_operand(OperandKind::Float)?,
                    dst = negd.dst.x86_operand(OperandKind::Float)?
                ));

                Ok(())
            }

            Self::Cfeq(_) | Self::Cdeq(_) => {
                self.handle_x86_fp_compare_set(self.x86_operand_kind(), "eq", false, asm)
            }

            Self::Cfnequn(_) | Self::Cdnequn(_) => {
                self.handle_x86_fp_compare_set(self.x86_operand_kind(), "nequn", false, asm)
            }

            Self::Fi2f(fi2f) => {
                asm.format(format_args!(
                    "movd {src}, {dst}",
                    src = fi2f.src.x86_operand(OperandKind::Int)?,
                    dst = fi2f.dst.x86_operand(OperandKind::Float)?
                ));

                Ok(())
            }

            Self::Ff2i(ff2i) => {
                asm.format(format_args!(
                    "cvttss2si {src}, {dst}",
                    src = ff2i.src.x86_operand(OperandKind::Float)?,
                    dst = ff2i.dst.x86_operand(OperandKind::Int)?
                ));

                Ok(())
            }

            Self::TlsLoadp(ld) => {
                let mem = if let Some(immediate) = ld.src.try_immediate() {
                    format!("%gs:{}", immediate.wrapping_mul(size_of::<usize>() as _))
                } else {
                    format!(
                        "%gs:({src}, $8)",
                        src = ld.src.x86_operand(OperandKind::Ptr)?
                    )
                };

                asm.format(format_args!(
                    "movq {mem}, {dst}",
                    mem = mem,
                    dst = ld.dst.x86_operand(OperandKind::Ptr)?
                ));

                Ok(())
            }

            Self::TlsStorep(st) => {
                let mem = if let Some(immediate) = st.dst.try_immediate() {
                    format!("%gs:{}", immediate.wrapping_mul(size_of::<usize>() as _))
                } else {
                    format!(
                        "%gs:({dst}, $8)",
                        dst = st.dst.x86_operand(OperandKind::Ptr)?
                    )
                };

                asm.format(format_args!(
                    "movq {src}, {mem}",
                    src = st.src.x86_operand(OperandKind::Ptr)?,
                    mem = mem
                ));

                Ok(())
            }
        }
    }
}
