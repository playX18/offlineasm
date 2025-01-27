use std::cell::LazyCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::sync::LazyLock;

use proc_macro2::Span;
use syn::Ident;

use crate::instructions::*;
use crate::operands::*;
use crate::registers::*;
use crate::stmt::*;

use super::is_setting_set;
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
                (&["ft5", "fa5"], "xmm5"),
                (&["ft6", "fa6"], "xmm6"),
                (&["ft7", "fa7"], "xmm7"),
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

    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
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
                    return Err(syn::Error::new(self.span, &format!("address offset was not resolved: {}", self)));
                };

                let base = base.x86_operand(address_kind)?;

                Ok(offset_register(offset as i64, base))
            }
            AddressKind::Absolute { value } => {
                Ok(format!("${value}"))
            }
            AddressKind::BaseIndex { base, index, scale, offset } => {
                
                let Some(offset) = offset.try_immediate() else {
                    return Err(syn::Error::new(self.span, &format!("address offset was not resolved: {}", self)));
                };

                let Some(scale) = scale.try_immediate() else {
                    return Err(syn::Error::new(self.span, &format!("address scale was not resolved: {}", self)));
                };

                let base = base.x86_operand(address_kind)?;
                let index = index.x86_operand(address_kind)?;

                

                Ok(
                    format!(
                        "{offset}({base}, {index}, {scale})"
                    )
                )
            }
        }
    }

    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        let _ = kind;
        self.x86_address_operand(OperandKind::Ptr)
    }

    pub fn x86_call_operand(&self) -> syn::Result<String> {
        Ok(format!("{CALL_PREFIX}{}", self.x86_operand(OperandKind::Ptr)?))
    }
}

impl LabelReference {
    pub fn x86_operand(&self, _: OperandKind) -> syn::Result<String> {
        Ok(self.label.name().to_string())
    }
}

impl Operand {
    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        match self {
            Operand::Address(addr) => addr.x86_operand(kind),
            Operand::Constant(c) => c.x86_operand(),
            Operand::GPRegister(r) => r.x86_operand(kind),
            Operand::FPRegister(r) => r.x86_operand(kind),
            _ => todo!()
        }
    }
}

impl Instruction {
    pub fn lower_x86(&self, asm: &mut Assembler) -> syn::Result<()> {
        todo!()
    }
}
