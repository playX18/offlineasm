// GPR conventions
// On x86-64 (windows and non-windows)
//
// rax => t0,     r0
// rdi => t6, a0
// rsi => t1, a1
// rdx => t2, a2, r1
// rcx => t3, a3
//  r8 => t4, a4
//  r9 => t7, a5
// r10 => t5
// rbx =>             csr0 (callee-save, wasmInstance)
// r12 =>             csr1 (callee-save, metadataTable)
// r13 =>             csr2 (callee-save, PB)
// r14 =>             csr3 (callee-save, tagTypeNumber)
// r15 =>             csr4 (callee-save, tagMask)
// rsp => sp
// rbp => cfr
// r11 =>                  (scratch)

use proc_macro2::Span;
use std::sync::LazyLock;
use syn::Ident;

use crate::{asm::Assembler, ast::*, id, instructions::is_power_of_two, is_windows, punc_from_vec};

fn register(name: impl ToString) -> String {
    let name = name.to_string();
    format!("%{}", name)
}

fn offset_register(off: impl ToString, register: impl ToString) -> String {
    format!(
        "{off}({register})",
        off = off.to_string(),
        register = register.to_string()
    )
}

fn call_prefix() -> &'static str {
    "*"
}

fn constant(c: impl ToString) -> String {
    format!("${}", c.to_string())
}

fn constant0x(c: impl ToString) -> String {
    format!("0x{}", c.to_string())
}

fn constant0b(c: impl ToString) -> String {
    format!("0b{}", c.to_string())
}
#[derive(Clone)]
pub struct SpecialRegister {
    name: Ident,
}

unsafe impl Sync for SpecialRegister {}
unsafe impl Send for SpecialRegister {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperandKind {
    Byte,
    Half,
    Int,
    Ptr,
    Quad,
    Float,
    Double,
    Vector,
}

impl SpecialRegister {
    pub fn new(name: &Ident) -> Self {
        Self { name: name.clone() }
    }

    pub fn x86_operand(&self, kind: OperandKind) -> String {
        match kind {
            OperandKind::Half => register(&format!("{}w", self.name)),
            OperandKind::Int => register(&format!("{}d", self.name)),
            OperandKind::Ptr => register(&self.name),
            OperandKind::Quad => register(&self.name),
            _ => unreachable!("special operand for {} and {:?}", self.name, kind),
        }
    }

    pub fn x86_call_operand(&self) -> String {
        format!("*{}", self.x86_operand(OperandKind::Ptr))
    }
}

static X86_SCRATCH_REGISTER: LazyLock<SpecialRegister> =
    LazyLock::new(|| SpecialRegister::new(&Ident::new("r11", Span::call_site())));

pub fn x86_gpr_name(name: &str, kind: OperandKind) -> syn::Result<String> {
    let name8;
    let name16;

    match name {
        "eax" | "ebx" | "ecx" | "edx" => {
            name8 = format!("{}l", name.chars().nth(1).unwrap());
            name16 = &name[1..3];
        }
        "esi" | "edi" | "ebp" | "esp" => {
            name16 = &name[1..3];
            name8 = format!("{}l", name16);
        }
        "r8" | "r9" | "r10" | "r12" | "r13" | "r14" | "r15" => match kind {
            OperandKind::Byte => return Ok(register(&format!("{}b", name))),
            OperandKind::Half => return Ok(register(&format!("{}w", name))),
            OperandKind::Int => return Ok(register(&format!("{}d", name))),
            OperandKind::Ptr | OperandKind::Quad => return Ok(register(name)),
            _ => {
                return Err(syn::Error::new(
                    proc_macro2::Span::call_site(),
                    format!("invalid operand kind for GPR: {:?}", kind),
                ))
            }
        },

        _ => {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                format!("bad GPR name {}", name),
            ))
        }
    }
    match kind {
        OperandKind::Byte => Ok(name8),
        OperandKind::Half => Ok(name16.to_string()),
        OperandKind::Int => Ok(register(&format!("e{}", name16))),
        OperandKind::Ptr | OperandKind::Quad => Ok(register(&format!("r{}", name16))),
        _ => unreachable!("invalid operand kind for GPR: {:?}", kind),
    }
}

impl RegisterId {
    pub fn supports_8bit_on_x86(&self) -> syn::Result<bool> {
        match self.x86_gpr()?.as_str() {
            "eax" | "ebx" | "ecx" | "edx" | "edi" | "esi" | "ebp" | "esp" => Ok(true),
            "r8" | "r9" | "r10" | "r12" | "r13" | "r14" | "r15" => Ok(false),
            _ => Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                format!("unsupported GPR for 8-bit check: {}", self.x86_gpr()?),
            )),
        }
    }

    pub fn x86_gpr(&self) -> syn::Result<String> {
        let name = self.name.to_string();
        match name.as_str() {
            "t0" | "r0" | "ws0" => Ok("eax".to_string()),
            "t6" | "a0" | "wa0" => Ok("edi".to_string()),
            "t1" | "a1" | "wa1" => Ok("esi".to_string()),
            "t2" | "r1" | "a2" | "wa2" => Ok("edx".to_string()),
            "t3" | "a3" | "wa3" => Ok("ecx".to_string()),
            "t4" | "a4" | "wa4" => Ok("r8".to_string()),
            "t5" | "ws1" => Ok("r10".to_string()),
            "t7" | "a5" | "wa5" => Ok("r9".to_string()),
            "csr0" => Ok("ebx".to_string()),
            "csr1" => Ok("r12".to_string()),
            "csr2" => Ok("r13".to_string()),
            "csr3" => Ok("r14".to_string()),
            "csr4" => Ok("r15".to_string()),
            "csr5" | "csr6" => Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                format!("cannot use register {} on X86-64", self.name),
            )),
            "cfr" => Ok("ebp".to_string()),
            "sp" => Ok("esp".to_string()),
            _ => Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                format!("cannot use register {} on X86", self.name),
            )),
        }
    }

    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        x86_gpr_name(&self.x86_gpr()?, kind)
    }

    pub fn x86_call_operand(&self) -> syn::Result<String> {
        Ok(format!("*{}", self.x86_operand(OperandKind::Ptr)?))
    }
}

impl FPRegisterId {
    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        if !matches!(
            kind,
            OperandKind::Float | OperandKind::Double | OperandKind::Vector
        ) {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                format!("invalid operand kind for FP register: {:?}", kind),
            ));
        }
        let name = self.name.to_string();
        let reg = match name.as_str() {
            "ft0" | "fa0" | "fr" | "wfa0" => "xmm0",
            "ft1" | "fa1" | "wfa1" => "xmm1",
            "ft2" | "fa2" | "wfa2" => "xmm2",
            "ft3" | "fa3" | "wfa3" => "xmm3",
            "ft4" | "wfa4" => "xmm4",
            "ft5" | "wfa5" => "xmm5",
            "wfa6" => "xmm6",
            "wfa7" => "xmm7",
            _ => {
                return Err(syn::Error::new(
                    proc_macro2::Span::call_site(),
                    format!("bad register {} for X86", self.name),
                ))
            }
        };

        Ok(reg.to_string())
    }

    pub fn x86_call_operand(&self, kind: OperandKind) -> syn::Result<String> {
        Ok(format!("*{}", self.x86_operand(kind)?))
    }
}

impl VecRegisterId {
    pub fn x86_operand(&self, _kind: OperandKind) -> syn::Result<String> {
        let name = self.name.to_string();
        let reg = match name.as_str() {
            "v0" | "v0_b" | "v0_h" | "v0_i" | "v0_q" => "xmm0",
            "v1" | "v1_b" | "v1_h" | "v1_i" | "v1_q" => "xmm1",
            "v2" | "v2_b" | "v2_h" | "v2_i" | "v2_q" => "xmm2",
            "v3" | "v3_b" | "v3_h" | "v3_i" | "v3_q" => "xmm3",
            "v4" | "v4_b" | "v4_h" | "v4_i" | "v4_q" => "xmm4",
            "v5" | "v5_b" | "v5_h" | "v5_i" | "v5_q" => "xmm5",
            "v6" | "v6_b" | "v6_h" | "v6_i" | "v6_q" => "xmm6",
            "v7" | "v7_b" | "v7_h" | "v7_i" | "v7_q" => "xmm7",
            _ => {
                return Err(syn::Error::new(
                    proc_macro2::Span::call_site(),
                    format!("bad register name {} for X86", self.name),
                ))
            }
        };

        Ok(reg.to_string())
    }
}

impl Immediate {
    pub fn valid_x86_immediate(&self) -> bool {
        self.value >= -0x80000000 && self.value <= 0x7fffffff
    }

    pub fn x86_operand(&self, _kind: OperandKind) -> syn::Result<String> {
        Ok(format!("#{}", self.value))
    }

    pub fn x86_call_operand(&self, _kind: OperandKind) -> syn::Result<String> {
        Ok(self.value.to_string())
    }
}

impl Address {
    pub fn supports_8bit_on_x86(&self) -> bool {
        true
    }

    pub fn x86_address_operand(&self, address_kind: OperandKind) -> syn::Result<String> {
        let base = self.base.x86_operand(address_kind)?;
        Ok(format!("{}({})", self.offset, base))
    }

    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        Ok(self.x86_address_operand(OperandKind::Ptr)?)
    }

    pub fn x86_call_operand(&self, kind: OperandKind) -> syn::Result<String> {
        Ok(format!("*{}", self.x86_operand(kind)?))
    }
}

impl BaseIndex {
    pub fn supports_8bit_on_x86(&self) -> bool {
        true
    }

    pub fn x86_address_operand(&self, address_kind: OperandKind) -> syn::Result<String> {
        let base = self.base.x86_operand(address_kind)?;
        let index = self.index.x86_operand(address_kind)?;
        Ok(format!(
            "{}({}, {}, {})",
            self.offset, base, index, self.scale
        ))
    }

    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        self.x86_address_operand(OperandKind::Ptr)
    }

    pub fn x86_call_operand(&self, kind: OperandKind) -> syn::Result<String> {
        Ok(format!("*{}", self.x86_operand(kind)?))
    }
}

impl AbsoluteAddress {
    pub fn supports_8bit_on_x86(&self) -> bool {
        true
    }

    pub fn x86_address_operand(&self, address_kind: OperandKind) -> syn::Result<String> {
        Ok(self.base.to_string())
    }

    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        Ok(self.base.to_string())
    }

    pub fn x86_call_operand(&self, kind: OperandKind) -> syn::Result<String> {
        Ok(format!("*{}", self.base.to_string()))
    }
}

impl LabelReference {
    pub fn asm_label(&self) -> String {
        match &self.label {
            LabelMapping::Global(glob) => {
                if let Some(id) = glob.get_sym_id() {
                    return format!("{{_sym_{}}}", id);
                }
            }
            _ => (),
        }
        self.label.name().to_string()
    }

    pub fn x86_call_operand(&self, kind: OperandKind) -> syn::Result<String> {
        match &self.label {
            LabelMapping::Global(glob) => {
                if let Some(id) = glob.get_sym_id() {
                    return Ok(format!("{{ _sym_{} }}", id));
                }
            }
            _ => (),
        }
        Ok(format!(" {} ", self.label.name().to_string()))
    }

    pub fn x86_load_operand(
        &self,
        asm: &mut Assembler,
        kind: OperandKind,
        dst: &Node,
    ) -> syn::Result<String> {
        if !is_windows() {
            asm.puts(&format!(
                "movq {}@GOTPCREL(%rip), {}",
                self.x86_call_operand(kind)?,
                dst.x86_operand(kind)?
            ));
        } else {
            asm.puts(&format!(
                "lea {}@GOTPCREL(%rip), {}",
                self.x86_call_operand(kind)?,
                dst.x86_operand(kind)?
            ));
        }

        Ok(offset_register(
            self.offset.to_string(),
            dst.x86_operand(kind)?,
        ))
    }
}

impl LocalLabel {
    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        Ok(format!("{}", self.name.to_string()))
    }

    pub fn x86_call_operand(&self, kind: OperandKind) -> syn::Result<String> {
        Ok(format!("{}", self.name.to_string()))
    }
}

impl LocalLabelReference {
    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        Ok(format!("{}", self.label.name.to_string()))
    }

    pub fn x86_call_operand(&self, kind: OperandKind) -> syn::Result<String> {
        Ok(format!("{}", self.label.name.to_string()))
    }
}

fn order_operands(operands: &[String]) -> String {
    operands.join(" , ").to_string()
}

impl Instruction {
    pub fn x86_operands(&self, kinds: &[OperandKind]) -> syn::Result<String> {
        if kinds.len() != self.operands.len() {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                format!(
                    "expected {} operands, got {}",
                    kinds.len(),
                    self.operands.len()
                ),
            ));
        }

        let mut result = Vec::new();

        for (i, kind) in kinds.iter().copied().enumerate() {
            result.push(self.operands[i].x86_operand(kind)?);
        }

        Ok(result.join(",").to_string())
    }

    pub fn x86_load_operands(
        &self,
        asm: &mut Assembler,
        src_kind: OperandKind,
        dst_kind: OperandKind,
    ) -> syn::Result<String> {
        Ok(order_operands(&[
            self.operands[0].x86_load_operand(asm, src_kind, &self.operands[1])?,
            self.operands[1].x86_operand(dst_kind)?,
        ]))
    }

    pub fn x86_suffix(kind: OperandKind) -> &'static str {
        match kind {
            OperandKind::Byte => "b",
            OperandKind::Half => "w",
            OperandKind::Int => "l",
            OperandKind::Ptr => "q",
            OperandKind::Quad => "q",
            OperandKind::Float => "ss",
            OperandKind::Double => "sd",
            OperandKind::Vector => "v",
        }
    }

    pub fn x86_bytes(kind: OperandKind) -> usize {
        match kind {
            OperandKind::Byte => 1,
            OperandKind::Half => 2,
            OperandKind::Int => 4,
            OperandKind::Ptr | OperandKind::Quad => 8,
            _ => unreachable!("bytes for {:?}", kind),
        }
    }

    pub fn emit_x86_lea(
        asm: &mut Assembler,
        src: &Node,
        dst: &Node,
        kind: OperandKind,
    ) -> syn::Result<()> {
        if let Node::LabelReference(lref) = src {
            if !is_windows() {
                asm.puts(&format!(
                    "movq {}@GOTPCREL(%rip), {}",
                    lref.asm_label(),
                    dst.x86_operand(OperandKind::Ptr)?
                ));
            } else {
                asm.puts(&format!(
                    "lea {}@GOTPCREL(%rip), {}",
                    lref.asm_label(),
                    dst.x86_operand(OperandKind::Ptr)?
                ));
            }

            if lref.offset != 0 {
                asm.puts(&format!(
                    "add{suffix} {operands}",
                    suffix = Self::x86_suffix(kind),
                    operands = order_operands(&[constant(lref.offset), dst.x86_operand(kind)?])
                ))
            }
        } else {
            asm.puts(&format!(
                "lea{suffix} {operands}",
                suffix = Self::x86_suffix(kind),
                operands = order_operands(&[src.x86_operand(kind)?, dst.x86_operand(kind)?])
            ));
        }

        Ok(())
    }

    pub fn handle_x86_op_with_n_operands(
        &self,
        asm: &mut Assembler,
        opcode: &str,
        kind: OperandKind,
        num_operands: usize,
    ) -> syn::Result<()> {
        if num_operands == 3 {
            if self.operands[0] == self.operands[2] {
                asm.puts(&format!(
                    "{opcode} {operands}",
                    operands = order_operands(&[
                        self.operands[1].x86_operand(kind)?,
                        self.operands[2].x86_operand(kind)?
                    ])
                ));
            } else if self.operands[1] == self.operands[2] {
                asm.puts(&format!(
                    "{opcode} {operands}",
                    operands = order_operands(&[
                        self.operands[0].x86_operand(kind)?,
                        self.operands[2].x86_operand(kind)?
                    ])
                ));
            } else {
                asm.puts(&format!(
                    "mov{suffix} {operands}",
                    suffix = Self::x86_suffix(kind),
                    operands = order_operands(&[
                        self.operands[0].x86_operand(kind)?,
                        self.operands[2].x86_operand(kind)?
                    ])
                ));

                asm.puts(&format!(
                    "{opcode} {operands}",
                    operands = order_operands(&[
                        self.operands[1].x86_operand(kind)?,
                        self.operands[2].x86_operand(kind)?
                    ])
                ));
            }
        } else {
            // 2 operands
            assert!(num_operands == 2);

            asm.puts(&format!(
                "{opcode} {operands}",
                operands = order_operands(&[
                    self.operands[0].x86_operand(kind)?,
                    self.operands[1].x86_operand(kind)?
                ])
            ));
        }

        Ok(())
    }

    pub fn handle_x86_op(
        &self,
        asm: &mut Assembler,
        opcode: &str,
        kind: OperandKind,
    ) -> syn::Result<()> {
        self.handle_x86_op_with_n_operands(asm, opcode, kind, self.operands.len())
    }

    pub fn handle_x86_shift(
        &self,
        asm: &mut Assembler,
        opcode: &str,
        kind: OperandKind,
    ) -> syn::Result<()> {
        if matches!(self.operands[0], Node::Immediate(_))
            || self.operands[0].try_x86_gpr() == Some("ecx".to_string())
        {
            asm.puts(&format!(
                "{opcode} {operands}",
                operands = order_operands(&[
                    self.operands[0].x86_operand(OperandKind::Byte)?,
                    self.operands[1].x86_operand(kind)?
                ])
            ));
        } else {
            asm.puts(&format!(
                "xchg{suffix} {operands}",
                suffix = Self::x86_suffix(OperandKind::Ptr),
                operands = order_operands(&[
                    self.operands[0].x86_operand(OperandKind::Ptr)?,
                    x86_gpr_name("ecx", OperandKind::Ptr)?
                ])
            ));

            asm.puts(&format!(
                "{opcode} {operands}",
                operands = order_operands(&[register("cl"), self.operands[1].x86_operand(kind)?])
            ));

            asm.puts(&format!(
                "xchg{suffix} {operands}",
                suffix = Self::x86_suffix(OperandKind::Ptr),
                operands = order_operands(&[
                    self.operands[0].x86_operand(OperandKind::Ptr)?,
                    x86_gpr_name("ecx", OperandKind::Ptr)?
                ])
            ));
        }
        Ok(())
    }

    pub fn handle_x86_fp_branch(
        &self,
        asm: &mut Assembler,
        kind: OperandKind,
        branch_opcode: &str,
        normal: bool,
    ) -> syn::Result<()> {
        if normal {
            asm.puts(&format!(
                "ucomi{} {}",
                Self::x86_suffix(kind),
                order_operands(&[
                    self.operands[1].x86_operand(OperandKind::Double)?,
                    self.operands[0].x86_operand(OperandKind::Double)?
                ])
            ));
        } else {
            asm.puts(&format!(
                "ucomi{} {}",
                Self::x86_suffix(kind),
                order_operands(&[
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Double)?
                ])
            ));
        }
        asm.puts(&format!(
            "{} {}",
            branch_opcode,
            self.operands[2].asm_label()?
        ));
        Ok(())
    }

    pub fn handle_x86_int_compare(
        &self,
        asm: &mut Assembler,
        opcode_suffix: &str,
        kind: OperandKind,
    ) -> syn::Result<()> {
        if self.operands[0].is_immediate_zero()
            && self.operands[1].is_register_id()
            && (opcode_suffix == "e" || opcode_suffix == "ne")
        {
            asm.puts(&format!(
                "test{} {}",
                Self::x86_suffix(kind),
                order_operands(&[
                    self.operands[1].x86_operand(kind)?,
                    self.operands[1].x86_operand(kind)?
                ])
            ));
        } else if self.operands[1].is_immediate_zero()
            && self.operands[0].is_register_id()
            && (opcode_suffix == "e" || opcode_suffix == "ne")
        {
            asm.puts(&format!(
                "test{} {}",
                Self::x86_suffix(kind),
                order_operands(&[
                    self.operands[0].x86_operand(kind)?,
                    self.operands[0].x86_operand(kind)?
                ])
            ));
        } else {
            asm.puts(&format!(
                "cmp{} {}",
                Self::x86_suffix(kind),
                order_operands(&[
                    self.operands[1].x86_operand(kind)?,
                    self.operands[0].x86_operand(kind)?
                ])
            ));
        }
        Ok(())
    }

    pub fn handle_x86_int_branch(
        &self,
        asm: &mut Assembler,
        branch_opcode: &str,
        kind: OperandKind,
    ) -> syn::Result<()> {
        let opcode_suffix = &branch_opcode[1..branch_opcode.len() - 1];
        self.handle_x86_int_compare(asm, opcode_suffix, kind)?;
        asm.puts(&format!(
            "{} {}",
            branch_opcode,
            self.operands[2].asm_label()?
        ));
        Ok(())
    }

    pub fn handle_x86_test(&self, asm: &mut Assembler, kind: OperandKind) -> syn::Result<()> {
        let value = &self.operands[0];
        let mask = match self.operands.len() {
            2 => Node::Immediate(Immediate { value: -1 }),
            3 => self.operands[1].clone(),
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("Expected 2 or 3 operands, but got {}", self.operands.len()),
                ))
            }
        };

        if mask.is_immediate() && mask.immediate_value()? == -1 {
            if value.is_register_id() {
                asm.puts(&format!(
                    "test{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[value.x86_operand(kind)?, value.x86_operand(kind)?])
                ));
            } else {
                asm.puts(&format!(
                    "cmp{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        Node::Immediate(Immediate { value: 0 }).x86_operand(kind)?,
                        value.x86_operand(kind)?
                    ])
                ));
            }
        } else {
            asm.puts(&format!(
                "test{} {}",
                Self::x86_suffix(kind),
                order_operands(&[mask.x86_operand(kind)?, value.x86_operand(kind)?])
            ));
        }
        Ok(())
    }

    pub fn handle_x86_branch_test(
        &self,
        asm: &mut Assembler,
        opcode: &str,
        kind: OperandKind,
    ) -> syn::Result<()> {
        self.handle_x86_test(asm, kind)?;
        asm.puts(&format!(
            "{} {}",
            opcode,
            self.operands.last().unwrap().asm_label()?
        ));
        Ok(())
    }

    pub fn handle_x86_set(
        asm: &mut Assembler,
        set_opcode: &str,
        operand: &Node,
    ) -> syn::Result<()> {
        if operand.supports_8bit_on_x86()? {
            asm.puts(&format!(
                "{} {}",
                set_opcode,
                operand.x86_operand(OperandKind::Byte)?
            ));
            asm.puts(&format!(
                "movzbl {}",
                order_operands(&[
                    operand.x86_operand(OperandKind::Byte)?,
                    operand.x86_operand(OperandKind::Int)?
                ])
            ));
        } else {
            let ax = Node::RegisterId(RegisterId::for_name_str("r0"));
            asm.puts(&format!(
                "xchg{} {}",
                Self::x86_suffix(OperandKind::Ptr),
                order_operands(&[
                    operand.x86_operand(OperandKind::Ptr)?,
                    ax.x86_operand(OperandKind::Ptr)?
                ])
            ));
            asm.puts(&format!(
                "{} {}",
                set_opcode,
                ax.x86_operand(OperandKind::Byte)?
            ));
            asm.puts(&format!(
                "movzbl {}",
                order_operands(&[
                    ax.x86_operand(OperandKind::Byte)?,
                    ax.x86_operand(OperandKind::Int)?
                ])
            ));
            asm.puts(&format!(
                "xchg{} {}",
                Self::x86_suffix(OperandKind::Ptr),
                order_operands(&[
                    operand.x86_operand(OperandKind::Ptr)?,
                    ax.x86_operand(OperandKind::Ptr)?
                ])
            ));
        }
        Ok(())
    }

    pub fn handle_x86_set_test(
        &self,
        asm: &mut Assembler,
        set_opcode: &str,
        kind: OperandKind,
    ) -> syn::Result<()> {
        self.handle_x86_test(asm, kind)?;
        Self::handle_x86_set(asm, set_opcode, self.operands.last().unwrap())
    }

    pub fn handle_x86_op_branch(
        &self,
        asm: &mut Assembler,
        opcode: &str,
        branch_opcode: &str,
        kind: OperandKind,
    ) -> syn::Result<()> {
        self.handle_x86_op_with_n_operands(asm, opcode, kind, self.operands.len() - 1)?;
        let jump_target = match self.operands.len() {
            4 => &self.operands[3],
            3 => &self.operands[2],
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "invalid number of operands",
                ))
            }
        };
        asm.puts(&format!("{} {}", branch_opcode, jump_target.asm_label()?));
        Ok(())
    }

    pub fn handle_x86_sub_branch(
        &self,
        asm: &mut Assembler,
        branch_opcode: &str,
        kind: OperandKind,
    ) -> syn::Result<()> {
        if self.operands.len() == 4 && self.operands[1] == self.operands[2] {
            asm.puts(&format!(
                "neg{} {}",
                Self::x86_suffix(kind),
                self.operands[2].x86_operand(kind)?
            ));
            asm.puts(&format!(
                "add{} {}",
                Self::x86_suffix(kind),
                order_operands(&[
                    self.operands[0].x86_operand(kind)?,
                    self.operands[2].x86_operand(kind)?
                ])
            ));
        } else {
            self.handle_x86_op_with_n_operands(
                asm,
                &format!("sub{}", Self::x86_suffix(kind)),
                kind,
                self.operands.len() - 1,
            )?;
        }

        let jump_target = match self.operands.len() {
            4 => &self.operands[3],
            3 => &self.operands[2],
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "invalid number of operands",
                ))
            }
        };
        asm.puts(&format!("{} {}", branch_opcode, jump_target.asm_label()?));
        Ok(())
    }

    pub fn handle_x86_int_compare_set(
        &self,
        asm: &mut Assembler,
        set_opcode: &str,
        kind: OperandKind,
    ) -> syn::Result<()> {
        self.handle_x86_int_compare(asm, &set_opcode[3..set_opcode.len() - 1], kind)?;
        Self::handle_x86_set(asm, set_opcode, &self.operands[2])
    }

    pub fn handle_x86_fp_compare_set(
        &self,
        asm: &mut Assembler,
        kind: OperandKind,
        set_opcode: &str,
        normal_order: bool,
    ) -> syn::Result<()> {
        let is_special = set_opcode == "nequn" || set_opcode == "eq";

        let left = &self.operands[0];
        let right = &self.operands[1];
        let target = &self.operands[2];

        let cmp = |asm: &mut Assembler, lhs: &Node, rhs: &Node| -> syn::Result<()> {
            asm.puts(&format!(
                "ucomi{} {}",
                Self::x86_suffix(kind),
                order_operands(&[
                    lhs.x86_operand(OperandKind::Double)?,
                    rhs.x86_operand(OperandKind::Double)?
                ])
            ));
            Ok(())
        };

        if is_special {
            match set_opcode {
                "eq" => {
                    if left == right {
                        cmp(asm, left, right)?;
                        Self::handle_x86_set(asm, "setnp", target)?;
                        return Ok(());
                    }

                    let is_unordered = LocalLabel::unique("is_unordered");
                    asm.puts(&format!(
                        "mov{suffix} {operands}",
                        suffix = Self::x86_suffix(kind),
                        operands =
                            order_operands(&[constant(0), target.x86_operand(OperandKind::Quad)?])
                    ));
                    cmp(asm, left, right)?;
                    asm.puts(&format!("jp {}", is_unordered.name));
                    Self::handle_x86_set(asm, "setne", target)?;
                    is_unordered.lower(asm)?;
                    return Ok(());
                }

                "nequn" => {
                    if left == right {
                        cmp(asm, left, right)?;
                        Self::handle_x86_set(asm, "setp", target)?;
                        return Ok(());
                    }

                    let is_unordered = LocalLabel::unique("is_unordered");
                    asm.puts(&format!(
                        "mov{suffix} {operands}",
                        suffix = Self::x86_suffix(kind),
                        operands =
                            order_operands(&[constant(0), target.x86_operand(OperandKind::Quad)?])
                    ));
                    cmp(asm, left, right)?;
                    asm.puts(&format!("jp {}", is_unordered.name));
                    Self::handle_x86_set(asm, "sete", target)?;
                    is_unordered.lower(asm)?;
                    return Ok(());
                }

                _ => unreachable!(),
            }
        }

        if normal_order {
            cmp(asm, right, left)?;
        } else {
            cmp(asm, left, right)?;
        }

        Self::handle_x86_set(asm, set_opcode, target)
    }

    pub fn handle_x86_add(&self, asm: &mut Assembler, kind: OperandKind) -> syn::Result<()> {
        if self.operands.len() == 3 && self.operands[1] == self.operands[2] {
            if !self.operands[0].is_immediate_zero() {
                asm.puts(&format!(
                    "add{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        self.operands[0].x86_operand(kind)?,
                        self.operands[2].x86_operand(kind)?
                    ])
                ));
            }
        } else if self.operands.len() == 3 && self.operands[0].is_immediate() {
            if !self.operands[1].is_register_id() || !self.operands[2].is_register_id() {
                return Err(syn::Error::new(Span::call_site(), "invalid operand types"));
            }
            if self.operands[0].is_immediate_zero() {
                if self.operands[1] != self.operands[2] {
                    asm.puts(&format!(
                        "mov{} {}",
                        Self::x86_suffix(kind),
                        order_operands(&[
                            self.operands[1].x86_operand(kind)?,
                            self.operands[2].x86_operand(kind)?
                        ])
                    ));
                }
            } else {
                asm.puts(&format!(
                    "lea{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        offset_register(
                            self.operands[0].immediate_value()?,
                            self.operands[1].x86_operand(kind)?
                        ),
                        self.operands[2].x86_operand(kind)?
                    ])
                ));
            }
        } else if self.operands.len() == 3 && self.operands[0].is_register_id() {
            if !self.operands[1].is_register_id() || !self.operands[2].is_register_id() {
                return Err(syn::Error::new(Span::call_site(), "invalid operand types"));
            }
            if self.operands[0] == self.operands[2] {
                asm.puts(&format!(
                    "add{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        self.operands[1].x86_operand(kind)?,
                        self.operands[2].x86_operand(kind)?
                    ])
                ));
            } else {
                asm.puts(&format!(
                    "lea{} ({}, {}), {}",
                    Self::x86_suffix(kind),
                    self.operands[0].x86_operand(kind)?,
                    self.operands[1].x86_operand(kind)?,
                    self.operands[2].x86_operand(kind)?
                ));
            }
        } else {
            if !self.operands[0].is_immediate_zero() {
                asm.puts(&format!(
                    "add{} {}",
                    Self::x86_suffix(kind),
                    self.x86_operands(&[kind, kind])?
                ));
            }
        }
        Ok(())
    }

    fn handle_x86_sub(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        if self.operands.len() == 3 {
            if self.operands[1].is_immediate_zero() {
                if !self.operands[0].is_register_id() || !self.operands[2].is_register_id() {
                    return Err(syn::Error::new(Span::call_site(), "invalid operand types"));
                }
                if self.operands[0] != self.operands[2] {
                    asm.puts(&format!(
                        "mov{} {}",
                        Self::x86_suffix(kind),
                        order_operands(&[
                            self.operands[0].x86_operand(kind)?,
                            self.operands[2].x86_operand(kind)?
                        ])
                    ));
                }
                return Ok(());
            }
            if self.operands[1] == self.operands[2] {
                asm.puts(&format!(
                    "neg{} {}",
                    Self::x86_suffix(kind),
                    self.operands[2].x86_operand(kind)?
                ));
                if !self.operands[0].is_immediate_zero() {
                    asm.puts(&format!(
                        "add{} {}",
                        Self::x86_suffix(kind),
                        order_operands(&[
                            self.operands[0].x86_operand(kind)?,
                            self.operands[2].x86_operand(kind)?
                        ])
                    ));
                }
                return Ok(());
            }
        }

        if self.operands.len() == 2 {
            if self.operands[0].is_immediate_zero() {
                return Ok(());
            }
        }

        self.handle_x86_op(asm, &format!("sub{}", Self::x86_suffix(kind)), kind)
    }

    fn handle_x86_mul(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        if self.operands.len() == 3 && self.operands[0].is_immediate() {
            asm.puts(&format!(
                "imul{} {}",
                Self::x86_suffix(kind),
                self.x86_operands(&[kind, kind, kind])?
            ));
            return Ok(());
        }

        if self.operands.len() == 2 && self.operands[0].is_immediate() {
            if let Node::Immediate(imm) = &self.operands[0] {
                let value = imm.value;
                if value > 0 && is_power_of_two(value) {
                    let shift = value.trailing_zeros();
                    asm.puts(&format!(
                        "sal{} {}",
                        Self::x86_suffix(kind),
                        order_operands(&[
                            Node::Immediate(Immediate { value: shift as _ }).x86_operand(kind)?,
                            self.operands[1].x86_operand(kind)?
                        ])
                    ));
                    return Ok(());
                }
            }
        }

        self.handle_x86_op(asm, &format!("imul{}", Self::x86_suffix(kind)), kind)
    }

    fn handle_x86_add_fp(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        match self.operands.len() {
            2 => {
                asm.puts(&format!(
                    "add{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        self.operands[0].x86_operand(kind)?,
                        self.operands[1].x86_operand(kind)?
                    ])
                ));
            }
            3 => {
                asm.puts(&format!(
                    "vadd{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        self.operands[1].x86_operand(kind)?,
                        self.operands[0].x86_operand(kind)?,
                        self.operands[2].x86_operand(kind)?
                    ])
                ));
            }
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!(
                        "Unexpected number of operands for floating point addition: {}",
                        self.operands.len()
                    ),
                ));
            }
        }
        Ok(())
    }

    fn handle_x86_sub_fp(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        match self.operands.len() {
            2 => {
                asm.puts(&format!(
                    "sub{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        self.operands[0].x86_operand(kind)?,
                        self.operands[1].x86_operand(kind)?
                    ])
                ));
            }
            3 => {
                asm.puts(&format!(
                    "vsub{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        self.operands[1].x86_operand(kind)?,
                        self.operands[0].x86_operand(kind)?,
                        self.operands[2].x86_operand(kind)?
                    ])
                ));
            }
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!(
                        "Unexpected number of operands for floating point subtraction: {}",
                        self.operands.len()
                    ),
                ));
            }
        }
        Ok(())
    }

    fn handle_x86_mul_fp(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        match self.operands.len() {
            2 => {
                asm.puts(&format!(
                    "mul{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        self.operands[0].x86_operand(kind)?,
                        self.operands[1].x86_operand(kind)?
                    ])
                ));
            }
            3 => {
                asm.puts(&format!(
                    "vmul{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        self.operands[1].x86_operand(kind)?,
                        self.operands[0].x86_operand(kind)?,
                        self.operands[2].x86_operand(kind)?
                    ])
                ));
            }
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!(
                        "Unexpected number of operands for floating point multiplication: {}",
                        self.operands.len()
                    ),
                ));
            }
        }
        Ok(())
    }

    fn handle_x86_div_fp(&self, kind: OperandKind, asm: &mut Assembler) -> syn::Result<()> {
        match self.operands.len() {
            2 => {
                asm.puts(&format!(
                    "div{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        self.operands[0].x86_operand(kind)?,
                        self.operands[1].x86_operand(kind)?
                    ])
                ));
            }
            3 => {
                asm.puts(&format!(
                    "vdiv{} {}",
                    Self::x86_suffix(kind),
                    order_operands(&[
                        self.operands[1].x86_operand(kind)?,
                        self.operands[0].x86_operand(kind)?,
                        self.operands[2].x86_operand(kind)?
                    ])
                ));
            }
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!(
                        "Unexpected number of operands for floating point division: {}",
                        self.operands.len()
                    ),
                ));
            }
        }
        Ok(())
    }

    fn handle_x86_peek(&self, asm: &mut Assembler) -> syn::Result<()> {
        let sp = RegisterId::for_name_str("sp");
        let op_a = offset_register(
            self.operands[0].immediate_value()? * Self::x86_bytes(OperandKind::Ptr) as isize,
            sp.x86_operand(OperandKind::Ptr)?,
        );
        let op_b = self.operands[1].x86_operand(OperandKind::Ptr)?;
        asm.puts(&format!(
            "mov{} {}",
            Self::x86_suffix(OperandKind::Ptr),
            order_operands(&[op_a, op_b])
        ));
        Ok(())
    }

    fn handle_x86_poke(&self, asm: &mut Assembler) -> syn::Result<()> {
        let sp = RegisterId::for_name_str("sp");
        let op_a = self.operands[0].x86_operand(OperandKind::Ptr)?;
        let op_b = offset_register(
            self.operands[1].immediate_value()? * Self::x86_bytes(OperandKind::Ptr) as isize,
            sp.x86_operand(OperandKind::Ptr)?,
        );
        asm.puts(&format!(
            "mov{} {}",
            Self::x86_suffix(OperandKind::Ptr),
            order_operands(&[op_a, op_b])
        ));
        Ok(())
    }

    fn handle_move(&self, asm: &mut Assembler) -> syn::Result<()> {
        if self.operands[0].is_immediate_zero() && self.operands[1].is_register_id() {
            let op = self.operands[1].x86_operand(OperandKind::Quad)?;
            asm.puts(&format!(
                "xor{} {}, {}",
                Self::x86_suffix(OperandKind::Quad),
                op,
                op
            ));
        } else {
            let op0 = self.operands[0].x86_operand(OperandKind::Quad)?;
            let op1 = self.operands[1].x86_operand(OperandKind::Quad)?;
            if op0 != op1 {
                asm.puts(&format!(
                    "mov{} {}",
                    Self::x86_suffix(OperandKind::Quad),
                    order_operands(&[op0, op1])
                ));
            }
        }
        Ok(())
    }

    fn truncate_fp_to_quad(&self, asm: &mut Assembler, kind: OperandKind) -> syn::Result<()> {
        let src = &self.operands[0];
        let dst = &self.operands[1];

        let slow = LocalLabel::unique("slow");
        let done = LocalLabel::unique("done");

        let gpr_scratch = Node::SpecialRegister(X86_SCRATCH_REGISTER.clone());
        let fpr_scratch = Node::FPRegisterId(FPRegisterId::for_name(&Ident::new(
            "wfa7",
            Span::call_site(),
        )));
        let i64_sign_bit = Node::Immediate(Immediate {
            value: 0x8000000000000000u64 as isize,
        });
        let i64_min;
        let neg_i64_min;
        let integer_suffix;
        let floating_suffix;
        match kind {
            OperandKind::Float => {
                i64_min = Node::Immediate(Immediate { value: 0xdf000000 });
                neg_i64_min = Node::Immediate(Immediate { value: 0x5f000000 });
                integer_suffix = "i";
                floating_suffix = "f";
            }

            OperandKind::Double => {
                i64_min = Node::Immediate(Immediate {
                    value: 0xc3e0000000000000u64 as isize,
                });
                neg_i64_min = Node::Immediate(Immediate {
                    value: 0x43e0000000000000u64 as isize,
                });
                integer_suffix = "q";
                floating_suffix = "d";
            }

            _ => unreachable!(),
        };

        let seq = vec![
            Node::Instruction(Instruction::new(
                id("mov"),
                punc_from_vec(vec![neg_i64_min.clone(), gpr_scratch.clone()]),
            )),
            Node::Instruction(Instruction::new(
                id(format!("f{integer_suffix}2{floating_suffix}")),
                punc_from_vec(vec![gpr_scratch.clone(), fpr_scratch.clone()]),
            )),
            Node::Instruction(Instruction::new(
                id(format!("b{floating_suffix}geq")),
                punc_from_vec(vec![
                    src.clone(),
                    fpr_scratch.clone(),
                    Node::LocalLabelReference(LocalLabelReference::new(slow.clone())),
                ]),
            )),
            Node::Instruction(Instruction::new(
                id(format!("truncate{floating_suffix}2qs")),
                punc_from_vec(vec![src.clone(), dst.clone()]),
            )),
            Node::Instruction(Instruction::new(
                id("jmp"),
                punc_from_vec(vec![Node::LocalLabelReference(LocalLabelReference::new(
                    done.clone(),
                ))]),
            )),
            Node::LocalLabel(slow.clone()),
            Node::Instruction(Instruction::new(
                id("mov"),
                punc_from_vec(vec![i64_min.clone(), gpr_scratch.clone()]),
            )),
            Node::Instruction(Instruction::new(
                id(format!("f{integer_suffix}2{floating_suffix}")),
                punc_from_vec(vec![gpr_scratch.clone(), fpr_scratch.clone()]),
            )),
            Node::Instruction(Instruction::new(
                id(format!("add{floating_suffix}")),
                punc_from_vec(vec![src.clone(), fpr_scratch.clone()]),
            )),
            Node::Instruction(Instruction::new(
                id(format!("truncate{floating_suffix}2qs")),
                punc_from_vec(vec![fpr_scratch.clone(), dst.clone()]),
            )),
            Node::Instruction(Instruction::new(
                id("mov"),
                punc_from_vec(vec![i64_sign_bit, gpr_scratch.clone()]),
            )),
            Node::Instruction(Instruction::new(
                id("orq"),
                punc_from_vec(vec![gpr_scratch.clone(), dst.clone()]),
            )),
            Node::LocalLabel(done.clone()),
        ];

        let seq = Node::Seq(punc_from_vec(seq));

        seq.lower(asm)?;

        Ok(())
    }

    fn convert_quad_to_fp(&self, asm: &mut Assembler, kind: OperandKind) -> syn::Result<()> {
        let src = &self.operands[0];
        let scratch1 = &self.operands[1];
        let dst = &self.operands[2];

        let slow = LocalLabel::unique("slow");
        let done = LocalLabel::unique("done");

        let scratch2 = Node::SpecialRegister(X86_SCRATCH_REGISTER.clone());
        let one = Node::Immediate(Immediate { value: 1 });

        let floating_suffix = match kind {
            OperandKind::Float => "f",
            OperandKind::Double => "d",
            _ => unreachable!(),
        };

        let mut seq = vec![];

        seq.push(Node::Instruction(Instruction::new(
            id("btqs"),
            punc_from_vec(vec![
                src.clone(),
                Node::LocalLabelReference(LocalLabelReference::new(slow.clone())),
            ]),
        )));

        seq.push(Node::Instruction(Instruction::new(
            id(&format!("cq2{}s", floating_suffix)),
            punc_from_vec(vec![src.clone(), dst.clone()]),
        )));
        seq.push(Node::Instruction(Instruction::new(
            id("jmp"),
            punc_from_vec(vec![Node::LocalLabelReference(LocalLabelReference::new(
                done.clone(),
            ))]),
        )));

        seq.push(Node::LocalLabel(slow.clone()));
        seq.push(Node::Instruction(Instruction::new(
            id("mov"),
            punc_from_vec(vec![src.clone(), scratch1.clone()]),
        )));
        seq.push(Node::Instruction(Instruction::new(
            id("mov"),
            punc_from_vec(vec![src.clone(), scratch2.clone()]),
        )));
        seq.push(Node::Instruction(Instruction::new(
            id("urshiftq"),
            punc_from_vec(vec![one.clone(), scratch1.clone()]),
        )));
        seq.push(Node::Instruction(Instruction::new(
            id("andq"),
            punc_from_vec(vec![one.clone(), scratch2.clone()]),
        )));
        seq.push(Node::Instruction(Instruction::new(
            id("orq"),
            punc_from_vec(vec![scratch1.clone(), scratch2.clone()]),
        )));
        seq.push(Node::Instruction(Instruction::new(
            id(&format!("cq2{}s", floating_suffix)),
            punc_from_vec(vec![scratch2.clone(), dst.clone()]),
        )));
        seq.push(Node::Instruction(Instruction::new(
            id(&format!("add{}", floating_suffix)),
            punc_from_vec(vec![dst.clone(), dst.clone()]),
        )));
        seq.push(Node::LocalLabel(done.clone()));

        let seq = Node::Seq(punc_from_vec(seq));

        seq.lower(asm)?;

        Ok(())
    }

    fn handle_count_leading_zeros(
        &self,
        asm: &mut Assembler,
        kind: OperandKind,
    ) -> syn::Result<()> {
        let target = &self.operands[1];
        let src_is_non_zero = LocalLabel::unique("srcIsNonZero");
        let skip_non_zero_case = LocalLabel::unique("skipNonZeroCase");
        let zero_value = Immediate {
            value: Self::x86_bytes(kind) as isize * 8,
        };
        let xor_value = Immediate {
            value: if kind == OperandKind::Quad {
                0x3f
            } else {
                0x1f
            },
        };
        let xor = if kind == OperandKind::Quad {
            "xorq"
        } else {
            "xori"
        };

        asm.puts(&format!(
            "bsr{} {}",
            Self::x86_suffix(kind),
            self.x86_operands(&[kind, kind])?
        ));

        let mut seq = vec![
            Node::Instruction(Instruction::new(
                id("bnz"),
                punc_from_vec(vec![Node::LocalLabelReference(LocalLabelReference::new(
                    src_is_non_zero.clone(),
                ))]),
            )),
            Node::Instruction(Instruction::new(
                id("mov"),
                punc_from_vec(vec![Node::Immediate(zero_value), target.clone()]),
            )),
            Node::Instruction(Instruction::new(
                id("jmp"),
                punc_from_vec(vec![Node::LocalLabelReference(LocalLabelReference::new(
                    skip_non_zero_case.clone(),
                ))]),
            )),
            Node::LocalLabel(src_is_non_zero),
            Node::Instruction(Instruction::new(
                id(xor),
                punc_from_vec(vec![Node::Immediate(xor_value), target.clone()]),
            )),
            Node::LocalLabel(skip_non_zero_case),
        ];

        Node::Seq(punc_from_vec(seq)).lower(asm)?;
        Ok(())
    }

    fn handle_count_trailing_zeros(
        &self,
        asm: &mut Assembler,
        kind: OperandKind,
    ) -> syn::Result<()> {
        let target = &self.operands[1];
        let src_is_non_zero = LocalLabel::unique("srcIsNonZero");
        let zero_value = Immediate {
            value: Self::x86_bytes(kind) as isize * 8,
        };

        asm.puts(&format!(
            "bsf{} {}",
            Self::x86_suffix(kind),
            self.x86_operands(&[kind, kind])?
        ));

        let mut seq = vec![
            Node::Instruction(Instruction::new(
                id("bnz"),
                punc_from_vec(vec![Node::LocalLabelReference(LocalLabelReference::new(
                    src_is_non_zero.clone(),
                ))]),
            )),
            Node::Instruction(Instruction::new(
                id("mov"),
                punc_from_vec(vec![Node::Immediate(zero_value), target.clone()]),
            )),
            Node::LocalLabel(src_is_non_zero),
        ];

        Node::Seq(punc_from_vec(seq)).lower(asm)?;
        Ok(())
    }

    pub fn lower_x86(&self, asm: &mut Assembler) -> syn::Result<()> {
        let opcode = self.opcode.to_string();

        match opcode.as_str() {
            "mov" => self.handle_move(asm)?,
            "addi" => self.handle_x86_add(asm, OperandKind::Int)?,
            "addp" => self.handle_x86_add(asm, OperandKind::Ptr)?,
            "addq" => self.handle_x86_add(asm, OperandKind::Quad)?,
            "andi" => self.handle_x86_op(asm, "and", OperandKind::Int)?,
            "andp" => self.handle_x86_op(asm, "and", OperandKind::Ptr)?,
            "andq" => self.handle_x86_op(asm, "and", OperandKind::Quad)?,
            "andf" => self.handle_x86_op(asm, "andps", OperandKind::Float)?,
            "andd" => self.handle_x86_op(asm, "andpd", OperandKind::Double)?,
            "lshifti" => self.handle_x86_shift(asm, "sal", OperandKind::Int)?,
            "lshiftp" => self.handle_x86_shift(asm, "sal", OperandKind::Ptr)?,
            "lshiftq" => self.handle_x86_shift(asm, "sal", OperandKind::Quad)?,
            "muli" => self.handle_x86_mul(OperandKind::Int, asm)?,
            "mulp" => self.handle_x86_mul(OperandKind::Ptr, asm)?,
            "mulq" => self.handle_x86_mul(OperandKind::Quad, asm)?,
            "negi" => {
                asm.puts(&format!(
                    "neg{} {}",
                    Self::x86_suffix(OperandKind::Int),
                    self.x86_operands(&[OperandKind::Int])?
                ));
            }
            "negp" => {
                asm.puts(&format!(
                    "neg{} {}",
                    Self::x86_suffix(OperandKind::Ptr),
                    self.x86_operands(&[OperandKind::Ptr])?
                ));
            }
            "negq" => {
                asm.puts(&format!(
                    "neg{} {}",
                    Self::x86_suffix(OperandKind::Quad),
                    self.x86_operands(&[OperandKind::Quad])?
                ));
            }
            "noti" => {
                asm.puts(&format!(
                    "not{} {}",
                    Self::x86_suffix(OperandKind::Int),
                    self.x86_operands(&[OperandKind::Int])?
                ));
            }
            "notq" => {
                asm.puts(&format!(
                    "not{} {}",
                    Self::x86_suffix(OperandKind::Quad),
                    self.x86_operands(&[OperandKind::Quad])?
                ));
            }
            "ori" => self.handle_x86_op(asm, "or", OperandKind::Int)?,

            "orp" => self.handle_x86_op(asm, "or", OperandKind::Ptr)?,
            "orq" => self.handle_x86_op(asm, "or", OperandKind::Quad)?,
            "orf" => self.handle_x86_op(asm, "orps", OperandKind::Float)?,
            "ord" => self.handle_x86_op(asm, "orpd", OperandKind::Double)?,
            "orh" => self.handle_x86_op(asm, "or", OperandKind::Half)?,
            "rshifti" => self.handle_x86_shift(asm, "sar", OperandKind::Int)?,
            "rshiftp" => self.handle_x86_shift(asm, "sar", OperandKind::Ptr)?,
            "rshiftq" => self.handle_x86_shift(asm, "sar", OperandKind::Quad)?,
            "urshifti" => self.handle_x86_shift(asm, "shr", OperandKind::Int)?,
            "urshiftp" => self.handle_x86_shift(asm, "shr", OperandKind::Ptr)?,
            "urshiftq" => self.handle_x86_shift(asm, "shr", OperandKind::Quad)?,
            "rrotatei" => self.handle_x86_shift(asm, "ror", OperandKind::Int)?,
            "rrotateq" => self.handle_x86_shift(asm, "ror", OperandKind::Quad)?,
            "lrotatei" => self.handle_x86_shift(asm, "rol", OperandKind::Int)?,
            "lrotateq" => self.handle_x86_shift(asm, "rol", OperandKind::Quad)?,
            "subi" => self.handle_x86_sub(OperandKind::Int, asm)?,
            "subp" => self.handle_x86_sub(OperandKind::Ptr, asm)?,
            "subq" => self.handle_x86_sub(OperandKind::Quad, asm)?,
            "xori" => self.handle_x86_op(asm, "xor", OperandKind::Int)?,
            "xorp" => self.handle_x86_op(asm, "xor", OperandKind::Ptr)?,
            "xorq" => self.handle_x86_op(asm, "xor", OperandKind::Quad)?,
            "leap" => {
                Self::emit_x86_lea(asm, &self.operands[0], &self.operands[1], OperandKind::Ptr)?
            }
            "loadi" | "atomicloadi" => {
                let op = self.x86_load_operands(asm, OperandKind::Int, OperandKind::Int)?;
                asm.puts(&format!("mov{} {}", Self::x86_suffix(OperandKind::Int), op));
            }
            "storei" => {
                let op = self.x86_operands(&[OperandKind::Int, OperandKind::Int])?;
                asm.puts(&format!("mov{} {}", Self::x86_suffix(OperandKind::Int), op));
            }
            "loadis" => {
                let op = self.x86_load_operands(asm, OperandKind::Int, OperandKind::Quad)?;
                asm.puts(&format!("movslq {}", op));
            }
            "loadp" => {
                let op = self.x86_load_operands(asm, OperandKind::Ptr, OperandKind::Ptr)?;
                asm.puts(&format!("mov{} {}", Self::x86_suffix(OperandKind::Ptr), op));
            }
            "storep" => {
                let op = self.x86_operands(&[OperandKind::Ptr, OperandKind::Ptr])?;
                asm.puts(&format!("mov{} {}", Self::x86_suffix(OperandKind::Ptr), op));
            }

            "loadq" | "atomicloadq" => {
                let op = self.x86_load_operands(asm, OperandKind::Quad, OperandKind::Quad)?;
                asm.puts(&format!(
                    "mov{} {}",
                    Self::x86_suffix(OperandKind::Quad),
                    op
                ));
            }
            "storeq" => {
                let op = self.x86_operands(&[OperandKind::Quad, OperandKind::Quad])?;
                asm.puts(&format!(
                    "mov{} {}",
                    Self::x86_suffix(OperandKind::Quad),
                    op
                ));
            }
            "loadb" | "atomicloadb" => {
                let op = self.x86_load_operands(asm, OperandKind::Byte, OperandKind::Int)?;
                asm.puts(&format!("movzbl {}", op));
            }
            "loadbsi" => {
                let op = self.x86_load_operands(asm, OperandKind::Byte, OperandKind::Int)?;
                asm.puts(&format!("movsbl {}", op));
            }
            "loadbsq" => {
                let op = self.x86_load_operands(asm, OperandKind::Byte, OperandKind::Quad)?;
                asm.puts(&format!("movsbq {}", op));
            }
            "loadh" | "atomicloadh" => {
                let op = self.x86_load_operands(asm, OperandKind::Half, OperandKind::Int)?;
                asm.puts(&format!("movzwl {}", op));
            }
            "loadhsi" => {
                let op = self.x86_load_operands(asm, OperandKind::Half, OperandKind::Int)?;
                asm.puts(&format!("movswl {}", op));
            }
            "loadhsq" => {
                let op = self.x86_load_operands(asm, OperandKind::Half, OperandKind::Quad)?;
                asm.puts(&format!("movswq {}", op));
            }
            "storeb" => {
                asm.puts(&format!(
                    "mov{} {}",
                    Self::x86_suffix(OperandKind::Byte),
                    self.x86_operands(&[OperandKind::Byte, OperandKind::Byte])?
                ));
            }
            "storeh" => {
                asm.puts(&format!(
                    "mov{} {}",
                    Self::x86_suffix(OperandKind::Half),
                    self.x86_operands(&[OperandKind::Half, OperandKind::Half])?
                ));
            }
            "loadf" => {
                asm.puts(&format!(
                    "movss {}",
                    self.x86_operands(&[OperandKind::Float, OperandKind::Float])?
                ));
            }
            "loadd" => {
                asm.puts(&format!(
                    "movsd {}",
                    self.x86_operands(&[OperandKind::Double, OperandKind::Double])?
                ));
            }
            "loadv" => {
                asm.puts(&format!(
                    "movdqu {}",
                    self.x86_operands(&[OperandKind::Int, OperandKind::Double])?
                ));
            }
            "moved" => {
                asm.puts(&format!(
                    "movsd {}",
                    self.x86_operands(&[OperandKind::Double, OperandKind::Double])?
                ));
            }
            "storef" => {
                asm.puts(&format!(
                    "movss {}",
                    self.x86_operands(&[OperandKind::Float, OperandKind::Float])?
                ));
            }
            "stored" => {
                asm.puts(&format!(
                    "movsd {}",
                    self.x86_operands(&[OperandKind::Double, OperandKind::Double])?
                ));
            }
            "storev" => {
                asm.puts(&format!(
                    "movups {}",
                    self.x86_operands(&[OperandKind::Vector, OperandKind::Vector])?
                ));
            }
            "addf" => self.handle_x86_add_fp(OperandKind::Float, asm)?,
            "addd" => self.handle_x86_add_fp(OperandKind::Double, asm)?,
            "mulf" => self.handle_x86_mul_fp(OperandKind::Float, asm)?,
            "muld" => self.handle_x86_mul_fp(OperandKind::Double, asm)?,
            "subf" => self.handle_x86_sub_fp(OperandKind::Float, asm)?,
            "subd" => self.handle_x86_sub_fp(OperandKind::Double, asm)?,
            "divf" => self.handle_x86_div_fp(OperandKind::Float, asm)?,
            "divd" => self.handle_x86_div_fp(OperandKind::Double, asm)?,
            "sqrtf" => {
                asm.puts(&format!(
                    "sqrtss {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Float)?,
                        self.operands[1].x86_operand(OperandKind::Float)?
                    ])
                ));
            }
            "sqrtd" => {
                asm.puts(&format!(
                    "sqrtsd {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Double)?,
                        self.operands[1].x86_operand(OperandKind::Double)?
                    ])
                ));
            }
            "roundf" => {
                asm.puts(&format!(
                    "roundss ${}, {}, {}",
                    0,
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Double)?
                ));
            }
            "roundd" => {
                asm.puts(&format!(
                    "roundsd ${}, {}, {}",
                    0,
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Double)?
                ));
            }
            "floorf" => {
                asm.puts(&format!(
                    "roundss ${}, {}, {}",
                    1,
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Double)?
                ));
            }
            "floord" => {
                asm.puts(&format!(
                    "roundsd ${}, {}, {}",
                    1,
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Double)?
                ));
            }
            "ceilf" => {
                asm.puts(&format!(
                    "roundss ${}, {}, {}",
                    2,
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Double)?
                ));
            }
            "ceild" => {
                asm.puts(&format!(
                    "roundsd ${}, {}, {}",
                    2,
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Double)?
                ));
            }
            "truncatef" => {
                asm.puts(&format!(
                    "roundss ${}, {}, {}",
                    3,
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Double)?
                ));
            }
            "truncated" => {
                asm.puts(&format!(
                    "roundsd ${}, {}, {}",
                    3,
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Double)?
                ));
            }
            "truncatef2i" => {
                asm.puts(&format!(
                    "cvttss2si {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Float)?,
                        self.operands[1].x86_operand(OperandKind::Quad)?
                    ])
                ));
            }
            "truncatef2q" => self.truncate_fp_to_quad(asm, OperandKind::Float)?,
            "truncated2q" => self.truncate_fp_to_quad(asm, OperandKind::Double)?,
            "truncated2i" => {
                asm.puts(&format!(
                    "cvttsd2si {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Double)?,
                        self.operands[1].x86_operand(OperandKind::Quad)?
                    ])
                ));
            }

            "truncatef2is" => {
                asm.puts(&format!(
                    "cvttss2si {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Float)?,
                        self.operands[1].x86_operand(OperandKind::Int)?
                    ])
                ));
            }
            "truncatef2qs" => {
                asm.puts(&format!(
                    "cvttss2si {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Float)?,
                        self.operands[1].x86_operand(OperandKind::Quad)?
                    ])
                ));
            }
            "truncated2is" => {
                asm.puts(&format!(
                    "cvttsd2si {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Double)?,
                        self.operands[1].x86_operand(OperandKind::Int)?
                    ])
                ));
            }
            "truncated2qs" => {
                asm.puts(&format!(
                    "cvttsd2si {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Double)?,
                        self.operands[1].x86_operand(OperandKind::Quad)?
                    ])
                ));
            }
            "ci2d" => {
                asm.puts(&format!(
                    "cvtsi2sd {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Quad)?,
                        self.operands[1].x86_operand(OperandKind::Double)?
                    ])
                ));
            }
            "ci2ds" => {
                asm.puts(&format!(
                    "cvtsi2sd {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Int)?,
                        self.operands[1].x86_operand(OperandKind::Double)?
                    ])
                ));
            }
            "ci2fs" => {
                asm.puts(&format!(
                    "cvtsi2ss {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Int)?,
                        self.operands[1].x86_operand(OperandKind::Float)?
                    ])
                ));
            }
            "ci2f" => {
                asm.puts(&format!(
                    "cvtsi2ss {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Quad)?,
                        self.operands[1].x86_operand(OperandKind::Float)?
                    ])
                ));
            }

            "cq2f" => self.convert_quad_to_fp(asm, OperandKind::Float)?,
            "cq2d" => self.convert_quad_to_fp(asm, OperandKind::Double)?,
            "cq2fs" => {
                asm.puts(&format!(
                    "cvtsi2ssq {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Quad)?,
                        self.operands[1].x86_operand(OperandKind::Float)?
                    ])
                ));
            }
            "cq2ds" => {
                asm.puts(&format!(
                    "cvtsi2sdq {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Quad)?,
                        self.operands[1].x86_operand(OperandKind::Double)?
                    ])
                ));
            }
            "cd2f" => {
                asm.puts(&format!(
                    "cvtsd2ss {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Double)?,
                        self.operands[1].x86_operand(OperandKind::Float)?
                    ])
                ));
            }
            "cf2d" => {
                asm.puts(&format!(
                    "cvtss2sd {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Float)?,
                        self.operands[1].x86_operand(OperandKind::Double)?
                    ])
                ));
            }

            "bdeq" => {
                asm.puts(&format!(
                    "ucomisd {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Double)?,
                        self.operands[1].x86_operand(OperandKind::Double)?
                    ])
                ));
                if self.operands[0] == self.operands[1] {
                    asm.puts(&format!("jnp {}", self.operands[2].asm_label()?));
                } else {
                    let is_unordered = LocalLabel::unique("bdeq");
                    asm.puts(&format!("jp {}", is_unordered.name));
                    asm.puts(&format!("je {}", self.operands[2].asm_label()?));
                    is_unordered.lower(asm)?;
                }
            }

            "bdneq" => self.handle_x86_fp_branch(asm, OperandKind::Double, "jne", true)?,
            "bdgt" => self.handle_x86_fp_branch(asm, OperandKind::Double, "ja", true)?,
            "bdgteq" => self.handle_x86_fp_branch(asm, OperandKind::Double, "jae", true)?,
            "bdlt" => self.handle_x86_fp_branch(asm, OperandKind::Double, "ja", false)?,
            "bdlteq" => self.handle_x86_fp_branch(asm, OperandKind::Double, "jae", false)?,
            "bdequn" => self.handle_x86_fp_branch(asm, OperandKind::Double, "je", true)?,
            "bdnequn" => {
                asm.puts(&format!(
                    "ucomisd {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Double)?,
                        self.operands[1].x86_operand(OperandKind::Double)?
                    ])
                ));
                if self.operands[0] == self.operands[1] {
                    asm.puts(&format!("jp {}", self.operands[2].asm_label()?));
                } else {
                    let is_unordered = LocalLabel::unique("bdnequn");
                    let is_equal = LocalLabel::unique("bdnequn");
                    asm.puts(&format!("jp {}", is_unordered.name));
                    asm.puts(&format!("je {}", is_equal.name));
                    is_unordered.lower(asm)?;
                    asm.puts(&format!("jmp {}", self.operands[2].asm_label()?));
                    is_equal.lower(asm)?;
                }
            }

            "bdgtun" => self.handle_x86_fp_branch(asm, OperandKind::Double, "jb", false)?,
            "bdgtequn" => self.handle_x86_fp_branch(asm, OperandKind::Double, "jbe", false)?,
            "bdltun" => self.handle_x86_fp_branch(asm, OperandKind::Double, "jb", true)?,
            "bdltequn" => self.handle_x86_fp_branch(asm, OperandKind::Double, "jbe", true)?,
            "bfeq" => {
                asm.puts(&format!(
                    "ucomiss {}",
                    order_operands(&[
                        self.operands[0].x86_operand(OperandKind::Float)?,
                        self.operands[1].x86_operand(OperandKind::Float)?
                    ])
                ));
                if self.operands[0] == self.operands[1] {
                    asm.puts(&format!("jnp {}", self.operands[2].asm_label()?));
                } else {
                    let is_unordered = LocalLabel::unique("bfeq");
                    asm.puts(&format!("jp {}", is_unordered.name));
                    asm.puts(&format!("je {}", self.operands[2].asm_label()?));
                    is_unordered.lower(asm)?;
                }
            }
            "bfgt" => self.handle_x86_fp_branch(asm, OperandKind::Float, "ja", true)?,
            "bfgteq" => self.handle_x86_fp_branch(asm, OperandKind::Float, "jae", true)?,
            "bflt" => self.handle_x86_fp_branch(asm, OperandKind::Float, "ja", false)?,
            "bfgtun" => self.handle_x86_fp_branch(asm, OperandKind::Float, "jb", false)?,
            "bfgtequn" => self.handle_x86_fp_branch(asm, OperandKind::Float, "jbe", false)?,
            "bfltun" => self.handle_x86_fp_branch(asm, OperandKind::Float, "jb", true)?,
            "bfltequn" => self.handle_x86_fp_branch(asm, OperandKind::Float, "jbe", true)?,
            "btd2i" => {
                asm.puts(&format!(
                    "cvttsd2si {}, {}",
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Int)?
                ));
                asm.puts(&format!(
                    "cmpl ${}, {}",
                    "80000000",
                    self.operands[1].x86_operand(OperandKind::Int)?
                ));
                asm.puts(&format!("je {}", self.operands[2].asm_label()?));
            }
            "td2i" => {
                asm.puts(&format!(
                    "cvttsd2si {}, {}",
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Int)?
                ));
            }
            "bcd2i" => {
                asm.puts(&format!(
                    "cvttsd2si {}, {}",
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[1].x86_operand(OperandKind::Int)?
                ));
                asm.puts(&format!(
                    "testl {}, {}",
                    self.operands[1].x86_operand(OperandKind::Int)?,
                    self.operands[1].x86_operand(OperandKind::Int)?
                ));
                asm.puts(&format!("je {}", self.operands[2].asm_label()?));
                asm.puts(&format!(
                    "cvtsi2sd {}, %xmm7",
                    self.operands[1].x86_operand(OperandKind::Int)?
                ));
                asm.puts(&format!(
                    "ucomisd {}, %xmm7",
                    self.operands[0].x86_operand(OperandKind::Double)?
                ));
                asm.puts(&format!("jp {}", self.operands[2].asm_label()?));
                asm.puts(&format!("jne {}", self.operands[2].asm_label()?));
            }

            "movdz" => {
                asm.puts(&format!(
                    "xorpd {}, {}",
                    self.operands[0].x86_operand(OperandKind::Double)?,
                    self.operands[0].x86_operand(OperandKind::Double)?
                ));
            }

            "pop" => {
                for operand in self.operands.iter() {
                    asm.puts(&format!("pop {}", operand.x86_operand(OperandKind::Ptr)?));
                }
            }

            "popv" => {
                for operand in self.operands.iter() {
                    asm.puts(&format!(
                        "movdqu (%rsp), {}",
                        operand.x86_operand(OperandKind::Vector)?
                    ));
                    asm.puts("add $16, %rsp");
                }
            }

            "push" => {
                for operand in self.operands.iter() {
                    asm.puts(&format!("push {}", operand.x86_operand(OperandKind::Ptr)?));
                }
            }

            "pushv" => {
                for operand in self.operands.iter() {
                    asm.puts(&format!("sub $16, %rsp",));
                    asm.puts(&format!(
                        "movdqu {}, (%rsp)",
                        operand.x86_operand(OperandKind::Vector)?
                    ));
                }
            }

            "sxi2q" => asm.puts(&format!(
                "movslq {}, {}",
                self.operands[0].x86_operand(OperandKind::Int)?,
                self.operands[1].x86_operand(OperandKind::Quad)?
            )),
            "zxi2q" => asm.puts(&format!(
                "mov{} {}, {}",
                Self::x86_suffix(OperandKind::Int),
                self.operands[0].x86_operand(OperandKind::Int)?,
                self.operands[1].x86_operand(OperandKind::Int)?
            )),
            "sxb2i" => asm.puts(&format!(
                "movsbl {}, {}",
                self.operands[0].x86_operand(OperandKind::Byte)?,
                self.operands[1].x86_operand(OperandKind::Int)?
            )),
            "sxh2i" => asm.puts(&format!(
                "movswl {}, {}",
                self.operands[0].x86_operand(OperandKind::Half)?,
                self.operands[1].x86_operand(OperandKind::Int)?
            )),
            "sxb2q" => asm.puts(&format!(
                "movsbq {}, {}",
                self.operands[0].x86_operand(OperandKind::Byte)?,
                self.operands[1].x86_operand(OperandKind::Quad)?
            )),
            "sxh2q" => asm.puts(&format!(
                "movswq {}, {}",
                self.operands[0].x86_operand(OperandKind::Half)?,
                self.operands[1].x86_operand(OperandKind::Quad)?
            )),
            "nop" => asm.puts("nop"),
            "bieq" => self.handle_x86_int_branch(asm, "je", OperandKind::Int)?,
            "bpeq" => self.handle_x86_int_branch(asm, "je", OperandKind::Ptr)?,
            "bqeq" => self.handle_x86_int_branch(asm, "je", OperandKind::Quad)?,
            "bineq" => self.handle_x86_int_branch(asm, "jne", OperandKind::Int)?,
            "bpneq" => self.handle_x86_int_branch(asm, "jne", OperandKind::Ptr)?,
            "bqneq" => self.handle_x86_int_branch(asm, "jne", OperandKind::Quad)?,
            "bia" => self.handle_x86_int_branch(asm, "ja", OperandKind::Int)?,
            "bpa" => self.handle_x86_int_branch(asm, "ja", OperandKind::Ptr)?,
            "bqa" => self.handle_x86_int_branch(asm, "ja", OperandKind::Quad)?,
            "biaeq" => self.handle_x86_int_branch(asm, "jae", OperandKind::Int)?,
            "bpaeq" => self.handle_x86_int_branch(asm, "jae", OperandKind::Ptr)?,
            "bqaeq" => self.handle_x86_int_branch(asm, "jae", OperandKind::Quad)?,
            "bib" => self.handle_x86_int_branch(asm, "jb", OperandKind::Int)?,
            "bpb" => self.handle_x86_int_branch(asm, "jb", OperandKind::Ptr)?,
            "bqb" => self.handle_x86_int_branch(asm, "jb", OperandKind::Quad)?,
            "bibeq" => self.handle_x86_int_branch(asm, "jbe", OperandKind::Int)?,
            "bpbeq" => self.handle_x86_int_branch(asm, "jbe", OperandKind::Ptr)?,
            "bqbeq" => self.handle_x86_int_branch(asm, "jbe", OperandKind::Quad)?,
            "bigt" => self.handle_x86_int_branch(asm, "jg", OperandKind::Int)?,
            "bpgt" => self.handle_x86_int_branch(asm, "jg", OperandKind::Ptr)?,
            "bqgt" => self.handle_x86_int_branch(asm, "jg", OperandKind::Quad)?,
            "bigteq" => self.handle_x86_int_branch(asm, "jge", OperandKind::Int)?,
            "bpgteq" => self.handle_x86_int_branch(asm, "jge", OperandKind::Ptr)?,
            "bqgteq" => self.handle_x86_int_branch(asm, "jge", OperandKind::Quad)?,
            "bilt" => self.handle_x86_int_branch(asm, "jl", OperandKind::Int)?,
            "bplt" => self.handle_x86_int_branch(asm, "jl", OperandKind::Ptr)?,
            "bqlt" => self.handle_x86_int_branch(asm, "jl", OperandKind::Quad)?,
            "bilteq" => self.handle_x86_int_branch(asm, "jle", OperandKind::Int)?,
            "bplteq" => self.handle_x86_int_branch(asm, "jle", OperandKind::Ptr)?,
            "bqlteq" => self.handle_x86_int_branch(asm, "jle", OperandKind::Quad)?,
            "bbeq" => self.handle_x86_int_branch(asm, "je", OperandKind::Byte)?,
            "bbneq" => self.handle_x86_int_branch(asm, "jne", OperandKind::Byte)?,
            "bba" => self.handle_x86_int_branch(asm, "ja", OperandKind::Byte)?,
            "bbaeq" => self.handle_x86_int_branch(asm, "jae", OperandKind::Byte)?,
            "bbb" => self.handle_x86_int_branch(asm, "jb", OperandKind::Byte)?,
            "bbbeq" => self.handle_x86_int_branch(asm, "jbe", OperandKind::Byte)?,
            "bbgt" => self.handle_x86_int_branch(asm, "jg", OperandKind::Byte)?,
            "bbgteq" => self.handle_x86_int_branch(asm, "jge", OperandKind::Byte)?,
            "bblt" => self.handle_x86_int_branch(asm, "jl", OperandKind::Byte)?,
            "bblteq" => self.handle_x86_int_branch(asm, "jle", OperandKind::Byte)?,
            "btis" => self.handle_x86_branch_test(asm, "js", OperandKind::Int)?,
            "btps" => self.handle_x86_branch_test(asm, "js", OperandKind::Ptr)?,
            "btqs" => self.handle_x86_branch_test(asm, "js", OperandKind::Quad)?,
            "btiz" => self.handle_x86_branch_test(asm, "jz", OperandKind::Int)?,
            "btpz" => self.handle_x86_branch_test(asm, "jz", OperandKind::Ptr)?,
            "btqz" => self.handle_x86_branch_test(asm, "jz", OperandKind::Quad)?,
            "btinz" => self.handle_x86_branch_test(asm, "jnz", OperandKind::Int)?,
            "btpnz" => self.handle_x86_branch_test(asm, "jnz", OperandKind::Ptr)?,
            "btqnz" => self.handle_x86_branch_test(asm, "jnz", OperandKind::Quad)?,
            "btbs" => self.handle_x86_branch_test(asm, "js", OperandKind::Byte)?,
            "btbz" => self.handle_x86_branch_test(asm, "jz", OperandKind::Byte)?,
            "btbnz" => self.handle_x86_branch_test(asm, "jnz", OperandKind::Byte)?,
            "jmp" => asm.puts(&format!(
                "jmp {}",
                self.operands[0].x86_call_operand(OperandKind::Ptr)?
            )),
            "baddio" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Int)),
                "jo",
                OperandKind::Int,
            )?,
            "baddpo" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Ptr)),
                "jo",
                OperandKind::Ptr,
            )?,
            "baddqo" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Quad)),
                "jo",
                OperandKind::Quad,
            )?,
            "baddis" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Int)),
                "js",
                OperandKind::Int,
            )?,
            "baddps" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Ptr)),
                "js",
                OperandKind::Ptr,
            )?,
            "baddqs" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Quad)),
                "js",
                OperandKind::Quad,
            )?,
            "baddiz" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Int)),
                "jz",
                OperandKind::Int,
            )?,
            "baddpz" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Ptr)),
                "jz",
                OperandKind::Ptr,
            )?,
            "baddqz" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Quad)),
                "jz",
                OperandKind::Quad,
            )?,
            "baddinz" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Int)),
                "jnz",
                OperandKind::Int,
            )?,
            "baddpnz" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Ptr)),
                "jnz",
                OperandKind::Ptr,
            )?,
            "baddqnz" => self.handle_x86_op_branch(
                asm,
                &format!("add{}", Self::x86_suffix(OperandKind::Quad)),
                "jnz",
                OperandKind::Quad,
            )?,
            "bsubio" => self.handle_x86_sub_branch(asm, "jo", OperandKind::Int)?,
            "bsubis" => self.handle_x86_sub_branch(asm, "js", OperandKind::Int)?,
            "bsubiz" => self.handle_x86_sub_branch(asm, "jz", OperandKind::Int)?,
            "bsubinz" => self.handle_x86_sub_branch(asm, "jnz", OperandKind::Int)?,
            "bmulio" => self.handle_x86_op_branch(
                asm,
                &format!("imul{}", Self::x86_suffix(OperandKind::Int)),
                "jo",
                OperandKind::Int,
            )?,
            "bmulis" => self.handle_x86_op_branch(
                asm,
                &format!("imul{}", Self::x86_suffix(OperandKind::Int)),
                "js",
                OperandKind::Int,
            )?,
            "bmuliz" => self.handle_x86_op_branch(
                asm,
                &format!("imul{}", Self::x86_suffix(OperandKind::Int)),
                "jz",
                OperandKind::Int,
            )?,
            "bmulinz" => self.handle_x86_op_branch(
                asm,
                &format!("imul{}", Self::x86_suffix(OperandKind::Int)),
                "jnz",
                OperandKind::Int,
            )?,
            "call" => asm.puts(&format!(
                "call {}",
                self.operands[0].x86_call_operand(OperandKind::Ptr)?
            )),
            "ret" => asm.puts("ret"),
            "break" => asm.puts("int $3"),
            "cieq" => self.handle_x86_int_compare_set(asm, "sete", OperandKind::Int)?,
            "cbeq" => self.handle_x86_int_compare_set(asm, "sete", OperandKind::Byte)?,
            "cpeq" => self.handle_x86_int_compare_set(asm, "sete", OperandKind::Ptr)?,
            "cqeq" => self.handle_x86_int_compare_set(asm, "sete", OperandKind::Quad)?,
            "cineq" => self.handle_x86_int_compare_set(asm, "setne", OperandKind::Int)?,
            "cbneq" => self.handle_x86_int_compare_set(asm, "setne", OperandKind::Byte)?,
            "cpneq" => self.handle_x86_int_compare_set(asm, "setne", OperandKind::Ptr)?,
            "cqneq" => self.handle_x86_int_compare_set(asm, "setne", OperandKind::Quad)?,
            "cia" => self.handle_x86_int_compare_set(asm, "seta", OperandKind::Int)?,
            "cba" => self.handle_x86_int_compare_set(asm, "seta", OperandKind::Byte)?,
            "cpa" => self.handle_x86_int_compare_set(asm, "seta", OperandKind::Ptr)?,
            "cqa" => self.handle_x86_int_compare_set(asm, "seta", OperandKind::Quad)?,
            "ciaeq" => self.handle_x86_int_compare_set(asm, "setae", OperandKind::Int)?,
            "cbaeq" => self.handle_x86_int_compare_set(asm, "setae", OperandKind::Byte)?,
            "cpaeq" => self.handle_x86_int_compare_set(asm, "setae", OperandKind::Ptr)?,
            "cqaeq" => self.handle_x86_int_compare_set(asm, "setae", OperandKind::Quad)?,
            "cib" => self.handle_x86_int_compare_set(asm, "setb", OperandKind::Int)?,
            "cbb" => self.handle_x86_int_compare_set(asm, "setb", OperandKind::Byte)?,
            "cpb" => self.handle_x86_int_compare_set(asm, "setb", OperandKind::Ptr)?,
            "cqb" => self.handle_x86_int_compare_set(asm, "setb", OperandKind::Quad)?,
            "cibeq" => self.handle_x86_int_compare_set(asm, "setbe", OperandKind::Int)?,
            "cbbeq" => self.handle_x86_int_compare_set(asm, "setbe", OperandKind::Byte)?,
            "cpbeq" => self.handle_x86_int_compare_set(asm, "setbe", OperandKind::Ptr)?,
            "cqbeq" => self.handle_x86_int_compare_set(asm, "setbe", OperandKind::Quad)?,
            "cigt" => self.handle_x86_int_compare_set(asm, "setg", OperandKind::Int)?,
            "cbgt" => self.handle_x86_int_compare_set(asm, "setg", OperandKind::Byte)?,
            "cpgt" => self.handle_x86_int_compare_set(asm, "setg", OperandKind::Ptr)?,
            "cqgt" => self.handle_x86_int_compare_set(asm, "setg", OperandKind::Quad)?,
            "cigteq" => self.handle_x86_int_compare_set(asm, "setge", OperandKind::Int)?,
            "cbgteq" => self.handle_x86_int_compare_set(asm, "setge", OperandKind::Byte)?,
            "cpgteq" => self.handle_x86_int_compare_set(asm, "setge", OperandKind::Ptr)?,
            "cqgteq" => self.handle_x86_int_compare_set(asm, "setge", OperandKind::Quad)?,
            "cilt" => self.handle_x86_int_compare_set(asm, "setl", OperandKind::Int)?,
            "cblt" => self.handle_x86_int_compare_set(asm, "setl", OperandKind::Byte)?,
            "cplt" => self.handle_x86_int_compare_set(asm, "setl", OperandKind::Ptr)?,
            "cqlt" => self.handle_x86_int_compare_set(asm, "setl", OperandKind::Quad)?,
            "cilteq" => self.handle_x86_int_compare_set(asm, "setle", OperandKind::Int)?,
            "cblteq" => self.handle_x86_int_compare_set(asm, "setle", OperandKind::Byte)?,
            "cplteq" => self.handle_x86_int_compare_set(asm, "setle", OperandKind::Ptr)?,
            "cqlteq" => self.handle_x86_int_compare_set(asm, "setle", OperandKind::Quad)?,
            "cfeq" => self.handle_x86_fp_compare_set(asm, OperandKind::Float, "eq", true)?,
            "cdeq" => self.handle_x86_fp_compare_set(asm, OperandKind::Double, "eq", true)?,
            "cfneq" => self.handle_x86_fp_compare_set(asm, OperandKind::Float, "setne", true)?,
            "cdneq" => self.handle_x86_fp_compare_set(asm, OperandKind::Double, "setne", true)?,
            "cfnequn" => self.handle_x86_fp_compare_set(asm, OperandKind::Float, "nequn", true)?,
            "cdnequn" => self.handle_x86_fp_compare_set(asm, OperandKind::Double, "nequn", true)?,
            "cfgt" => self.handle_x86_fp_compare_set(asm, OperandKind::Float, "seta", true)?,
            "cdgt" => self.handle_x86_fp_compare_set(asm, OperandKind::Double, "seta", true)?,
            "cfgteq" => self.handle_x86_fp_compare_set(asm, OperandKind::Float, "setae", true)?,
            "cdgteq" => self.handle_x86_fp_compare_set(asm, OperandKind::Double, "setae", true)?,
            "cflt" => self.handle_x86_fp_compare_set(asm, OperandKind::Float, "seta", false)?,
            "cdlt" => self.handle_x86_fp_compare_set(asm, OperandKind::Double, "seta", false)?,
            "cflteq" => self.handle_x86_fp_compare_set(asm, OperandKind::Float, "setae", false)?,
            "cdlteq" => self.handle_x86_fp_compare_set(asm, OperandKind::Double, "setae", false)?,
            "tis" => self.handle_x86_set_test(asm, "sets", OperandKind::Int)?,
            "tiz" => self.handle_x86_set_test(asm, "setz", OperandKind::Int)?,
            "tinz" => self.handle_x86_set_test(asm, "setnz", OperandKind::Int)?,
            "tps" => self.handle_x86_set_test(asm, "sets", OperandKind::Ptr)?,
            "tpz" => self.handle_x86_set_test(asm, "setz", OperandKind::Ptr)?,
            "tpnz" => self.handle_x86_set_test(asm, "setnz", OperandKind::Ptr)?,
            "tqs" => self.handle_x86_set_test(asm, "sets", OperandKind::Quad)?,
            "tqz" => self.handle_x86_set_test(asm, "setz", OperandKind::Quad)?,
            "tqnz" => self.handle_x86_set_test(asm, "setnz", OperandKind::Quad)?,
            "tbs" => self.handle_x86_set_test(asm, "sets", OperandKind::Byte)?,
            "tbz" => self.handle_x86_set_test(asm, "setz", OperandKind::Byte)?,
            "tbnz" => self.handle_x86_set_test(asm, "setnz", OperandKind::Byte)?,
            "peek" => self.handle_x86_peek(asm)?,
            "poke" => self.handle_x86_poke(asm)?,
            "cdqi" => asm.puts("cdq"),
            "cqoq" => asm.puts("cqo"),
            "idivi" => {
                let op = self.operands[0].x86_operand(OperandKind::Int)?;
                asm.puts(&format!(
                    "idiv{} {}",
                    Self::x86_suffix(OperandKind::Int),
                    op
                ));
            }
            "udivi" => {
                let op = self.operands[0].x86_operand(OperandKind::Int)?;
                asm.puts(&format!("div{} {}", Self::x86_suffix(OperandKind::Int), op));
            }
            "idivq" => {
                let op = self.operands[0].x86_operand(OperandKind::Quad)?;
                asm.puts(&format!(
                    "idiv{} {}",
                    Self::x86_suffix(OperandKind::Quad),
                    op
                ));
            }
            "udivq" => {
                let op = self.operands[0].x86_operand(OperandKind::Quad)?;
                asm.puts(&format!(
                    "div{} {}",
                    Self::x86_suffix(OperandKind::Quad),
                    op
                ));
            }
            "popcnti" => {
                let ops = self.x86_operands(&[OperandKind::Int, OperandKind::Int])?;
                asm.puts(&format!(
                    "popcnt{} {}",
                    Self::x86_suffix(OperandKind::Int),
                    ops
                ));
            }
            "popcntq" => {
                let ops = self.x86_operands(&[OperandKind::Quad, OperandKind::Quad])?;
                asm.puts(&format!(
                    "popcnt{} {}",
                    Self::x86_suffix(OperandKind::Quad),
                    ops
                ));
            }

            "tzcnti" => {
                self.handle_count_trailing_zeros(asm, OperandKind::Int)?;
            }

            "lzcnti" => {
                self.handle_count_leading_zeros(asm, OperandKind::Int)?;
            }

            "lzcntq" => {
                self.handle_count_leading_zeros(asm, OperandKind::Quad)?;
            }

            "fii2d" => {
                let op0 = self.operands[0].x86_operand(OperandKind::Int)?;
                let op2 = self.operands[2].x86_operand(OperandKind::Double)?;
                asm.puts(&format!("movd {}, {}", op0, op2));

                let op1 = self.operands[1].x86_operand(OperandKind::Int)?;
                asm.puts(&format!("movd {}, %xmm7", op1));

                asm.puts("psllq $32, %xmm7");
                asm.puts(&format!("por %xmm7, {}", op2));
            }

            "fd2ii" => {
                let op0 = self.operands[0].x86_operand(OperandKind::Double)?;
                let op1 = self.operands[1].x86_operand(OperandKind::Int)?;
                asm.puts(&format!("movd {}, {}", op0, op1));

                asm.puts(&format!("movsd {}, %xmm7", op0));
                asm.puts("psrlq $32, %xmm7");

                let op2 = self.operands[2].x86_operand(OperandKind::Int)?;
                asm.puts(&format!("movd %xmm7, {}", op2));
            }
            "fq2d" => {
                let ops = self.x86_operands(&[OperandKind::Quad, OperandKind::Double])?;
                asm.puts(&format!("movq {}", ops));
            }
            "fd2q" => {
                let ops = self.x86_operands(&[OperandKind::Double, OperandKind::Quad])?;
                asm.puts(&format!("movq {}", ops));
            }
            "fi2f" => {
                let ops = self.x86_operands(&[OperandKind::Int, OperandKind::Float])?;
                asm.puts(&format!("movd {}", ops));
            }

            "ff2i" => {
                let ops = self.x86_operands(&[OperandKind::Float, OperandKind::Int])?;
                asm.puts(&format!("movd {}", ops));
            }
            "bo" => {
                asm.puts(&format!("jo {}", self.operands[0].asm_label()?));
            }
            "bs" => {
                asm.puts(&format!("js {}", self.operands[0].asm_label()?));
            }
            "bz" => {
                asm.puts(&format!("jz {}", self.operands[0].asm_label()?));
            }
            "bnz" => {
                asm.puts(&format!("jnz {}", self.operands[0].asm_label()?));
            }
            "leai" => {
                Self::emit_x86_lea(asm, &self.operands[0], &self.operands[1], OperandKind::Int)?
            }
            "memfence" | "fence" => {
                let sp = RegisterId::for_name_str("sp");
                asm.puts(&format!(
                    "lock; orl $0, ({})",
                    sp.x86_operand(OperandKind::Ptr)?
                ));
            }

            "absf" => {
                let op0 = self.operands[0].x86_operand(OperandKind::Float)?;
                let op1 = self.operands[1].x86_operand(OperandKind::Float)?;
                let scratch = X86_SCRATCH_REGISTER.x86_operand(OperandKind::Int);
                asm.puts(&format!("movl $0x80000000, {}", scratch));
                asm.puts(&format!("movd {}, {}", scratch, op1));
                asm.puts(&format!("andnps {}, {}", op0, op1));
            }
            "absd" => {
                let op0 = self.operands[0].x86_operand(OperandKind::Double)?;
                let op1 = self.operands[1].x86_operand(OperandKind::Double)?;
                let scratch = X86_SCRATCH_REGISTER.x86_operand(OperandKind::Quad);
                asm.puts(&format!("movq $0x8000000000000000, {}", scratch));
                asm.puts(&format!("movd {}, {}", scratch, op1));
                asm.puts(&format!("andnps {}, {}", op0, op1));
            }
            "negf" => {
                let op0 = self.operands[0].x86_operand(OperandKind::Float)?;
                let op1 = self.operands[1].x86_operand(OperandKind::Float)?;
                let scratch = X86_SCRATCH_REGISTER.x86_operand(OperandKind::Int);
                asm.puts(&format!("movl $0x80000000, {}", scratch));
                asm.puts(&format!("movd {}, {}", scratch, op1));
                asm.puts(&format!("xorps {}, {}", op0, op1));
            }
            "negd" => {
                let op0 = self.operands[0].x86_operand(OperandKind::Double)?;
                let op1 = self.operands[1].x86_operand(OperandKind::Double)?;
                let scratch = RegisterId::for_name_str("X64_SCRATCH_REGISTER")
                    .x86_operand(OperandKind::Quad)?;
                asm.puts(&format!("movq $0x8000000000000000, {}", scratch));
                asm.puts(&format!("movd {}, {}", scratch, op1));
                asm.puts(&format!("xorpd {}, {}", op0, op1));
            }
            "atomicxchgaddb" => asm.puts(&format!(
                "lock xaddb {}",
                self.x86_operands(&[OperandKind::Byte, OperandKind::Byte])?
            )),
            "atomicxchgaddh" => asm.puts(&format!(
                "lock xaddh {}",
                self.x86_operands(&[OperandKind::Half, OperandKind::Half])?
            )),
            "atomicxchgaddi" => asm.puts(&format!(
                "lock xaddl {}",
                self.x86_operands(&[OperandKind::Int, OperandKind::Int])?
            )),
            "atomicxchgaddq" => asm.puts(&format!(
                "lock xaddq {}",
                self.x86_operands(&[OperandKind::Quad, OperandKind::Quad])?
            )),

            "atomicxchgsubb" => {
                asm.puts(&format!(
                    "negb {}",
                    self.operands[0].x86_operand(OperandKind::Byte)?
                ));
                asm.puts(&format!(
                    "lock xaddb {}",
                    self.x86_operands(&[OperandKind::Byte, OperandKind::Byte])?
                ))
            }
            "atomicxchgsubh" => {
                asm.puts(&format!(
                    "negh {}",
                    self.operands[0].x86_operand(OperandKind::Half)?
                ));
                asm.puts(&format!(
                    "lock xaddh {}",
                    self.x86_operands(&[OperandKind::Half, OperandKind::Half])?
                ))
            }

            "atomicxchgsubi" => {
                asm.puts(&format!(
                    "negl {}",
                    self.operands[0].x86_operand(OperandKind::Int)?
                ));
                asm.puts(&format!(
                    "lock xaddl {}",
                    self.x86_operands(&[OperandKind::Int, OperandKind::Int])?
                ))
            }

            "atomicxchgsubq" => {
                asm.puts(&format!(
                    "negq {}",
                    self.operands[0].x86_operand(OperandKind::Quad)?
                ));
                asm.puts(&format!(
                    "lock xaddq {}",
                    self.x86_operands(&[OperandKind::Quad, OperandKind::Quad])?
                ))
            }

            "atomicxchgb" => asm.puts(&format!(
                "xchgb {}",
                self.x86_operands(&[OperandKind::Byte, OperandKind::Byte])?
            )),

            "atomicxchgh" => asm.puts(&format!(
                "xchgh {}",
                self.x86_operands(&[OperandKind::Half, OperandKind::Half])?
            )),

            "atomicxchgi" => asm.puts(&format!(
                "xchgl {}",
                self.x86_operands(&[OperandKind::Int, OperandKind::Int])?
            )),

            "atomicxchgq" => asm.puts(&format!(
                "xchgq {}",
                self.x86_operands(&[OperandKind::Quad, OperandKind::Quad])?
            )),

            _ => self.lower_default(asm)?,
        }

        Ok(())
    }
}

impl Node {
    pub fn is_immediate_zero(&self) -> bool {
        match self {
            Self::Immediate(x) => x.value == 0,
            _ => false,
        }
    }

    pub fn is_immediate(&self) -> bool {
        matches!(self, Self::Immediate(_))
    }

    pub fn is_register_id(&self) -> bool {
        matches!(self, Self::RegisterId(_))
    }

    pub fn is_x86_gpr(&self, name: &str) -> bool {
        self.try_x86_gpr() == Some(name.to_string())
    }

    pub fn x86_operand(&self, kind: OperandKind) -> syn::Result<String> {
        match self {
            Self::SpecialRegister(x) => Ok(x.x86_operand(kind)),
            Self::Label(x) => Ok(format!("{}", x.name())),
            Self::LabelReference(x) => Ok(format!("{}", x.label.name())),
            Self::RegisterId(x) => Ok(x.x86_operand(kind)?),
            Self::FPRegisterId(x) => Ok(x.x86_operand(kind)?),
            Self::VecRegisterId(x) => Ok(x.x86_operand(kind)?),
            Self::Address(x) => Ok(x.x86_operand(kind)?),
            Self::AbsoluteAddress(x) => Ok(x.x86_operand(kind)?),
            Self::BaseIndex(x) => Ok(x.x86_operand(kind)?),
            Self::LocalLabel(x) => Ok(format!("{}", x.name)),
            Self::LocalLabelReference(x) => Ok(format!("{}", x.label.name)),
            Self::AsmOperand(x) => Ok(format!("${{_{}}}", x)),
            Self::Immediate(x) => Ok(format!("${}", x.value)),
            x => Err(syn::Error::new(
                Span::call_site(),
                &format!("invalid operand x86: {}", x),
            )),
        }
    }

    pub fn x86_call_operand(&self, kind: OperandKind) -> syn::Result<String> {
        match self {
            Self::Label(x) => Ok(format!("{}", x.name())),
            Self::LabelReference(x) => Ok(format!("{}", x.label.name())),
            Self::LocalLabel(x) => Ok(format!("{}", x.name)),
            Self::LocalLabelReference(x) => Ok(format!("{}", x.label.name)),
            Self::RegisterId(x) => Ok(x.x86_operand(kind)?),
            Self::Address(x) => Ok(x.x86_call_operand(kind)?),
            Self::AbsoluteAddress(x) => Ok(x.x86_call_operand(kind)?),
            Self::BaseIndex(x) => Ok(x.x86_call_operand(kind)?),
            _ => Err(syn::Error::new(Span::call_site(), "invalid operand")),
        }
    }

    pub fn x86_load_operand(
        &self,
        asm: &mut Assembler,
        kind: OperandKind,
        dst: &Node,
    ) -> syn::Result<String> {
        match self {
            Self::LabelReference(x) => x.x86_load_operand(asm, kind, dst),
            _ => self.x86_operand(kind),
        }
    }

    pub fn try_x86_gpr(&self) -> Option<String> {
        match self {
            Self::RegisterId(x) => x.x86_gpr().ok(),
            _ => None,
        }
    }

    pub fn x86_gpr(&self) -> syn::Result<String> {
        match self {
            Self::RegisterId(x) => x.x86_gpr(),
            _ => Err(syn::Error::new(Span::call_site(), "invalid operand")),
        }
    }

    pub fn asm_label(&self) -> syn::Result<String> {
        match self {
            Self::Label(x) => Ok(x.name().to_string()),
            Self::LocalLabel(x) => Ok(x.name.to_string()),
            Self::LabelReference(x) => Ok(x.label.name().to_string()),
            Self::LocalLabelReference(x) => Ok(x.label.name.to_string()),
            _ => Err(syn::Error::new(Span::call_site(), "invalid operand")),
        }
    }

    pub fn supports_8bit_on_x86(&self) -> syn::Result<bool> {
        match self {
            Self::RegisterId(x) => x.supports_8bit_on_x86(),
            Self::AbsoluteAddress(_) | Self::Address(_) | Self::BaseIndex(_) => Ok(true),
            _ => Err(syn::Error::new(Span::call_site(), "invalid operand")),
        }
    }

    pub fn immediate_value(&self) -> syn::Result<isize> {
        match self {
            Self::Immediate(x) => Ok(x.value),
            Self::AddImmediates(x) => Ok(x.left.immediate_value()? + x.right.immediate_value()?),
            Self::SubImmediates(x) => Ok(x.left.immediate_value()? - x.right.immediate_value()?),
            Self::MulImmediates(x) => Ok(x.left.immediate_value()? * x.right.immediate_value()?),
            Self::AndImmediate(x) => Ok(x.left.immediate_value()? & x.right.immediate_value()?),
            Self::OrImmediate(x) => Ok(x.left.immediate_value()? | x.right.immediate_value()?),
            Self::XorImmediate(x) => Ok(x.left.immediate_value()? ^ x.right.immediate_value()?),
            Self::BitNotImmediate(x) => Ok(!x.value.immediate_value()?),
            _ => Err(syn::Error::new(Span::call_site(), "invalid operand")),
        }
    }

    pub fn x86_address_operand(&self, kind: OperandKind) -> syn::Result<String> {
        match self {
            Self::Address(x) => x.x86_address_operand(kind),
            Self::AbsoluteAddress(x) => x.x86_address_operand(kind),
            Self::BaseIndex(x) => x.x86_address_operand(kind),
            _ => Err(syn::Error::new(Span::call_site(), "invalid operand")),
        }
    }
}
