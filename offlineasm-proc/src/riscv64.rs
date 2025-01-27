#![allow(unused_imports, dead_code)]
use std::cell::LazyCell;
use std::iter::Map;

use proc_macro2::Span;

use crate::asm::Assembler;
use crate::id;
use crate::opt::assign_registers_to_temporaries;
use crate::punc_from_vec;
use crate::x86::SpecialRegister;

/// # Naming conventions
///
/// - `x<number>` => GPR, used to operate with 32-bit and 64-bit integer values
/// - `f<number>` => FPR, used to operate with 32-bit and 64-bit floating-point values
///
/// # GPR conventions, to match the baseline JIT:
///
/// - `x0`  => not used (except where needed for operations) (RISC-V hard-wired zero register)
/// - `x1`  => la (through alias ra) (RISC-V return address register)
/// - `x2`  => sp (through alias sp) (RISC-V stack pointer register)
/// - `x3`  => not used (RISC-V global pointer register)
/// - `x4`  => not used (RISC-V thread pointer register)
/// - `x5`  => not used
/// - `x6`  => ws0
/// - `x7`  => ws1
/// - `x8`  => cfr (through alias fp) (RISC-V frame pointer register)
/// - `x9`  => csr0
/// - `x10` => t0, a0, wa0, r0
/// - `x11` => t1, a1, wa1, r1
/// - `x12` => t2, a2, wa2
/// - `x13` => t3, a3, wa3
/// - `x14` => t4, a4, wa4
/// - `x15` => t5, a5, wa5
/// - `x16` => t6, a6, wa6
/// - `x17` => t7, a7, wa7
/// - `x18` => csr1
/// - `x19` => csr2
/// - `x20` => csr3
/// - `x21` => csr4
/// - `x22` => csr5
/// - `x23` => csr6 (metadataTable)
/// - `x24` => csr7 (PB)
/// - `x25` => csr8 (numberTag)
/// - `x26` => csr9 (notCellMask)
/// - `x27` => csr10
/// - `x28` => scratch register
/// - `x29` => scratch register
/// - `x30` => scratch register
/// - `x31` => scratch register
///
/// # FPR conventions, to match the baseline JIT:
///
/// - `f0`  => ft0
/// - `f1`  => ft1
/// - `f2`  => ft2
/// - `f3`  => ft3
/// - `f4`  => ft4
/// - `f5`  => ft5
/// - `f6`  => not used
/// - `f7`  => not used
/// - `f8`  => csfr0
/// - `f9`  => csfr1
/// - `f10` => fa0, wfa0
/// - `f11` => fa1, wfa1
/// - `f12` => fa2, wfa2
/// - `f13` => fa3, wfa3
/// - `f14` => fa4, wfa4
/// - `f15` => fa5, wfa5
/// - `f16` => fa6, wfa6
/// - `f17` => fa7, wfa7
/// - `f18` => csfr2
/// - `f19` => csfr3
/// - `f20` => csfr4
/// - `f21` => csfr5
/// - `f22` => csfr6
/// - `f23` => csfr7
/// - `f24` => csfr8
/// - `f25` => csfr9
/// - `f26` => csfr10
/// - `f27` => csfr11
/// - `f28` => scratch register
/// - `f29` => scratch register
/// - `f30` => scratch register
/// - `f31` => scratch register
use super::ast::*;
use super::instructions::*;
use super::risc::*;

fn special(name: &str) -> Node {
    Node::SpecialRegister(SpecialRegister::new(&id(name)))
}

thread_local! {
    static RISCV64_EXTRA_GPRS: LazyCell<Vec<Node>> = LazyCell::new(|| {
        vec![
            special("x28"),
            special("x29"),
            special("x30"),
            special("x31")
        ]
    });

    static RISCV64_EXTRA_FPRS: LazyCell<Vec<Node>> = LazyCell::new(|| {
        vec![
            special("f28"),
            special("f29"),
            special("f30"),
            special("f31")
        ]
    });
}

pub fn riscv64_operand_types<'a>(
    operands: impl Iterator<Item = &'a Node>,
) -> Map<impl Iterator<Item = &'a Node>, fn(&'a Node) -> OperandType> {
    operands.map(|operand| match operand {
        Node::RegisterId(_) => OperandType::RegisterId,
        Node::FPRegisterId(_) => OperandType::FPRegisterId,
        Node::VecRegisterId(_) => OperandType::VecRegisterId,
        Node::Immediate(_) => OperandType::Immediate,
        Node::LabelReference(_) => OperandType::LabelReference,
        Node::LocalLabelReference(_) => OperandType::LocalLabelReference,
        Node::Address(_) => OperandType::Address,
        Node::BaseIndex(_) => OperandType::BaseIndex,
        Node::AbsoluteAddress(_) => OperandType::AbsoluteAddress,
        Node::Tmp(tmp) => {
            if tmp.kind == TmpKind::Gpr {
                OperandType::RegisterId
            } else {
                OperandType::FPRegisterId
            }
        }
        Node::SpecialRegister(reg) => {
            if reg.name == "x28" || reg.name == "x29" || reg.name == "x30" || reg.name == "x31" {
                OperandType::RegisterId
            } else if reg.name == "f28"
                || reg.name == "f29"
                || reg.name == "f30"
                || reg.name == "f31"
            {
                OperandType::FPRegisterId
            } else {
                panic!("Invalid special register: {}", reg.name);
            }
        }

        _ => panic!("Invalid operand: {}", operand),
    })
}

pub fn riscv64_validate_operands<'a>(
    operands: impl Iterator<Item = &'a Node>,
    expected: &[OperandType],
) -> syn::Result<()> {
    let actual = riscv64_operand_types(operands);
    for (i, actual) in actual.enumerate() {
        if i >= expected.len() {
            return Err(syn::Error::new(
                Span::call_site(),
                format!("Too many operands"),
            ));
        }
        if actual != expected[i] {
            return Err(syn::Error::new(
                Span::call_site(),
                format!(
                    "Invalid operand type at index {}: expected {:?}, got {:?}",
                    i, expected[i], actual
                ),
            ));
        }
    }
    Ok(())
}

#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Copy, Debug)]
pub enum IValidate {
    IImmediate,
    AnyImmediate,
    RV32Shift,
    RV64Shift,
}

pub fn riscv64_validate_immediate(validation: IValidate, immediate: isize) -> bool {
    match validation {
        IValidate::IImmediate => (-0x800..0x7ff).contains(&immediate),
        IValidate::AnyImmediate => true,
        IValidate::RV32Shift => (0..31).contains(&immediate),
        IValidate::RV64Shift => (0..63).contains(&immediate),
    }
}

impl RegisterId {
    pub fn riscv64_operand(&self) -> syn::Result<String> {
        let name = self.name.to_string();
        Ok(match name.as_str() {
            "t0" | "a0" | "wa0" | "r0" => "x10".to_string(),
            "t1" | "a1" | "wa1" | "r1" => "x11".to_string(),
            "t2" | "a2" | "wa2" => "x12".to_string(),
            "t3" | "a3" | "wa3" => "x13".to_string(),
            "t4" | "a4" | "wa4" => "x14".to_string(),
            "t5" | "a5" | "wa5" => "x15".to_string(),
            "t6" | "a6" | "wa6" => "x16".to_string(),
            "t7" | "a7" | "wa7" => "x17".to_string(),
            "ws0" => "x6".to_string(),
            "ws1" => "x7".to_string(),
            "csr0" => "x9".to_string(),
            "csr1" => "x18".to_string(),
            "csr2" => "x19".to_string(),
            "csr3" => "x20".to_string(),
            "csr4" => "x21".to_string(),
            "csr5" => "x22".to_string(),
            "csr6" => "x23".to_string(),
            "csr7" => "x24".to_string(),
            "csr8" => "x25".to_string(),
            "csr9" => "x26".to_string(),
            "csr10" => "x27".to_string(),
            "lr" => "ra".to_string(),
            "sp" => "sp".to_string(),
            "cfr" => "fp".to_string(),
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("Bad register name {}", name),
                ))
            }
        })
    }
}

impl FPRegisterId {
    pub fn riscv64_operand(&self) -> syn::Result<String> {
        let name = self.name.to_string();
        Ok(match name.as_str() {
            "ft0" => "f0".to_string(),
            "ft1" => "f1".to_string(),
            "ft2" => "f2".to_string(),
            "ft3" => "f3".to_string(),
            "ft4" => "f4".to_string(),
            "ft5" => "f5".to_string(),
            "csfr0" => "f8".to_string(),
            "csfr1" => "f9".to_string(),
            "fa0" | "wfa0" => "f10".to_string(),
            "fa1" | "wfa1" => "f11".to_string(),
            "fa2" | "wfa2" => "f12".to_string(),
            "fa3" | "wfa3" => "f13".to_string(),
            "fa4" | "wfa4" => "f14".to_string(),
            "fa5" | "wfa5" => "f15".to_string(),
            "fa6" | "wfa6" => "f16".to_string(),
            "fa7" | "wfa7" => "f17".to_string(),
            "csfr2" => "f18".to_string(),
            "csfr3" => "f19".to_string(),
            "csfr4" => "f20".to_string(),
            "csfr5" => "f21".to_string(),
            "csfr6" => "f22".to_string(),
            "csfr7" => "f23".to_string(),
            "csfr8" => "f24".to_string(),
            "csfr9" => "f25".to_string(),
            "csfr10" => "f26".to_string(),
            "csfr11" => "f27".to_string(),
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("Bad register name {}", name),
                ))
            }
        })
    }
}

impl SpecialRegister {
    pub fn riscv64_operand(&self) -> syn::Result<String> {
        Ok(self.name.to_string())
    }
}

impl Immediate {
    pub fn riscv64_operand(&self, validation: IValidate) -> syn::Result<String> {
        if self.riscv64_requires_load(validation) {
            return Err(syn::Error::new(
                Span::call_site(),
                format!("Immediate value {} requires loading", self.value),
            ));
        }
        Ok(self.value.to_string())
    }

    pub fn riscv64_requires_load(&self, validation: IValidate) -> bool {
        !riscv64_validate_immediate(validation, self.value)
    }
}

impl Address {
    pub fn riscv64_operand(&self) -> syn::Result<String> {
        Ok(format!(
            "{}({})",
            self.offset.riscv64_operand()?,
            self.base.riscv64_operand()?
        ))
    }

    pub fn riscv64_requires_load(&self) -> bool {
        self.offset.riscv64_requires_load(IValidate::IImmediate)
    }
}

#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Copy, Debug)]
pub enum RISCV64RoundingMode {
    Floor,
    Ceil,
    Round,
    Truncate,
}

impl RISCV64RoundingMode {
    pub fn riscv64_rounding_mode(&self) -> &'static str {
        match self {
            Self::Floor => "rdn",
            Self::Ceil => "rup",
            Self::Round => "rne",
            Self::Truncate => "rtz",
        }
    }
}

#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Copy, Debug)]
pub enum RISCV64MemoryOrdering {
    Rw,
    IoRw,
}

impl RISCV64MemoryOrdering {
    pub fn riscv64_memory_ordering(&self) -> &'static str {
        match self {
            Self::Rw => "rw",
            Self::IoRw => "iorw",
        }
    }
}

#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Copy, Debug)]
enum RV64Size {
    B,
    H,
    I,
    P,
    Q,
    BSI,
    BSQ,
    HSI,
    HSQ,
    IS,
}

impl RV64Size {
    pub fn from_str(s: &str) -> (RV64Size, &str) {
        let size = s.chars().next().unwrap();
        let suffix = &s[1..];

        match size {
            'b' => match suffix {
                x if x.starts_with("si") => (RV64Size::BSI, &suffix[2..]),
                x if x.starts_with("sq") => (RV64Size::BSQ, &suffix[2..]),
                _ => (RV64Size::B, suffix),
            },
            'h' => match suffix {
                x if x.starts_with("si") => (RV64Size::HSI, &suffix[2..]),
                x if x.starts_with("sq") => (RV64Size::HSQ, &suffix[2..]),
                _ => (RV64Size::H, suffix),
            },
            'i' => match suffix {
                x if x.starts_with("s") => (RV64Size::IS, &suffix[1..]),
                _ => (RV64Size::I, suffix),
            },
            'p' => (RV64Size::P, suffix),
            'q' => (RV64Size::Q, suffix),
            _ => (RV64Size::B, s),
        }
    }
}

fn riscv64_lower_emit_mask(
    new_list: &mut Vec<Node>,
    node: &Instruction,
    size: RV64Size,
    source: Node,
    destination: Node,
) {
    match size {
        RV64Size::B | RV64Size::H | RV64Size::I => {
            let shift_size = match size {
                RV64Size::B => 56,
                RV64Size::H => 48,
                RV64Size::I => 32,
                _ => 0,
            };

            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_slli"),
                operands: punc_from_vec(vec![
                    destination.clone(),
                    source.clone(),
                    Node::Immediate(Immediate { value: shift_size }),
                ]),
                ..Default::default()
            }));

            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_srli"),
                operands: punc_from_vec(vec![
                    destination.clone(),
                    destination.clone(),
                    Node::Immediate(Immediate { value: shift_size }),
                ]),
                ..Default::default()
            }));
        }

        _ => (),
    }
}

fn riscv64_lower_emit_sign_extension(
    new_list: &mut Vec<Node>,
    node: &Instruction,
    size: RV64Size,
    source: Node,
    destination: Node,
) {
    match size {
        RV64Size::B | RV64Size::H => {
            let shift_size = match size {
                RV64Size::B => 56,
                RV64Size::H => 48,
                _ => 0,
            };

            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_slli"),
                operands: punc_from_vec(vec![
                    destination.clone(),
                    source.clone(),
                    Node::Immediate(Immediate { value: shift_size }),
                ]),
                ..Default::default()
            }));
            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_srai"),
                operands: punc_from_vec(vec![
                    destination.clone(),
                    destination.clone(),
                    Node::Immediate(Immediate { value: shift_size }),
                ]),
                ..Default::default()
            }));
        }

        RV64Size::I => {
            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_sext.w"),
                operands: punc_from_vec(vec![destination.clone(), source.clone()]),
                ..Default::default()
            }));
        }

        _ => (),
    }
}

fn riscv64_lower_operand_into_register(
    new_list: &mut Vec<Node>,
    node: &Instruction,
    operand: &Node,
) -> syn::Result<Node> {
    let mut register = operand.clone();
    if operand.is_immediate() {
        register = Node::Tmp(Tmp::new(TmpKind::Gpr));
        new_list.push(Node::Instruction(Instruction {
            opcode: id("rv_li"),
            operands: punc_from_vec(vec![register.clone(), operand.clone()]),
            ..Default::default()
        }));
    }

    if !riscv64_operand_types(std::iter::once(operand)).all(|x| x == OperandType::RegisterId) {
        return Err(syn::Error::new(
            Span::call_site(),
            format!("Invalid register type: {}", operand),
        ));
    }

    Ok(register)
}

fn riscv64_lower_operand_into_register_and_sign_extend(
    new_list: &mut Vec<Node>,
    node: &Instruction,
    operand: &Node,
    size: RV64Size,
    forced_tmp: Option<TmpKind>,
) -> syn::Result<Node> {
    let source = riscv64_lower_operand_into_register(new_list, node, operand)?;
    let mut destination = source.clone();

    if (matches!(size, RV64Size::B | RV64Size::H | RV64Size::I) || forced_tmp.is_some())
        && !matches!(destination, Node::Tmp(_))
    {
        destination = Node::Tmp(Tmp::new(forced_tmp.unwrap_or(TmpKind::Gpr)));
    }

    riscv64_lower_emit_sign_extension(new_list, node, size, source, destination.clone());
    Ok(destination)
}

fn riscv64_lower_misplaced_address(list: &Vec<Node>) -> syn::Result<Vec<Node>> {
    let mut new_list = Vec::new();

    for node in list.iter() {
        match node {
            Node::Instruction(ins) => {
                let opcode = ins.opcode.to_string();
                if opcode.starts_with("baddi")
                    || opcode.starts_with("bsubi")
                        && (opcode.ends_with("z")
                            || opcode.ends_with("nz")
                            || opcode.ends_with("s"))
                {
                    let op = &opcode[1..4];
                    let result: Vec<OperandType> =
                        riscv64_operand_types(ins.operands.iter()).collect();

                    match result.as_slice() {
                        [OperandType::Address, OperandType::Immediate, OperandType::LocalLabelReference] =>
                        {
                            let tmp = Node::Tmp(Tmp::new(TmpKind::Gpr));
                            new_list.push(Node::Instruction(Instruction {
                                opcode: id("loadi"),
                                operands: punc_from_vec(vec![tmp.clone(), ins.operands[0].clone()]),
                                ..Default::default()
                            }));
                            new_list.push(Node::Instruction(Instruction {
                                opcode: id(&format!("{}i", op)),
                                operands: punc_from_vec(vec![
                                    tmp.clone(),
                                    tmp.clone(),
                                    ins.operands[1].clone(),
                                ]),
                                ..Default::default()
                            }));
                            new_list.push(Node::Instruction(Instruction {
                                opcode: id("storei"),
                                operands: punc_from_vec(vec![ins.operands[0].clone(), tmp.clone()]),
                                ..Default::default()
                            }));
                            let bt_code = &opcode[5..];
                            new_list.push(Node::Instruction(Instruction {
                                opcode: id(&format!("bti{}", bt_code)),
                                operands: punc_from_vec(vec![tmp, ins.operands[2].clone()]),
                                ..Default::default()
                            }));
                        }

                        _ => new_list.push(node.clone()),
                    }
                } else {
                    new_list.push(node.clone());
                }
            }
            _ => new_list.push(node.clone()),
        }
    }

    Ok(new_list)
}

// lower leai and leap into RISC style
fn riscv64_lower_address_loads(list: &Vec<Node>) -> syn::Result<Vec<Node>> {
    let mut new_list = Vec::new();

    for node in list.iter() {
        match node {
            Node::Instruction(ins) => {
                if ins.opcode == "leap" || ins.opcode == "leai" {
                    let operands: Vec<OperandType> =
                        riscv64_operand_types(ins.operands.iter()).collect();
                    match operands.as_slice() {
                        [OperandType::RegisterId, OperandType::Address] => {
                            let (dest, address) = (&ins.operands[0], &ins.operands[1]);
                            let address = address.as_address().unwrap();
                            if address.riscv64_requires_load() {
                                return Err(syn::Error::new(
                                    Span::call_site(),
                                    format!(
                                        "Invalid address: address {} requires loading",
                                        address
                                    ),
                                ));
                            }

                            new_list.push(Node::Instruction(Instruction {
                                opcode: id("rv_addi"),
                                operands: punc_from_vec(vec![
                                    dest.clone(),
                                    (*address.base).clone(),
                                    (*address.offset).clone(),
                                ]),
                                ..Default::default()
                            }));
                        }

                        [OperandType::RegisterId, OperandType::BaseIndex] => {
                            let (bi, dest) = (&ins.operands[1], &ins.operands[0]);
                            let bi = bi.as_base_index().unwrap();

                            new_list.push(Node::Instruction(Instruction {
                                opcode: id("rv_slli"),
                                operands: punc_from_vec(vec![
                                    dest.clone(),
                                    (*bi.index).clone(),
                                    (*bi.scale).clone(),
                                ]),
                                ..Default::default()
                            }));

                            if !bi.offset.is_immediate_zero() {
                                if bi.offset.riscv64_requires_load(IValidate::IImmediate) {
                                    let tmp = Node::Tmp(Tmp::new(TmpKind::Gpr));
                                    // rv_li tmp, bi.offset
                                    // rv_add dest, tmp, dest
                                    new_list.push(Node::Instruction(Instruction {
                                        opcode: id("rv_li"),
                                        operands: punc_from_vec(vec![
                                            tmp.clone(),
                                            (*bi.offset).clone(),
                                        ]),
                                        ..Default::default()
                                    }));
                                    new_list.push(Node::Instruction(Instruction {
                                        opcode: id("rv_add"),
                                        operands: punc_from_vec(vec![
                                            dest.clone(),
                                            tmp.clone(),
                                            dest.clone(),
                                        ]),
                                        ..Default::default()
                                    }));
                                } else {
                                    // rv_addi dest, dest, offset
                                    new_list.push(Node::Instruction(Instruction {
                                        opcode: id("rv_addi"),
                                        operands: punc_from_vec(vec![
                                            dest.clone(),
                                            dest.clone(),
                                            (*bi.offset).clone(),
                                        ]),
                                        ..Default::default()
                                    }));
                                }
                            }
                        }

                        [OperandType::RegisterId, OperandType::LabelReference] => {
                            let (dest, label) = (&ins.operands[0], &ins.operands[1]);
                            let label = label.as_label_reference().unwrap();
                            // rv_la dest, label
                            new_list.push(Node::Instruction(Instruction {
                                opcode: id("rv_la"),
                                operands: punc_from_vec(vec![
                                    dest.clone(),
                                    Node::LabelReference(label.clone()),
                                ]),
                                ..Default::default()
                            }));

                            if label.offset != 0 {
                                let offset = Node::Immediate(Immediate {
                                    value: label.offset,
                                });
                                if offset.riscv64_requires_load(IValidate::IImmediate) {
                                    let tmp = Node::Tmp(Tmp::new(TmpKind::Gpr));
                                    new_list.push(Node::Instruction(Instruction {
                                        opcode: id("rv_li"),
                                        operands: punc_from_vec(vec![tmp.clone(), offset.clone()]),
                                        ..Default::default()
                                    }));
                                    new_list.push(Node::Instruction(Instruction {
                                        opcode: id("rv_add"),
                                        operands: punc_from_vec(vec![
                                            dest.clone(),
                                            tmp.clone(),
                                            dest.clone(),
                                        ]),
                                        ..Default::default()
                                    }));
                                } else {
                                    new_list.push(Node::Instruction(Instruction {
                                        opcode: id("rv_addi"),
                                        operands: punc_from_vec(vec![
                                            dest.clone(),
                                            dest.clone(),
                                            offset.clone(),
                                        ]),
                                        ..Default::default()
                                    }));
                                }
                            }
                        }

                        _ => new_list.push(node.clone()),
                    }
                } else {
                    new_list.push(node.clone());
                }
            }

            _ => new_list.push(node.clone()),
        }
    }

    Ok(new_list)
}

fn riscv64_lower_immediate_sub(list: &Vec<Node>) -> syn::Result<Vec<Node>> {
    fn emit(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        size: RV64Size,
        operands: &syn::punctuated::Punctuated<Node, syn::token::Comma>,
    ) -> syn::Result<()> {
        if operands.len() == 3 {
            riscv64_validate_operands(
                operands.iter(),
                &[
                    OperandType::RegisterId,
                    OperandType::RegisterId,
                    OperandType::Immediate,
                ],
            )?;
        } else {
            riscv64_validate_operands(
                operands.iter(),
                &[OperandType::RegisterId, OperandType::Immediate],
            )?;
        }
        let nimmediate = Immediate {
            value: operands[2].immediate_value()?.wrapping_neg(),
        };

        if nimmediate.riscv64_requires_load(IValidate::IImmediate) {
            let tmp = Node::Tmp(Tmp::new(TmpKind::Gpr));
            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_li"),
                operands: punc_from_vec(vec![tmp.clone(), operands[2].clone()]),
                ..Default::default()
            }));

            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_sub"),
                operands: punc_from_vec(vec![
                    operands[0].clone(),
                    tmp.clone(),
                    operands[1].clone(),
                ]),
                ..Default::default()
            }));
        } else {
            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_subi"),
                operands: punc_from_vec(vec![
                    operands[0].clone(),
                    operands[1].clone(),
                    Node::Immediate(nimmediate),
                ]),
                ..Default::default()
            }));
        }

        riscv64_lower_emit_mask(
            new_list,
            node,
            size,
            operands[0].clone(),
            operands[0].clone(),
        );
        Ok(())
    }

    let mut new_list = Vec::new();

    for node in list.iter() {
        match node {
            Node::Instruction(ins) => {
                if ins.opcode == "subi" || ins.opcode == "subq" || ins.opcode == "subp" {
                    let size = if ins.opcode == "subi" {
                        RV64Size::I
                    } else if ins.opcode == "subq" {
                        RV64Size::Q
                    } else {
                        RV64Size::P
                    };
                    let operand_kinds: Vec<OperandType> =
                        riscv64_operand_types(ins.operands.iter()).collect();
                    match operand_kinds.as_slice() {
                        [OperandType::RegisterId, OperandType::RegisterId, OperandType::Immediate] =>
                        {
                            emit(&mut new_list, ins, size, &ins.operands)?;
                        }
                        [OperandType::RegisterId, OperandType::Immediate] => {
                            emit(&mut new_list, ins, size, &ins.operands)?;
                        }
                        _ => new_list.push(node.clone()),
                    }
                } else {
                    new_list.push(node.clone());
                }
            }
            _ => new_list.push(node.clone()),
        }
    }

    Ok(new_list)
}

pub fn riscv64_lower_operation(list: &Vec<Node>) -> syn::Result<Vec<Node>> {
    fn emit_load_operation(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        size: RV64Size,
    ) -> syn::Result<()> {
        riscv64_validate_operands(
            node.operands.iter(),
            &[OperandType::RegisterId, OperandType::Address],
        )?;

        let suffix = match size {
            RV64Size::B => "bu",
            RV64Size::BSI | RV64Size::BSQ => "b",
            RV64Size::H => "hu",
            RV64Size::HSI | RV64Size::HSQ => "h",
            RV64Size::IS => "w",
            RV64Size::I => "w",
            RV64Size::Q => "d",
            RV64Size::P => "d",
        };

        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_l{suffix}")),
            operands: node.operands.clone(),
            ..Default::default()
        }));

        match size {
            RV64Size::BSI | RV64Size::BSQ => riscv64_lower_emit_mask(
                new_list,
                node,
                RV64Size::I,
                node.operands[0].clone(),
                node.operands[0].clone(),
            ),
            _ => (),
        }
        Ok(())
    }

    fn emit_store_operation(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        size: RV64Size,
    ) -> syn::Result<()> {
        riscv64_validate_operands(
            node.operands.iter(),
            &[OperandType::Address, OperandType::RegisterId],
        )?;

        let suffix = match size {
            RV64Size::B => "bu",
            RV64Size::BSI | RV64Size::BSQ => "b",
            RV64Size::H => "h",
            RV64Size::HSI | RV64Size::HSQ => "h",
            RV64Size::IS => "w",
            RV64Size::I => "w",
            RV64Size::Q => "d",
            RV64Size::P => "d",
        };

        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_s{suffix}")),
            operands: node.operands.clone(),
            ..Default::default()
        }));

        Ok(())
    }

    fn emit_move_operation(new_list: &mut Vec<Node>, node: &Instruction) -> syn::Result<()> {
        let optypes: Vec<OperandType> = riscv64_operand_types(node.operands.iter()).collect();

        match optypes.as_slice() {
            [OperandType::RegisterId, OperandType::RegisterId] => {
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_mv"),
                    operands: node.operands.clone(),
                    ..Default::default()
                }));
            }

            [OperandType::RegisterId, OperandType::Immediate] => {
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_li"),
                    operands: node.operands.clone(),
                    ..Default::default()
                }));
            }
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("Invalid operands for move operation: {:?}", optypes),
                ))
            }
        }
        Ok(())
    }

    fn emit_jump(new_list: &mut Vec<Node>, node: &Instruction) -> syn::Result<()> {
        let op = match riscv64_operand_types(node.operands.iter()).next().unwrap() {
            OperandType::RegisterId => "jr",
            OperandType::LabelReference | OperandType::LocalLabelReference => "tail",
            operand => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("Invalid operand for jump operation: {:?}", operand),
                ))
            }
        };
        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_{}", op)),
            operands: node.operands.clone(),
            ..Default::default()
        }));
        Ok(())
    }

    fn emit_call(new_list: &mut Vec<Node>, node: &Instruction) -> syn::Result<()> {
        let op = match riscv64_operand_types(node.operands.iter()).next().unwrap() {
            OperandType::LabelReference | OperandType::LocalLabelReference => "call",
            OperandType::RegisterId => "jalr",
            operand => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("Invalid operand for call operation: {:?}", operand),
                ))
            }
        };

        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_{}", op)),
            operands: node.operands.clone(),
            ..Default::default()
        }));

        Ok(())
    }

    fn emit_push(new_list: &mut Vec<Node>, node: &Instruction) -> syn::Result<()> {
        let sp = RegisterId::for_name(&id("sp"));
        let size = 8 * node.operands.len();

        // Adjust stack pointer
        new_list.push(Node::Instruction(Instruction {
            opcode: id("rv_addi"),
            operands: punc_from_vec(vec![
                Node::RegisterId(sp.clone()),
                Node::Immediate(Immediate {
                    value: -(size as isize),
                }),
                Node::RegisterId(sp.clone()),
            ]),
            ..Default::default()
        }));

        // Store operands in reverse order
        for (index, op) in node.operands.iter().rev().enumerate() {
            let offset = size - 8 * (index + 1);
            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_sd"),
                operands: punc_from_vec(vec![
                    op.clone(),
                    Node::Address(Address {
                        base: Box::new(Node::RegisterId(sp.clone())),
                        offset: Box::new(Node::Immediate(Immediate {
                            value: offset as isize,
                        })),
                    }),
                ]),
                ..Default::default()
            }));
        }

        Ok(())
    }

    fn emit_pop(new_list: &mut Vec<Node>, node: &Instruction) -> syn::Result<()> {
        let sp = RegisterId::for_name(&id("sp"));
        let size = 8 * node.operands.len();

        // Load operands in order
        for (index, op) in node.operands.iter().enumerate() {
            let offset = size - 8 * (index + 1);
            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_ld"),
                operands: punc_from_vec(vec![
                    Node::Address(Address {
                        base: Box::new(Node::RegisterId(sp.clone())),
                        offset: Box::new(Node::Immediate(Immediate {
                            value: offset as isize,
                        })),
                    }),
                    op.clone(),
                ]),
                ..Default::default()
            }));
        }

        // Adjust stack pointer
        new_list.push(Node::Instruction(Instruction {
            opcode: id("rv_addi"),
            operands: punc_from_vec(vec![
                Node::RegisterId(sp.clone()),
                Node::Immediate(Immediate {
                    value: size as isize,
                }),
                Node::RegisterId(sp.clone()),
            ]),
            ..Default::default()
        }));

        Ok(())
    }

    fn emit_addition_operation(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        is_add: bool,
        size: RV64Size,
    ) -> syn::Result<()> {
        let mut operands = node.operands.clone();

        // Handle 2-operand case by duplicating first operand
        if operands.len() == 2 {
            operands = punc_from_vec(vec![
                operands[0].clone(),
                operands[0].clone(),
                operands[1].clone(),
            ]);
        }

        // Check operand types
        let operand_types: Vec<OperandType> = riscv64_operand_types(operands.iter()).collect();

        // Handle immediate-in-middle pattern
        if operand_types.as_slice()
            == [
                OperandType::RegisterId,
                OperandType::Immediate,
                OperandType::RegisterId,
            ]
        {
            if !is_add {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "Invalid subtraction pattern",
                ));
            }
            operands = punc_from_vec(vec![
                operands[0].clone(),
                operands[2].clone(),
                operands[1].clone(),
            ]);
        }

        // Build opcode
        let mut addition_opcode = if is_add {
            "add".to_string()
        } else {
            "sub".to_string()
        };

        if operands[2].is_immediate() {
            addition_opcode.push('i');
        }

        if size == RV64Size::I {
            addition_opcode.push('w');
        }

        // Emit instruction
        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_{}", addition_opcode)),
            operands: operands.clone(),
            ..Default::default()
        }));

        // Emit mask if needed
        riscv64_lower_emit_mask(
            new_list,
            node,
            size,
            operands[0].clone(),
            operands[0].clone(),
        );

        Ok(())
    }

    fn emit_multiplication_operation(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        operation: &str,
        size: RV64Size,
        signedness: &str,
    ) -> syn::Result<()> {
        let mut operands = node.operands.clone();

        // Handle 2-operand case
        if operands.len() == 2 {
            operands = punc_from_vec(vec![
                operands[0].clone(),
                operands[0].clone(),
                operands[1].clone(),
            ]);
        }

        // Handle immediate-in-middle pattern
        let operand_types: Vec<OperandType> = riscv64_operand_types(operands.iter()).collect();
        if operand_types.as_slice()
            == [
                OperandType::RegisterId,
                OperandType::Immediate,
                OperandType::RegisterId,
            ]
        {
            if operation == "div" || operation == "rem" {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "Invalid division/remainder pattern",
                ));
            }
            operands = punc_from_vec(vec![
                operands[0].clone(),
                operands[2].clone(),
                operands[1].clone(),
            ]);
        }

        // Build opcode
        let mut multiplication_opcode = match operation {
            "mul" => "mul".to_string(),
            "div" | "rem" => format!("{}{}", operation, if signedness != "s" { "u" } else { "" }),
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("Invalid operation {}", operation),
                ))
            }
        };

        // Add size suffix
        if size == RV64Size::I {
            multiplication_opcode.push('w');
        }

        // Emit instruction
        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_{}", multiplication_opcode)),
            operands: operands.clone(),
            ..Default::default()
        }));

        // Emit mask if needed
        riscv64_lower_emit_mask(
            new_list,
            node,
            size,
            operands[0].clone(),
            operands[0].clone(),
        );

        Ok(())
    }

    fn riscv64_emit_shift_operation(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        operation: &str,
        size: RV64Size,
    ) -> syn::Result<()> {
        let mut operands = node.operands.clone();

        // Handle 2-operand case by duplicating the second operand
        if operands.len() == 2 {
            operands = punc_from_vec(vec![
                operands[0].clone(),
                operands[0].clone(),
                operands[1].clone(),
            ]);
        }

        // Determine shift opcode
        let mut shift_opcode = match operation {
            "l" => "sll",
            "r" => "sra",
            "ur" => "srl",
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("Invalid shift operation {}", operation),
                ))
            }
        }
        .to_string();

        // Add immediate suffix if needed
        if matches!(operands[2], Node::Immediate(_)) {
            shift_opcode.push('i');
        }

        // Add size suffix
        if size == RV64Size::I {
            shift_opcode.push('w');
        }

        // Emit instruction
        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_{}", shift_opcode)),
            operands: operands.clone(),
            ..Default::default()
        }));

        // Emit mask if needed
        riscv64_lower_emit_mask(
            new_list,
            node,
            size,
            operands[2].clone(),
            operands[2].clone(),
        );

        Ok(())
    }

    fn riscv64_emit_rotate_operation(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        direction: &str,
        size: RV64Size,
    ) -> syn::Result<()> {
        // Validate operands
        riscv64_validate_operands(
            node.operands.iter(),
            &[OperandType::RegisterId, OperandType::RegisterId],
        )?;

        let lhs = node.operands[0].clone();
        let rhs = node.operands[1].clone();

        // Determine bit size and suffix based on size
        let (bits, suffix) = match size {
            RV64Size::I => (32, "w"),
            RV64Size::Q => (64, ""),
            _ => unreachable!(),
        };

        // Create temporary registers
        let inverse_amount = Node::Tmp(Tmp::new(TmpKind::Gpr));
        let real_amount = Node::Tmp(Tmp::new(TmpKind::Gpr));
        let left_register = Node::Tmp(Tmp::new(TmpKind::Gpr));
        let right_register = Node::Tmp(Tmp::new(TmpKind::Gpr));

        // Emit instructions for rotate operation
        new_list.push(Node::Instruction(Instruction {
            opcode: id("rv_li"),
            operands: punc_from_vec(vec![
                inverse_amount.clone(),
                Node::Immediate(Immediate {
                    value: bits as isize,
                }),
            ]),
            ..Default::default()
        }));

        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_rem{}", suffix)),
            operands: punc_from_vec(vec![
                real_amount.clone(),
                inverse_amount.clone(),
                rhs.clone(),
            ]),
            ..Default::default()
        }));

        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_sub{}", suffix)),
            operands: punc_from_vec(vec![
                inverse_amount.clone(),
                inverse_amount.clone(),
                real_amount.clone(),
            ]),
            ..Default::default()
        }));

        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_sll{}", suffix)),
            operands: punc_from_vec(vec![
                left_register.clone(),
                lhs.clone(),
                if direction == "l" {
                    real_amount.clone()
                } else {
                    inverse_amount.clone()
                },
            ]),
            ..Default::default()
        }));

        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_srl{}", suffix)),
            operands: punc_from_vec(vec![
                right_register.clone(),
                lhs.clone(),
                if direction == "l" {
                    inverse_amount.clone()
                } else {
                    real_amount.clone()
                },
            ]),
            ..Default::default()
        }));

        new_list.push(Node::Instruction(Instruction {
            opcode: id("rv_or"),
            operands: punc_from_vec(vec![
                lhs.clone(),
                left_register.clone(),
                right_register.clone(),
            ]),
            ..Default::default()
        }));

        Ok(())
    }

    fn emit_logical_operation(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        operation: &str,
        size: RV64Size,
    ) -> syn::Result<()> {
        let mut operands = node.operands.clone();
        if operands.len() == 2 {
            operands = punc_from_vec(vec![
                operands[0].clone(),
                operands[0].clone(),
                operands[1].clone(),
            ]);
        }

        let logical_opcode = match operation {
            "and" | "or" | "xor" => operation.to_string(),
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("Invalid operation: {}", operation),
                ))
            }
        };

        let final_opcode = if operands[1].is_immediate() {
            format!("{}i", logical_opcode)
        } else {
            logical_opcode
        };

        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_{}", final_opcode)),
            operands: operands.clone(),
            ..Default::default()
        }));

        riscv64_lower_emit_mask(
            new_list,
            node,
            size,
            operands[0].clone(),
            operands[0].clone(),
        );

        Ok(())
    }

    fn emit_complement_operation(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        operation: &str,
        size: RV64Size,
    ) -> syn::Result<()> {
        riscv64_validate_operands(node.operands.iter(), &[OperandType::RegisterId])?;

        let complement_opcode = match operation {
            "neg" => {
                if size == RV64Size::I {
                    "negw"
                } else {
                    "neg"
                }
            }
            "not" => "not",
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("Invalid operation: {}", operation),
                ))
            }
        };

        new_list.push(Node::Instruction(Instruction {
            opcode: id(&format!("rv_{}", complement_opcode)),
            operands: punc_from_vec(vec![node.operands[0].clone(), node.operands[0].clone()]),
            ..Default::default()
        }));

        riscv64_lower_emit_mask(
            new_list,
            node,
            size,
            node.operands[0].clone(),
            node.operands[0].clone(),
        );

        Ok(())
    }

    fn emit_bit_extension_operation(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        extension: &str,
        from_size: RV64Size,
        to_size: RV64Size,
    ) -> syn::Result<()> {
        riscv64_validate_operands(
            node.operands.iter(),
            &[OperandType::RegisterId, OperandType::RegisterId],
        )?;

        let source = node.operands[0].clone();
        let dest = node.operands[1].clone();

        if extension == "s"
            && from_size == RV64Size::I
            && (to_size == RV64Size::P || to_size == RV64Size::Q)
        {
            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_sext.w"),
                operands: node.operands.clone(),
                ..Default::default()
            }));
            return Ok(());
        }

        if extension == "z"
            && from_size == RV64Size::I
            && (to_size == RV64Size::P || to_size == RV64Size::Q)
        {
            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_slli"),
                operands: punc_from_vec(vec![
                    dest.clone(),
                    source.clone(),
                    Node::Immediate(Immediate { value: 32 }),
                ]),
                ..Default::default()
            }));
            new_list.push(Node::Instruction(Instruction {
                opcode: id("rv_srli"),
                operands: punc_from_vec(vec![
                    dest.clone(),
                    dest.clone(),
                    Node::Immediate(Immediate { value: 32 }),
                ]),
                ..Default::default()
            }));
            return Ok(());
        }

        if extension != "s" {
            return Err(syn::Error::new(
                Span::call_site(),
                "Invalid zero extension".to_string(),
            ));
        }

        match (from_size, to_size) {
            (RV64Size::B, RV64Size::I) => {
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_slli"),
                    operands: punc_from_vec(vec![
                        dest.clone(),
                        source.clone(),
                        Node::Immediate(Immediate { value: 56 }),
                    ]),
                    ..Default::default()
                }));
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_srai"),
                    operands: punc_from_vec(vec![
                        dest.clone(),
                        dest.clone(),
                        Node::Immediate(Immediate { value: 24 }),
                    ]),
                    ..Default::default()
                }));
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_srli"),
                    operands: punc_from_vec(vec![
                        dest.clone(),
                        dest.clone(),
                        Node::Immediate(Immediate { value: 32 }),
                    ]),
                    ..Default::default()
                }));
            }
            (RV64Size::B, RV64Size::Q) => {
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_slli"),
                    operands: punc_from_vec(vec![
                        dest.clone(),
                        source.clone(),
                        Node::Immediate(Immediate { value: 56 }),
                    ]),
                    ..Default::default()
                }));
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_srai"),
                    operands: punc_from_vec(vec![
                        dest.clone(),
                        dest.clone(),
                        Node::Immediate(Immediate { value: 56 }),
                    ]),
                    ..Default::default()
                }));
            }
            (RV64Size::H, RV64Size::I) => {
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_slli"),
                    operands: punc_from_vec(vec![
                        dest.clone(),
                        source.clone(),
                        Node::Immediate(Immediate { value: 48 }),
                    ]),
                    ..Default::default()
                }));
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_srai"),
                    operands: punc_from_vec(vec![
                        dest.clone(),
                        dest.clone(),
                        Node::Immediate(Immediate { value: 16 }),
                    ]),
                    ..Default::default()
                }));
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_srli"),
                    operands: punc_from_vec(vec![
                        dest.clone(),
                        dest.clone(),
                        Node::Immediate(Immediate { value: 32 }),
                    ]),
                    ..Default::default()
                }));
            }
            (RV64Size::H, RV64Size::Q) => {
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_slli"),
                    operands: punc_from_vec(vec![
                        dest.clone(),
                        source.clone(),
                        Node::Immediate(Immediate { value: 48 }),
                    ]),
                    ..Default::default()
                }));
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_srai"),
                    operands: punc_from_vec(vec![
                        dest.clone(),
                        dest.clone(),
                        Node::Immediate(Immediate { value: 48 }),
                    ]),
                    ..Default::default()
                }));
            }
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "Invalid bit-extension combination".to_string(),
                ));
            }
        }

        Ok(())
    }

    fn emit_zero_count_operation(
        new_list: &mut Vec<Node>,
        node: &Instruction,
        side: &str,
        size: RV64Size,
    ) -> syn::Result<()> {
        riscv64_validate_operands(
            node.operands.iter(),
            &[OperandType::RegisterId, OperandType::RegisterId],
        )?;

        let from = &node.operands[0];
        let to = &node.operands[1];

        let (bits, suffix) = match size {
            RV64Size::I => (32, "w"),
            RV64Size::Q => (64, ""),
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "Invalid size for zero count operation".to_string(),
                ))
            }
        };

        let count = Node::Tmp(Tmp::new(TmpKind::Gpr));
        new_list.push(Node::Instruction(Instruction {
            opcode: id("rv_xor"),
            operands: punc_from_vec(vec![count.clone(), count.clone(), count.clone()]),
            ..Default::default()
        }));

        let tmp = Node::Tmp(Tmp::new(TmpKind::Gpr));
        new_list.push(Node::Instruction(Instruction {
            opcode: id("rv_li"),
            operands: punc_from_vec(vec![
                tmp.clone(),
                Node::Immediate(Immediate {
                    value: if side == "t" { bits } else { bits - 1 },
                }),
            ]),
            ..Default::default()
        }));

        let loop_label = Node::LocalLabel(LocalLabel::unique("begin_count_loop"));
        new_list.push(loop_label.clone());

        let check = Node::Tmp(Tmp::new(TmpKind::Gpr));
        new_list.push(Node::Instruction(Instruction {
            opcode: id(format!("rv_srl{}", suffix).as_str()),
            operands: punc_from_vec(vec![
                check.clone(),
                from.clone(),
                if side == "t" {
                    count.clone()
                } else {
                    tmp.clone()
                },
            ]),
            ..Default::default()
        }));

        new_list.push(Node::Instruction(Instruction {
            opcode: id("rv_andi"),
            operands: punc_from_vec(vec![
                check.clone(),
                check.clone(),
                Node::Immediate(Immediate { value: 1 }),
            ]),
            ..Default::default()
        }));

        let return_label = Node::LocalLabel(LocalLabel::unique("return_count"));
        new_list.push(Node::Instruction(Instruction {
            opcode: id("rv_bgtz"),
            operands: punc_from_vec(vec![
                check.clone(),
                Node::LocalLabelReference(LocalLabelReference::new(
                    return_label.as_local_label().cloned().unwrap(),
                )),
            ]),
            ..Default::default()
        }));

        new_list.push(Node::Instruction(Instruction {
            opcode: id(format!("rv_addi{}", suffix).as_str()),
            operands: punc_from_vec(vec![
                count.clone(),
                count.clone(),
                Node::Immediate(Immediate { value: 1 }),
            ]),
            ..Default::default()
        }));

        match side {
            "t" => {
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_blt"),
                    operands: punc_from_vec(vec![
                        count.clone(),
                        tmp.clone(),
                        Node::LocalLabelReference(LocalLabelReference::new(
                            loop_label.as_local_label().cloned().unwrap(),
                        )),
                    ]),
                    ..Default::default()
                }));
            }
            "l" => {
                new_list.push(Node::Instruction(Instruction {
                    opcode: id(format!("rv_addi{}", suffix).as_str()),
                    operands: punc_from_vec(vec![
                        tmp.clone(),
                        tmp.clone(),
                        Node::Immediate(Immediate { value: -1 }),
                    ]),
                    ..Default::default()
                }));

                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rv_bgez"),
                    operands: punc_from_vec(vec![
                        tmp.clone(),
                        Node::LocalLabelReference(LocalLabelReference::new(
                            loop_label.as_local_label().cloned().unwrap(),
                        )),
                    ]),
                    ..Default::default()
                }));
            }
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "Invalid side for zero count operation".to_string(),
                ))
            }
        }

        new_list.push(return_label);
        new_list.push(Node::Instruction(Instruction {
            opcode: id("rv_mv"),
            operands: punc_from_vec(vec![to.clone(), count.clone()]),
            ..Default::default()
        }));

        Ok(())
    }

    let mut new_list = Vec::new();
    for node in list.iter() {
        match node {
            Node::Instruction(ins) => {
                let opcode = ins.opcode.to_string();

                if opcode.starts_with("load") {
                    let stripped = opcode.strip_prefix("load").unwrap();
                    let (size, _) = RV64Size::from_str(stripped);
                    emit_load_operation(&mut new_list, ins, size)?;
                } else if opcode.starts_with("store") {
                    let stripped = opcode.strip_prefix("store").unwrap();
                    let (size, _) = RV64Size::from_str(stripped);
                    emit_store_operation(&mut new_list, ins, size)?;
                } else if opcode == "move" {
                    emit_move_operation(&mut new_list, ins)?;
                } else if opcode == "jmp" {
                    emit_jump(&mut new_list, ins)?;
                } else if opcode == "call" {
                    emit_call(&mut new_list, ins)?;
                } else if opcode == "push" {
                    emit_push(&mut new_list, ins)?;
                } else if opcode == "pop" {
                    emit_pop(&mut new_list, ins)?;
                } else if opcode.starts_with("add") || opcode.starts_with("sub") {
                    let (op, suffix) = opcode.split_at(3);
                    let (size, _) = RV64Size::from_str(suffix);
                    emit_addition_operation(&mut new_list, ins, op == "add", size)?;
                } else if opcode.starts_with("mul")
                    || opcode.starts_with("div")
                    || opcode.starts_with("rem")
                {
                    let (op, rest) = opcode.split_at(3);
                    let (suffix, sign) = rest.split_at(1);
                    let (size, _) = RV64Size::from_str(suffix);
                    emit_multiplication_operation(&mut new_list, ins, op, size, sign)?;
                } else if opcode.starts_with("lrotate") || opcode.starts_with("rrotate") {
                    let (op, suffix) = opcode.split_at(7);
                    let (size, _) = RV64Size::from_str(suffix);
                    riscv64_emit_rotate_operation(&mut new_list, ins, op, size)?;
                } else if opcode.starts_with("lshift")
                    || opcode.starts_with("rshift")
                    || opcode.starts_with("urshift")
                {
                    let (op, suffix) = if opcode.starts_with("urshift") {
                        opcode.split_at(7)
                    } else {
                        opcode.split_at(6)
                    };
                    let (size, _) = RV64Size::from_str(suffix);
                    riscv64_emit_shift_operation(&mut new_list, ins, op, size)?;
                } else if opcode.starts_with("and")
                    || opcode.starts_with("or")
                    || opcode.starts_with("xor")
                {
                    let (op, suffix) = opcode.split_at(3);
                    let (size, _) = RV64Size::from_str(suffix);
                    emit_logical_operation(&mut new_list, ins, op, size)?;
                } else if opcode.starts_with("neg") || opcode.starts_with("not") {
                    let (op, suffix) = opcode.split_at(3);
                    let (size, _) = RV64Size::from_str(suffix);
                    emit_complement_operation(&mut new_list, ins, op, size)?;
                } else if opcode.starts_with("sx") || opcode.starts_with("zx") {
                    let (sign, rest) = opcode.split_at(2);
                    let (from, to) = rest.split_at(2);
                    let (from_size, _) = RV64Size::from_str(&from[1..2]);
                    let (to_size, _) = RV64Size::from_str(&to[1..2]);
                    emit_bit_extension_operation(&mut new_list, ins, sign, from_size, to_size)?;
                } else if opcode.starts_with("tzcnt") || opcode.starts_with("lzcnt") {
                    let (op, suffix) = opcode.split_at(5);
                    let (size, _) = RV64Size::from_str(suffix);
                    emit_zero_count_operation(&mut new_list, ins, op, size)?;
                } else if opcode == "break" {
                    new_list.push(Node::Instruction(Instruction {
                        opcode: id("rv_ebreak"),
                        operands: punc_from_vec(vec![]),
                        ..Default::default()
                    }));
                } else if opcode == "nop" || opcode == "ret" {
                    new_list.push(Node::Instruction(Instruction {
                        opcode: id(&format!("rv_{}", opcode)),
                        operands: punc_from_vec(vec![]),
                        ..Default::default()
                    }));
                } else if opcode == "memfence" {
                    new_list.push(Node::Instruction(Instruction {
                        opcode: id("rv_fence"),
                        operands: punc_from_vec(vec![
                            Node::RV64MemoryOrdering(RISCV64MemoryOrdering::Rw),
                            Node::RV64MemoryOrdering(RISCV64MemoryOrdering::Rw),
                        ]),
                        ..Default::default()
                    }));
                } else if opcode == "fence" {
                    new_list.push(Node::Instruction(Instruction {
                        opcode: id("rv_fence"),
                        operands: punc_from_vec(vec![
                            Node::RV64MemoryOrdering(RISCV64MemoryOrdering::IoRw),
                            Node::RV64MemoryOrdering(RISCV64MemoryOrdering::IoRw),
                        ]),
                        ..Default::default()
                    }));
                } else {
                    new_list.push(node.clone());
                }
            }
            _ => new_list.push(node.clone()),
        }
    }
    Ok(new_list)
}

impl Node {
    pub fn riscv64_memory_ordering(&self) -> syn::Result<RISCV64MemoryOrdering> {
        match self {
            Node::RV64MemoryOrdering(x) => Ok(x.clone()),
            _ => Err(syn::Error::new(
                Span::call_site(),
                format!("Invalid node: {}", self),
            )),
        }
    }

    pub fn riscv64_rounding_mode(&self) -> syn::Result<RISCV64RoundingMode> {
        match self {
            Node::RV64RoundingMode(x) => Ok(x.clone()),
            _ => Err(syn::Error::new(
                Span::call_site(),
                format!("Invalid node: {}", self),
            )),
        }
    }

    pub fn riscv64_operand(&self) -> syn::Result<String> {
        match self {
            Node::Immediate(immediate) => immediate.riscv64_operand(IValidate::IImmediate),
            Node::Address(address) => address.riscv64_operand(),
            _ => panic!("Invalid node: {}", self),
        }
    }

    pub fn riscv64_requires_load(&self, validation: IValidate) -> bool {
        match self {
            Node::Immediate(immediate) => immediate.riscv64_requires_load(validation),
            Node::Address(address) => address.offset.riscv64_requires_load(IValidate::IImmediate),
            _ => false,
        }
    }
}

fn rvop(opcode: &str) -> syn::Result<String> {
    let caps = lazy_regex::regex_captures!(r"^rv_(.+)", opcode).ok_or_else(|| {
        syn::Error::new(
            Span::call_site(),
            format!("Invalid opcode format: {}", opcode),
        )
    })?;
    Ok(caps.0.to_string())
}

impl Node {
    pub fn get_modifier_list_riscv64(&self) -> syn::Result<Vec<Node>> {
        let Node::Seq(seq) = self else {
            return Ok(vec![]);
        };
        let mut result = seq.to_vec();
        result = risc_lower_malformed_address_double(&result);
        println!(
            "RV64 lower_malformed_address_double:\n{}",
            result
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join("\n")
        );
        result = riscv64_lower_misplaced_address(&result)?;
        println!(
            "RV64 lower_misplaced_address:\n{}",
            result
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join("\n")
        );
        result = riscv64_lower_address_loads(&result)?;

        result = risc_lower_misplaced_immediates(
            &result,
            &["storeb", "storeh", "storei", "storep", "storeq"],
        );
        result = risc_lower_malformed_immediates(
            &result,
            &|imm| (-0x800..0x7ff).contains(&imm),
            &|imm| (-0x800..0x7ff).contains(&imm),
        );
        result = riscv64_lower_immediate_sub(&result)?;

        result = riscv64_lower_operation(&result)?;
        RISCV64_EXTRA_GPRS.with(|gprs| {
            result = assign_registers_to_temporaries(&result, TmpKind::Gpr, &*gprs).unwrap();
        });

        RISCV64_EXTRA_FPRS.with(|fprs| {
            result = assign_registers_to_temporaries(&result, TmpKind::Fpr, &*fprs).unwrap();
        });

        Ok(result)
    }
}

impl Instruction {
    /*pub fn lower_riscv64(&self, asm: &mut Assembler) -> syn::Result<()> {

    }*/
}
