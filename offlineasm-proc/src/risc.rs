//! This file contains utilities that are useful for implementing a backend
//! for RISC-like processors (ARM, MIPS, etc).

//! Lowering of simple branch ops. For example:
//!
//! ```
//! baddiz foo, bar, baz
//! ```
//!
//! will become:
//!
//! ```
//! addi foo, bar
//! bz baz
//! ```

use proc_macro2::Span;
use syn::punctuated::Punctuated;

use crate::{ast::*, id, punc_from_vec};

pub fn lower_simple_branch_ops(seq: &Vec<Node>) -> Vec<Node> {
    let mut new_list = Vec::new();

    for node in seq.iter() {
        match node {
            Node::Instruction(ins) => {
                let opcode = ins.opcode.to_string();
                //let (op, post_match) = lazy_regex::regex_captures!(r"^b(addi|subi|ori|addp)", &opcode).unwrap();

                match lazy_regex::regex_captures!(r"^b(addi|subi|ori|addp)", &opcode) {
                    Some((full_op, op)) => {
                        let branch = format!("b{}", &opcode[full_op.len()..]);

                        let op = match op {
                            "addi" => "addis",
                            "subi" => "subis",
                            "ori" => "oris",
                            "addp" => "addps",

                            _ => unreachable!(),
                        };
                        let operands = ins.operands.iter().cloned().collect::<Vec<_>>();
                        let bin_operands = operands[0..operands.len() - 2]
                            .iter()
                            .cloned()
                            .collect::<Vec<_>>();
                        let branch_operand = operands[operands.len() - 1].clone();
                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: id(op),
                            documentation: ins.documentation.clone(),
                            operands: punc_from_vec(bin_operands),
                        }));

                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: id(branch),
                            documentation: None,
                            operands: punc_from_vec(vec![branch_operand]),
                        }));
                    }

                    None => match opcode.as_str() {
                        "bmuliz" => {
                            let operands = ins.operands.iter().cloned().collect::<Vec<_>>();
                            let bin_operands = operands[0..operands.len() - 2]
                                .iter()
                                .cloned()
                                .collect::<Vec<_>>();
                            let branch_operand = operands[operands.len() - 1].clone();
                            new_list.push(Node::Instruction(Instruction {
                                span: ins.span.clone(),
                                opcode: id("mulis"),
                                documentation: None,
                                operands: punc_from_vec(bin_operands),
                            }));

                            new_list.push(Node::Instruction(Instruction {
                                span: ins.span.clone(),
                                opcode: id("btis"),
                                documentation: None,
                                operands: punc_from_vec(vec![
                                    operands[operands.len() - 2].clone(),
                                    branch_operand,
                                ]),
                            }));
                        }

                        _ => new_list.push(node.clone()),
                    },
                }
            }
            _ => new_list.push(node.clone()),
        }
    }

    new_list
}

/// Lowing of complex branch ops. For example:
///
/// ```
/// bmulio foo, bar, baz
/// ```
///
/// becomes:
///
/// ```
/// smulli foo, bar, bar, tmp1
/// rshifti bar, 31, tmp2
/// bineq tmp1, tmp2, baz
/// ```
pub fn risc_lower_hard_branch_ops(seq: &Vec<Node>) -> Vec<Node> {
    let mut new_list = Vec::new();

    for node in seq.iter() {
        match node {
            Node::Instruction(ins) if ins.opcode == "bmulio" => {
                let tmp1 = Tmp::new(TmpKind::Gpr);
                let tmp2 = Tmp::new(TmpKind::Gpr);
                // smulli operands[0], operands[1], operands[1], tmp1
                new_list.push(Node::Instruction(Instruction {
                    span: ins.span.clone(),
                    opcode: id("smulli"),
                    documentation: None,
                    operands: punc_from_vec(vec![
                        ins.operands[0].clone(),
                        ins.operands[1].clone(),
                        ins.operands[1].clone(),
                        Node::Tmp(tmp1.clone()),
                    ]),
                }));
                // rshifti operands[-2], 31, tmp2
                new_list.push(Node::Instruction(Instruction {
                    span: ins.span.clone(),
                    opcode: id("rshifti"),
                    documentation: None,
                    operands: punc_from_vec(vec![
                        ins.operands[ins.operands.len() - 2].clone(),
                        Node::Immediate(Immediate { value: 31 }),
                        Node::Tmp(tmp2.clone()),
                    ]),
                }));
                // bineq tmp1, tmp2, operands[-1]
                new_list.push(Node::Instruction(Instruction {
                    span: ins.span.clone(),
                    opcode: id("bineq"),
                    documentation: None,
                    operands: punc_from_vec(vec![
                        Node::Tmp(tmp1.clone()),
                        Node::Tmp(tmp2.clone()),
                        ins.operands[ins.operands.len() - 1].clone(),
                    ]),
                }));
            }

            _ => new_list.push(node.clone()),
        }
    }

    new_list
}

fn risc_sanitize_shift(operand: &Node, list: &mut Vec<Node>) -> Node {
    if let Node::Immediate(_) = operand {
        return operand.clone();
    }

    let tmp = Tmp::new(TmpKind::Gpr);
    list.push(Node::Instruction(Instruction {
        opcode: id("andi"),
        documentation: None,
        span: Span::call_site(),
        operands: punc_from_vec(vec![
            operand.clone(),
            Node::Immediate(Immediate { value: 31 }),
            Node::Tmp(tmp.clone()),
        ]),
    }));
    Node::Tmp(tmp)
}

fn risc_lower_shift_ops(seq: &Vec<Node>) -> Vec<Node> {
    let mut new_list = Vec::new();

    for node in seq.iter() {
        match node {
            Node::Instruction(ins)
                if matches!(
                    &*ins.opcode.to_string(),
                    "lshifti" | "rshifti" | "urshifti" | "lshiftp" | "rshiftp" | "urshiftp"
                ) =>
            {
                match ins.operands.len() {
                    2 => {
                        let sanitized = risc_sanitize_shift(&ins.operands[0], &mut new_list);
                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: ins.opcode.clone(),
                            documentation: None,
                            operands: punc_from_vec(vec![sanitized, ins.operands[1].clone()]),
                        }));
                    }
                    3 => {
                        let sanitized = risc_sanitize_shift(&ins.operands[1], &mut new_list);
                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: ins.opcode.clone(),
                            documentation: None,
                            operands: punc_from_vec(vec![
                                ins.operands[0].clone(),
                                sanitized,
                                ins.operands[2].clone(),
                            ]),
                        }));
                    }
                    _ => panic!("Wrong number of operands for shift at {:?}", ins.span),
                }
            }
            _ => new_list.push(node.clone()),
        }
    }

    new_list
}

impl Address {
    pub fn risc_lower_malformed_addresses_recurse(
        &self,
        orig: &Node,
        list: &mut Vec<Node>,
        node: &Node,
        filter: &impl Fn(&Node, &Node) -> bool,
    ) -> Node {
        if filter(node, orig) {
            return Node::Address(self.clone());
        }

        let tmp = Tmp::new(TmpKind::Gpr);
        // mov self.offset, tmp
        list.push(Node::Instruction(Instruction {
            span: Span::call_site(),
            opcode: id("mov"),
            documentation: None,
            operands: punc_from_vec(vec![(*self.offset).clone(), Node::Tmp(tmp.clone())]),
        }));
        // addp self.base, tmp
        list.push(Node::Instruction(Instruction {
            span: Span::call_site(),
            opcode: id("addp"),
            documentation: None,
            operands: punc_from_vec(vec![(*self.base).clone(), Node::Tmp(tmp.clone())]),
        }));

        Node::Address(Address {
            base: Box::new(Node::Tmp(tmp.clone())),
            offset: Box::new(Node::Immediate(Immediate { value: 0 })),
            bracket_token: self.bracket_token.clone(),
        })
    }
}

impl BaseIndex {
    pub fn risc_lower_malformed_addresses_recurse(
        &self,
        orig: &Node,
        list: &mut Vec<Node>,
        node: &Node,
        filter: &impl Fn(&Node, &Node) -> bool,
    ) -> Node {
        if filter(node, orig) {
            return Node::BaseIndex(self.clone());
        }
        let tmp = Tmp::new(TmpKind::Gpr);
        // leap 0[self.base, self.index, scale], tmp
        list.push(Node::Instruction(Instruction {
            span: Span::call_site(),
            opcode: id("leap"),
            documentation: None,
            operands: punc_from_vec(vec![
                Node::BaseIndex(BaseIndex {
                    base: self.base.clone(),
                    index: self.index.clone(),
                    scale: self.scale.clone(),
                    offset: Box::new(Node::Immediate(Immediate { value: 0 })),
                    comma1: self.comma1.clone(),
                    comma2: self.comma2.clone(),
                    bracket_token: self.bracket_token.clone(),
                }),
                Node::Tmp(tmp.clone()),
            ]),
        }));

        Node::Address(Address {
            base: Box::new(Node::Tmp(tmp.clone())),
            offset: self.offset.clone(),
            bracket_token: self.bracket_token.clone(),
        })
        .risc_lower_malformed_addresses_recurse(list, node, filter)
    }
}

impl AbsoluteAddress {
    pub fn risc_lower_malformed_addresses_recurse(
        &self,
        orig: &Node,
        list: &mut Vec<Node>,
        node: &Node,
        filter: &impl Fn(&Node, &Node) -> bool,
    ) -> Node {
        if filter(node, orig) {
            return Node::AbsoluteAddress(self.clone());
        }

        let tmp = Tmp::new(TmpKind::Gpr);
        // mov address, tmp
        list.push(Node::Instruction(Instruction {
            span: Span::call_site(),
            opcode: id("mov"),
            documentation: None,
            operands: punc_from_vec(vec![(*self.base).clone(), Node::Tmp(tmp.clone())]),
        }));

        Node::Address(Address {
            base: Box::new(Node::Tmp(tmp.clone())),
            offset: Box::new(Node::Immediate(Immediate { value: 0 })),
            bracket_token: self.bracket_token.clone(),
        })
        .risc_lower_malformed_addresses_recurse(list, node, filter)
    }
}

impl BaseIndex {
    pub fn risc_double_address(&self, list: &mut Vec<Node>) -> Node {
        let tmp = Tmp::new(TmpKind::Gpr);
        // leap self, tmp
        list.push(Node::Instruction(Instruction {
            span: Span::call_site(),
            opcode: id("leap"),
            documentation: None,
            operands: punc_from_vec(vec![Node::BaseIndex(self.clone()), Node::Tmp(tmp.clone())]),
        }));
        Node::Address(Address {
            base: Box::new(Node::Tmp(tmp.clone())),
            offset: Box::new(Node::Immediate(Immediate { value: 0 })),
            bracket_token: self.bracket_token.clone(),
        })
    }
}

impl Node {
    pub fn risc_lower_malformed_addresses_recurse(
        &self,
        list: &mut Vec<Node>,
        node: &Node,
        filter: &impl Fn(&Node, &Node) -> bool,
    ) -> Node {
        match self {
            Node::Address(address) => {
                address.risc_lower_malformed_addresses_recurse(self, list, node, filter)
            }
            Node::BaseIndex(base_index) => {
                base_index.risc_lower_malformed_addresses_recurse(self, list, node, filter)
            }
            Node::AbsoluteAddress(absolute_address) => {
                absolute_address.risc_lower_malformed_addresses_recurse(self, list, node, filter)
            }
            Node::Instruction(instruction) => Node::Instruction(Instruction {
                span: instruction.span.clone(),
                opcode: instruction.opcode.clone(),
                documentation: instruction.documentation.clone(),
                operands: instruction
                    .operands
                    .iter()
                    .map(|operand| {
                        operand.risc_lower_malformed_addresses_recurse(list, node, filter)
                    })
                    .collect(),
            }),
            _ => self.clone(),
        }
    }

    pub fn risc_double_address(&self, list: &mut Vec<Node>) -> Node {
        match self {
            Node::BaseIndex(base_index) => base_index.risc_double_address(list),
            Node::Instruction(instruction) => Node::Instruction(Instruction {
                span: instruction.span.clone(),
                opcode: instruction.opcode.clone(),
                documentation: instruction.documentation.clone(),
                operands: instruction
                    .operands
                    .iter()
                    .map(|operand| operand.risc_double_address(list))
                    .collect(),
            }),
            _ => self.clone(),
        }
    }
}

pub fn risc_lower_malformed_address_double(list: &Vec<Node>) -> Vec<Node> {
    let mut new_list = Vec::new();

    for node in list.iter() {
        match node {
            Node::Instruction(ins) => {
                match &ins.opcode {
                    id if id == "loadd" => {
                        // loadd ins.operands[0].risc_double_address(&mut new_list), ins.operands[1]
                        let op0 = ins.operands[0].risc_double_address(&mut new_list);
                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: ins.opcode.clone(),
                            documentation: None,
                            operands: punc_from_vec(vec![op0, ins.operands[1].clone()]),
                        }));
                    }
                    id if id == "loadv" => {
                        // loadv ins.operands[0].risc_double_address(&mut new_list), ins.operands[1]
                        let op0 = ins.operands[0].risc_double_address(&mut new_list);
                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: ins.opcode.clone(),
                            documentation: None,
                            operands: punc_from_vec(vec![op0, ins.operands[1].clone()]),
                        }));
                    }

                    id if id == "loadf" => {
                        // loadf ins.operands[0].risc_double_address(&mut new_list), ins.operands[1]
                        let op0 = ins.operands[0].risc_double_address(&mut new_list);
                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: ins.opcode.clone(),
                            documentation: None,
                            operands: punc_from_vec(vec![op0, ins.operands[1].clone()]),
                        }));
                    }

                    id if id == "stored" => {
                        // stored ins.operands[0], ins.operands[1].risc_double_address(&mut new_list)
                        let op1 = ins.operands[1].risc_double_address(&mut new_list);
                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: ins.opcode.clone(),
                            documentation: None,
                            operands: punc_from_vec(vec![op1, ins.operands[1].clone()]),
                        }));
                    }

                    id if id == "storef" => {
                        // storef ins.operands[0], ins.operands[1].risc_double_address(&mut new_list)
                        let op1 = ins.operands[1].risc_double_address(&mut new_list);
                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: ins.opcode.clone(),
                            documentation: None,
                            operands: punc_from_vec(vec![ins.operands[0].clone(), op1]),
                        }));
                    }

                    id if id == "storev" => {
                        // storev ins.operands[0], ins.operands[1].risc_double_address(&mut new_list)
                        let op1 = ins.operands[1].risc_double_address(&mut new_list);
                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: ins.opcode.clone(),
                            documentation: None,
                            operands: punc_from_vec(vec![ins.operands[0].clone(), op1]),
                        }));
                    }

                    _ => new_list.push(node.clone()),
                }
            }

            _ => new_list.push(node.clone()),
        }
    }

    new_list
}

pub fn risc_lower_misplaced_immediates(list: &Vec<Node>, opcode_list: &[&str]) -> Vec<Node> {
    let mut new_list = Vec::new();

    for node in list.iter() {
        if let Node::Instruction(ins) = node {
            if opcode_list.iter().any(|opcode| ins.opcode == opcode) {
                let mut new_operands = Vec::new();
                for operand in ins.operands.iter() {
                    if let Node::Immediate(_) = operand {
                        // mov operand, tmp
                        let tmp = Tmp::new(TmpKind::Gpr);
                        new_list.push(Node::Instruction(Instruction {
                            span: Span::call_site(),
                            opcode: id("mov"),
                            documentation: None,
                            operands: punc_from_vec(vec![operand.clone(), Node::Tmp(tmp.clone())]),
                        }));
                        new_operands.push(Node::Tmp(tmp.clone()));
                    } else {
                        new_operands.push(operand.clone());
                    }
                }
                new_list.push(Node::Instruction(Instruction {
                    span: ins.span.clone(),
                    opcode: ins.opcode.clone(),
                    documentation: ins.documentation.clone(),
                    operands: punc_from_vec(new_operands),
                }));
            } else {
                new_list.push(node.clone());
            }
        } else {
            new_list.push(node.clone());
        }
    }

    new_list
}

impl Node {
    pub fn risc_lower_malformed_immediates(
        &self,
        list: &mut Vec<Node>,
        valid_immediates: &impl Fn(isize) -> bool,
    ) -> Node {
        match self {
            Node::Seq(seq) => Node::Seq({
                let mut new_list = Vec::new();
                for node in seq.iter() {
                    new_list.push(node.risc_lower_malformed_immediates(list, valid_immediates));
                }
                new_list
            }),
            Node::Instruction(ins) => Node::Instruction(Instruction {
                span: ins.span.clone(),
                opcode: ins.opcode.clone(),
                documentation: ins.documentation.clone(),
                operands: ins
                    .operands
                    .iter()
                    .map(|operand| operand.risc_lower_malformed_immediates(list, valid_immediates))
                    .collect(),
            }),

            Node::Immediate(imm) => {
                if valid_immediates(imm.value) {
                    return self.clone();
                }

                let tmp = Tmp::new(TmpKind::Gpr);
                // mov imm, tmp
                list.push(Node::Instruction(Instruction {
                    span: Span::call_site(),
                    opcode: id("mov"),
                    documentation: None,
                    operands: punc_from_vec(vec![self.clone(), Node::Tmp(tmp.clone())]),
                }));
                Node::Tmp(tmp)
            }

            Node::Address(address) => Node::Address(Address {
                base: Box::new(
                    address
                        .base
                        .risc_lower_malformed_immediates(list, valid_immediates),
                ),
                offset: address.offset.clone(),
                bracket_token: address.bracket_token.clone(),
            }),
            Node::BaseIndex(base_index) => Node::BaseIndex(BaseIndex {
                base: Box::new(
                    base_index
                        .base
                        .risc_lower_malformed_immediates(list, valid_immediates),
                ),
                index: base_index.index.clone(),
                scale: base_index.scale.clone(),
                offset: base_index.offset.clone(),
                comma1: base_index.comma1.clone(),
                comma2: base_index.comma2.clone(),
                bracket_token: base_index.bracket_token.clone(),
            }),

            _ => self.clone(),
        }
    }
}

pub fn riscv_lower_malformed_immediates(
    list: &Vec<Node>,
    valid_immediates: &impl Fn(isize) -> bool,
    valid_logic_immediates: &impl Fn(isize) -> bool,
) -> Vec<Node> {
    let mut new_list = Vec::new();

    for node in list.iter() {
        match node {
            Node::Instruction(ins) => match &ins.opcode {
                op if op == "mov" || op == "moveii" => {
                    new_list.push(node.clone());
                }

                op if op == "addi"
                    || op == "addp"
                    || op == "addq"
                    || op == "addis"
                    || op == "subi"
                    || op == "subp"
                    || op == "subq"
                    || op == "subis" =>
                {
                    match &ins.operands[0] {
                        Node::Immediate(imm)
                            if !valid_immediates(imm.value)
                                && valid_immediates(imm.value.wrapping_neg())
                                && ins.operands.len() == 2 =>
                        {
                            let mut opcode = ins.opcode.to_string();
                            if opcode.starts_with("add") {
                                opcode = opcode.replace("add", "sub");
                            } else {
                                opcode = opcode.replace("sub", "add");
                            }
                            let mut new_operands = vec![Node::Immediate(Immediate {
                                value: imm.value.wrapping_neg(),
                            })];
                            new_operands.extend(
                                ins.operands.iter().cloned().collect::<Vec<_>>()
                                    [1..]
                                    .iter()
                                    .cloned(),
                            );
                            new_list.push(Node::Instruction(Instruction {
                                span: ins.span.clone(),
                                opcode: id(opcode),
                                documentation: None,
                                operands: punc_from_vec(new_operands),
                            }));
                        }
                        _ => {
                            let node = node.risc_lower_malformed_immediates(&mut new_list, valid_immediates);
                            new_list.push(node);
                        }
                    }
                }

                op if op == "muli" || op == "mulp" || op == "mulq" => {
                    match &ins.operands[0] {
                        Node::Immediate(imm) if !valid_immediates(imm.value) => {
                            let tmp = Tmp::new(TmpKind::Gpr);
                            new_list.push(Node::Instruction(Instruction {
                                span: ins.span.clone(),
                                opcode: id("mov"),
                                documentation: None,
                                operands: punc_from_vec(vec![Node::Immediate(imm.clone()), Node::Tmp(tmp.clone())]),
                            }));

                            let mut new_operands = Punctuated::new();
                            new_operands.push(Node::Tmp(tmp.clone()));
                            for (i, operand) in ins.operands.iter().enumerate() {
                                if i == 0 {
                                    continue;
                                }


                                new_operands.push(operand.clone());
                            }

                            new_list.push(Node::Instruction(Instruction {
                                span: ins.span.clone(),
                                opcode: id("mul"),
                                documentation: None,
                                operands: new_operands,
                            }));
                        }
                        _ => {
                            let node = node.risc_lower_malformed_immediates(&mut new_list, valid_immediates);
                            new_list.push(node);
                        }
                    }
                }

                op if op == "ori" || op == "orh" || op == "orp" || op == "oris" || 
                    op == "xori" || op == "xorp" || op == "andi" || op == "andp" => {
                    let node = node.risc_lower_malformed_immediates(&mut new_list, valid_logic_immediates);
                    new_list.push(node);
                }

                _ => {
                    let node = node.risc_lower_malformed_immediates(&mut new_list, valid_immediates);
                    new_list.push(node);
                }
            },

            _ => new_list.push(node.clone()),
        }
    }

    new_list
}
