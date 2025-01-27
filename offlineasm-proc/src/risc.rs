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

use crate::{ast::*, id, instructions::mov, punc_from_vec};
use proc_macro2::Span;
use syn::punctuated::Punctuated;

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
                // smulli tmp1, operands[0], operands[1], operands[1]
                new_list.push(Node::Instruction(Instruction {
                    span: ins.span.clone(),
                    opcode: id("smulli"),
                    documentation: None,
                    operands: punc_from_vec(vec![
                        Node::Tmp(tmp1.clone()),
                        ins.operands[0].clone(),
                        ins.operands[1].clone(),
                        ins.operands[1].clone(),
                    ]),
                }));
                // rshifti tmp2, operands[-2], 31
                new_list.push(Node::Instruction(Instruction {
                    span: ins.span.clone(),
                    opcode: id("rshifti"),
                    documentation: None,
                    operands: punc_from_vec(vec![
                        Node::Tmp(tmp2.clone()),
                        ins.operands[ins.operands.len() - 2].clone(),
                        Node::Immediate(Immediate { value: 31 }),
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
                }),
                Node::Tmp(tmp.clone()),
            ]),
        }));

        Node::Address(Address {
            base: Box::new(Node::Tmp(tmp.clone())),
            offset: self.offset.clone(),
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
        // mov tmp, address
        list.push(Node::Instruction(Instruction {
            span: Span::call_site(),
            opcode: id("mov"),
            documentation: None,
            operands: punc_from_vec(vec![Node::Tmp(tmp.clone()), (*self.base).clone()]),
        }));

        Node::Address(Address {
            base: Box::new(Node::Tmp(tmp.clone())),
            offset: Box::new(Node::Immediate(Immediate { value: 0 })),
        })
        .risc_lower_malformed_addresses_recurse(list, node, filter)
    }
}

impl BaseIndex {
    pub fn risc_double_address(&self, list: &mut Vec<Node>) -> Node {
        let tmp = Tmp::new(TmpKind::Gpr);
        // leap tmp, self
        list.push(Node::Instruction(Instruction {
            span: Span::call_site(),
            opcode: id("leap"),
            documentation: None,
            operands: punc_from_vec(vec![Node::Tmp(tmp.clone()), Node::BaseIndex(self.clone())]),
        }));
        Node::Address(Address {
            base: Box::new(Node::Tmp(tmp.clone())),
            offset: Box::new(Node::Immediate(Immediate { value: 0 })),
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
            }),

            _ => self.clone(),
        }
    }
}

pub fn risc_lower_malformed_immediates(
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
                                ins.operands.iter().cloned().collect::<Vec<_>>()[1..]
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
                            let node = node
                                .risc_lower_malformed_immediates(&mut new_list, valid_immediates);
                            new_list.push(node);
                        }
                    }
                }

                op if op == "muli" || op == "mulp" || op == "mulq" => match &ins.operands[0] {
                    Node::Immediate(imm) if !valid_immediates(imm.value) => {
                        let tmp = Tmp::new(TmpKind::Gpr);
                        new_list.push(Node::Instruction(Instruction {
                            span: ins.span.clone(),
                            opcode: id("mov"),
                            documentation: None,
                            operands: punc_from_vec(vec![
                                Node::Tmp(tmp.clone()),
                                Node::Immediate(imm.clone()),
                            ]),
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
                        let node =
                            node.risc_lower_malformed_immediates(&mut new_list, valid_immediates);
                        new_list.push(node);
                    }
                },

                op if op == "ori"
                    || op == "orh"
                    || op == "orp"
                    || op == "oris"
                    || op == "xori"
                    || op == "xorp"
                    || op == "andi"
                    || op == "andp" =>
                {
                    let node =
                        node.risc_lower_malformed_immediates(&mut new_list, valid_logic_immediates);
                    new_list.push(node);
                }

                _ => {
                    let node =
                        node.risc_lower_malformed_immediates(&mut new_list, valid_immediates);
                    new_list.push(node);
                }
            },

            _ => new_list.push(node.clone()),
        }
    }

    new_list
}

/// Lowering of misplaced addresses. For example:
///
/// ```
/// addi [bar], foo
/// ```
///
/// will become:
///
/// ```
/// loadi tmp, [bar]
/// addi tmp, foo
/// storei [bar], tmp
/// ```
///
/// Another example:
///
/// ```
/// addi bar, [foo]
/// ```
///
/// will become:
///
/// ```
/// loadi tmp, [foo]
/// addi bar, tmp
/// ```
pub fn risc_lower_operand_to_registers(
    insn: &Instruction,
    pre_list: &mut Vec<Node>,
    post_list: &mut Vec<Node>,
    operand_index: usize,
    suffix: &str,
    need_store: bool,
) -> Node {
    let operand = &insn.operands[operand_index];
    if !matches!(
        operand,
        Node::Address(_) | Node::BaseIndex(_) | Node::AbsoluteAddress(_)
    ) {
        return operand.clone();
    }

    let tmp = Tmp::new(if suffix == "d" {
        TmpKind::Fpr
    } else {
        TmpKind::Gpr
    });

    pre_list.push(Node::Instruction(Instruction {
        span: insn.span.clone(),
        opcode: id(&format!("load{suffix}")),
        operands: punc_from_vec(vec![Node::Tmp(tmp.clone()), operand.clone()]),
        documentation: None,
    }));

    if need_store {
        post_list.push(Node::Instruction(Instruction {
            span: insn.span.clone(),
            opcode: id(&format!("store{suffix}")),
            operands: punc_from_vec(vec![operand.clone(), Node::Tmp(tmp.clone())]),
            documentation: None,
        }));
    }

    Node::Tmp(tmp)
}

pub fn risc_lower_operands_to_registers(
    insn: &Instruction,
    pre_list: &mut Vec<Node>,
    post_list: &mut Vec<Node>,
    suffix: &str,
) -> Vec<Node> {
    let mut new_operands = Vec::new();
    for (i, op) in insn.operands.iter().enumerate() {
        new_operands.push(risc_lower_operand_to_registers(
            insn,
            pre_list,
            post_list,
            i,
            suffix,
            i == 0,
        ));
    }

    new_operands
}

impl Instruction {
    pub fn clone_with_operand_lowered(
        &self,
        pre_list: &mut Vec<Node>,
        post_list: &mut Vec<Node>,
        operand_index: usize,
        suffix: &str,
        need_store: bool,
    ) -> Instruction {
        let operand = risc_lower_operand_to_registers(
            self,
            pre_list,
            post_list,
            operand_index,
            suffix,
            need_store,
        );
        let mut new_operands = self.operands.clone();
        new_operands[operand_index] = operand;
        Self {
            operands: new_operands,
            ..self.clone()
        }
    }

    pub fn clone_with_operands_lowered(
        &self,
        pre_list: &mut Vec<Node>,
        post_list: &mut Vec<Node>,
        suffix: &str,
    ) -> Instruction {
        let new_operands = risc_lower_operands_to_registers(self, pre_list, post_list, suffix);
        Self {
            operands: punc_from_vec(new_operands),
            ..self.clone()
        }
    }
}

pub fn risc_lower_misplaced_addresses(list: &Vec<Node>) -> Vec<Node> {
    let mut new_list = Vec::new();

    for node in list.iter() {
        match node {
            Node::Instruction(ins) => {
                let mut post_instuctions = Vec::new();

                let opcode = ins.opcode.to_string();
                match opcode.as_str() {
                    "addi" | "addis" | "andi" | "lshifti" | "muli" | "negi" | "noti" | "ori"
                    | "oris" | "rshifti" | "urshifti" | "subi" | "subis" | "xori" => {
                        let new_ins = ins.clone_with_operands_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            "i",
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }
                    _ if opcode.starts_with("bi")
                        || opcode.starts_with("bti")
                        || opcode.starts_with("ci")
                        || opcode.starts_with("ti") =>
                    {
                        let new_ins = ins.clone_with_operands_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            "",
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }
                    "addp" | "andp" | "lshiftp" | "mulp" | "negp" | "orp" | "rshiftp"
                    | "urshiftp" | "subp" | "xorp" => {
                        let new_ins = ins.clone_with_operands_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            "p",
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }
                    _ if opcode.starts_with("bp")
                        || opcode.starts_with("btp")
                        || opcode.starts_with("cp") =>
                    {
                        let new_ins = ins.clone_with_operands_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            "p",
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }
                    "addq" | "andq" | "lshiftq" | "mulq" | "negq" | "orq" | "rshiftq"
                    | "urshiftq" | "subq" | "xorq" => {
                        let new_ins = ins.clone_with_operands_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            "q",
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }
                    _ if opcode.starts_with("bq")
                        || opcode.starts_with("btq")
                        || opcode.starts_with("cq") =>
                    {
                        let new_ins = ins.clone_with_operands_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            "q",
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }

                    "bbeq" | "bbneq" | "bba" | "bbaeq" | "bbb" | "bbbeq" | "btbz" | "btbnz"
                    | "tbz" | "tbnz" | "cbeq" | "cbneq" | "cba" | "cbaeq" | "cbb" | "cbbeq" => {
                        let new_ins = ins.clone_with_operands_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            "b",
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }
                    "bbgt" | "bbgteq" | "bblt" | "bblteq" | "btbs" | "tbs" | "cbgt" | "cbgteq"
                    | "cblt" | "cblteq" => {
                        let new_ins = ins.clone_with_operands_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            "bs",
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }
                    "addd" | "divd" | "subd" | "muld" | "sqrtd" => {
                        let new_ins = ins.clone_with_operands_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            "d",
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }
                    _ if opcode.starts_with("bd") => {
                        let new_ins = ins.clone_with_operands_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            "d",
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }
                    "jmp" | "call" => {
                        let new_ins = ins.clone_with_operand_lowered(
                            &mut new_list,
                            &mut post_instuctions,
                            0,
                            "p",
                            false,
                        );
                        new_list.push(Node::Instruction(new_ins));
                    }
                    _ => new_list.push(node.clone()),
                }

                new_list.extend(post_instuctions);
            }
            _ => new_list.push(node.clone()),
        }
    }

    new_list
}

pub fn risc_lower_register_reuse(list: &Vec<Node>) -> Vec<Node> {
    let mut new_list = Vec::new();

    for node in list.iter() {
        match node {
            Node::Instruction(ins) => {
                let opcode = ins.opcode.to_string();
                let operands = &ins.operands;

                match opcode.as_str() {
                    "cieq" | "cineq" | "cia" | "ciaeq" | "cib" | "cibeq" | "cigt" | "cigteq"
                    | "cilt" | "cilteq" | "cpeq" | "cpneq" | "cpa" | "cpaeq" | "cpb" | "cpbeq"
                    | "cpgt" | "cpgteq" | "cplt" | "cplteq" | "tis" | "tiz" | "tinz" | "tbs"
                    | "tbz" | "tbnz" | "tps" | "tpz" | "tpnz" | "cbeq" | "cbneq" | "cba"
                    | "cbaeq" | "cbb" | "cbbeq" | "cbgt" | "cbgteq" | "cblt" | "cblteq" => {
                        if operands.len() == 2 {
                            if operands[0] == operands[1] {
                                let tmp = Tmp::new(TmpKind::Gpr);
                                new_list.push(mov(Node::Tmp(tmp.clone()), operands[1].clone()));
                                new_list.push(Node::Instruction(Instruction {
                                    operands: punc_from_vec(vec![
                                        operands[0].clone(),
                                        Node::Tmp(tmp.clone()),
                                    ]),
                                    ..ins.clone()
                                }));
                            } else {
                                new_list.push(Node::Instruction(ins.clone()));
                            }
                        } else {
                            if operands.len() != 3 {
                                unreachable!("wrong number of operands for instruction {}", node);
                            }

                            if operands[0] == operands[2] {
                                let tmp = Tmp::new(TmpKind::Gpr);
                                new_list.push(mov(Node::Tmp(tmp.clone()), operands[2].clone()));
                                new_list.push(Node::Instruction(Instruction {
                                    operands: punc_from_vec(vec![
                                        operands[0].clone(),
                                        operands[1].clone(),
                                        Node::Tmp(tmp.clone()),
                                    ]),
                                    ..ins.clone()
                                }));
                            } else if operands[1] == operands[2] {
                                let tmp = Tmp::new(TmpKind::Gpr);
                                new_list.push(mov(Node::Tmp(tmp.clone()), operands[2].clone()));
                                new_list.push(Node::Instruction(Instruction {
                                    operands: punc_from_vec(vec![
                                        operands[0].clone(),
                                        Node::Tmp(tmp.clone()),
                                        operands[1].clone(),
                                    ]),
                                    ..ins.clone()
                                }));
                            } else {
                                new_list.push(Node::Instruction(ins.clone()));
                            }
                        }
                    }
                    _ => new_list.push(Node::Instruction(ins.clone())),
                }
            }
            _ => new_list.push(node.clone()),
        }
    }

    new_list
}

fn risc_lower_not(list: Vec<Node>) -> Vec<Node> {
    let mut new_list = Vec::new();

    for node in list {
        match node {
            Node::Instruction(ins) => match &ins.opcode {
                x if x == "noti" || x == "notp" => {
                    if ins.operands.len() != 1 {
                        panic!("Wrong number of operands for not instruction");
                    }

                    let suffix = if x == "noti" { "i" } else { "p" };
                    let new_opcode = id(&format!("xor{}", suffix));

                    new_list.push(Node::Instruction(Instruction {
                        opcode: new_opcode,
                        operands: punc_from_vec(vec![
                            ins.operands[0].clone(),
                            Node::Immediate(Immediate { value: -1 }),
                        ]),
                        ..ins.clone()
                    }));
                }
                _ => new_list.push(Node::Instruction(ins.clone())),
            },
            _ => new_list.push(node.clone()),
        }
    }

    new_list
}

fn risc_lower_hard_branch_ops_64(list: Vec<Node>) -> Vec<Node> {
    let mut new_list = Vec::new();

    for node in list {
        match node {
            Node::Instruction(ins) if ins.opcode == "bmulio" => {
                if ins.operands.len() != 3 {
                    panic!("Wrong number of operands for bmulio instruction");
                }

                let tmp1 = Node::Tmp(Tmp::new(TmpKind::Gpr));
                let tmp2 = Node::Tmp(Tmp::new(TmpKind::Gpr));

                // smulli bar, bar, foo
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("smulli"),
                    operands: punc_from_vec(vec![
                        ins.operands[1].clone(),
                        ins.operands[1].clone(),
                        ins.operands[0].clone(),
                    ]),
                    ..ins.clone()
                }));

                // rshiftp tmp1, bar, 32
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rshiftp"),
                    operands: punc_from_vec(vec![
                        tmp1.clone(),
                        ins.operands[1].clone(),
                        Node::Immediate(Immediate { value: 32 }),
                    ]),
                    ..ins.clone()
                }));

                // rshifti tmp2, bar, 31
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("rshifti"),
                    operands: punc_from_vec(vec![
                        tmp2.clone(),
                        ins.operands[1].clone(),
                        Node::Immediate(Immediate { value: 31 }),
                    ]),
                    ..ins.clone()
                }));

                // zxi2p bar, bar
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("zxi2p"),
                    operands: punc_from_vec(vec![ins.operands[1].clone(), ins.operands[1].clone()]),
                    ..ins.clone()
                }));

                // bineq tmp1, tmp2, baz
                new_list.push(Node::Instruction(Instruction {
                    opcode: id("bineq"),
                    operands: punc_from_vec(vec![tmp1, tmp2, ins.operands[2].clone()]),
                    ..ins.clone()
                }));
            }
            _ => new_list.push(node),
        }
    }

    new_list
}

pub fn risc_lower_test(list: &Vec<Node>) -> Vec<Node> {
    let mut emit = |new_list: &mut Vec<Node>,
                    and_opcode: &str,
                    branch_opcode: &str,
                    node: &Instruction| {
        let and_opcode = id(and_opcode);
        let branch_opcode = id(branch_opcode);
        if node.operands.len() == 2 {
            new_list.push(Node::Instruction(Instruction {
                opcode: branch_opcode,
                operands: punc_from_vec(vec![
                    node.operands[0].clone(),
                    Node::Immediate(Immediate { value: 0 }),
                    node.operands[1].clone(),
                ]),
                ..node.clone()
            }));
            return;
        }

        if node.operands[0].is_immediate() && node.operands[0].immediate_value().unwrap() == -1 {
            new_list.push(Node::Instruction(Instruction {
                opcode: branch_opcode,
                operands: punc_from_vec(vec![
                    node.operands[1].clone(),
                    Node::Immediate(Immediate { value: 0 }),
                    node.operands[2].clone(),
                ]),
                ..node.clone()
            }));
            return;
        }

        if node.operands[1].is_immediate() && node.operands[1].immediate_value().unwrap() == -1 {
            new_list.push(Node::Instruction(Instruction {
                opcode: branch_opcode,
                operands: punc_from_vec(vec![
                    node.operands[0].clone(),
                    Node::Immediate(Immediate { value: 0 }),
                    node.operands[2].clone(),
                ]),
                ..node.clone()
            }));
            return;
        }

        let tmp = Node::Tmp(Tmp::new(TmpKind::Gpr));

        new_list.push(Node::Instruction(Instruction {
            opcode: and_opcode,
            operands: punc_from_vec(vec![
                tmp.clone(),
                node.operands[0].clone(),
                node.operands[1].clone(),
            ]),
            ..node.clone()
        }));

        new_list.push(Node::Instruction(Instruction {
            opcode: branch_opcode,
            operands: punc_from_vec(vec![
                tmp.clone(),
                Node::Immediate(Immediate { value: 0 }),
                node.operands[2].clone(),
            ]),
            ..node.clone()
        }));
    };

    let mut new_list = Vec::new();

    for node in list.iter() {
        match node {
            Node::Instruction(ins) => {
                let opcode = ins.opcode.to_string();
                let _n = node;
                let node = ins;

                match opcode.as_str() {
                    "btis" => emit(&mut new_list, "andi", "bilt", node),
                    "btiz" => emit(&mut new_list, "andi", "bieq", node),
                    "btinz" => emit(&mut new_list, "andi", "bineq", node),
                    "btps" => emit(&mut new_list, "andp", "bplt", node),
                    "btpz" => emit(&mut new_list, "andp", "bpeq", node),
                    "btpnz" => emit(&mut new_list, "andp", "bpneq", node),
                    "btqs" => emit(&mut new_list, "andq", "bqlt", node),
                    "btqz" => emit(&mut new_list, "andq", "bqeq", node),
                    "btqnz" => emit(&mut new_list, "andq", "bqneq", node),
                    "btbs" => emit(&mut new_list, "andi", "bblt", node),
                    "btbz" => emit(&mut new_list, "andi", "bbeq", node),
                    "btbnz" => emit(&mut new_list, "andi", "bbneq", node),
                    "tis" => emit(&mut new_list, "andi", "cilt", node),
                    "tiz" => emit(&mut new_list, "andi", "cieq", node),
                    "tinz" => emit(&mut new_list, "andi", "cineq", node),
                    "tps" => emit(&mut new_list, "andp", "cplt", node),
                    "tpz" => emit(&mut new_list, "andp", "cpeq", node),
                    "tpnz" => emit(&mut new_list, "andp", "cpneq", node),
                    "tqs" => emit(&mut new_list, "andq", "cqlt", node),
                    "tqz" => emit(&mut new_list, "andq", "cqeq", node),
                    "tqnz" => emit(&mut new_list, "andq", "cqneq", node),
                    "tbs" => emit(&mut new_list, "andi", "cblt", node),
                    "tbz" => emit(&mut new_list, "andi", "cbeq", node),
                    "tbnz" => emit(&mut new_list, "andi", "cbneq", node),
                    _ => new_list.push(_n.clone()),
                }
            }
            _ => new_list.push(node.clone()),
        }
    }

    new_list
}
