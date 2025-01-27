use proc_macro2::Span;
use syn::punctuated::Punctuated;

use crate::ast::*;

impl Node {
    pub fn replace_temporaries_with_registers(&self, kind: TmpKind) -> syn::Result<Node> {
        match self {
            Node::Tmp(tmp) => tmp.replace_temporaries_with_registers(kind),
            Node::Seq(seq) => Ok(Node::Seq({
                let mut new_list = Vec::new();
                for node in seq.iter() {
                    new_list.push(node.replace_temporaries_with_registers(kind)?);
                }
                new_list
            })),
            Node::Instruction(ins) => Ok({
                let mut operands = Punctuated::new();
                for operand in ins.operands.iter() {
                    operands.push(operand.replace_temporaries_with_registers(kind)?);
                }
                Node::Instruction(Instruction {
                    opcode: ins.opcode.clone(),
                    operands,
                    documentation: ins.documentation.clone(),
                    span: ins.span.clone(),
                })
            }),
            Node::Address(address) => Ok(Node::Address(Address {
                base: Box::new(address.base.replace_temporaries_with_registers(kind)?),
                offset: Box::new(address.offset.replace_temporaries_with_registers(kind)?),
            })),
            Node::AbsoluteAddress(address) => Ok(Node::AbsoluteAddress(AbsoluteAddress {
                base: Box::new(address.base.replace_temporaries_with_registers(kind)?),
            })),
            Node::BaseIndex(address) => Ok(Node::BaseIndex(BaseIndex {
                base: Box::new(address.base.replace_temporaries_with_registers(kind)?),
                index: Box::new(address.index.replace_temporaries_with_registers(kind)?),
                scale: Box::new(address.scale.replace_temporaries_with_registers(kind)?),
                offset: Box::new(address.offset.replace_temporaries_with_registers(kind)?),
            })),
            _ => Ok(self.clone()),
        }
    }
}

impl Node {
    fn mention(&self, index: usize) {
        match self {
            Node::Instruction(ins) => {
                for operand in ins.operands.iter() {
                    operand.mention(index);
                }
            }

            Node::Seq(seq) => {
                for node in seq.iter() {
                    node.mention(index);
                }
            }

            Node::Address(address) => {
                address.base.mention(index);
                address.offset.mention(index);
            }

            Node::AbsoluteAddress(address) => {
                address.base.mention(index);
            }

            Node::BaseIndex(address) => {
                address.base.mention(index);
                address.index.mention(index);
                address.scale.mention(index);
                address.offset.mention(index);
            }

            Node::Tmp(tmp) => tmp.mention(index),
            _ => (),
        }
    }
}

pub fn assign_registers_to_temporaries(
    seq: &Vec<Node>,
    kind: TmpKind,
    registers: &Vec<Node>,
) -> syn::Result<Vec<Node>> {
    let mut new_list = Vec::new();

    for (i, node) in seq.iter().enumerate() {
        node.mention(i);
    }

    let mut free_registers = registers.clone();

    for (i, node) in seq.iter().enumerate() {
        let mut tmp_list = node.filter(|x| matches!(x, Node::Tmp(_)));

        tmp_list.dedup_by(|a, b| match (a, b) {
            (Node::Tmp(a), Node::Tmp(b)) => a.id == b.id,
            _ => false,
        });

        for tmp in tmp_list.iter() {
            let Node::Tmp(tmp) = tmp else { unreachable!() };

            if tmp.kind == kind && tmp.first_mention.get() == i {
                if free_registers.is_empty() {
                    return Err(syn::Error::new(
                        Span::call_site(),
                        &format!(
                            "no free {:?} registers to assign to temporary `tmp{}`",
                            kind, tmp.id
                        ),
                    ));
                }

                let register = free_registers.pop().unwrap();

                tmp.register.borrow_mut().replace(register);
            }
            if tmp.kind == kind && tmp.last_mention.get() == i {
                if let Some(reg) = tmp.register.borrow_mut().as_ref().map(|x| x.clone()) {
                    free_registers.push(reg);
                }
            }
        }
    }

    for node in seq.iter() {
        new_list.push(node.replace_temporaries_with_registers(kind)?);
    }

    Ok(new_list)
}
