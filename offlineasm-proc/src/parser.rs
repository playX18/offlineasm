use super::ast::*;
use regex::Regex;
use std::collections::HashMap;
use std::sync::LazyLock;
use syn::parse::ParseStream;
use syn::punctuated::Punctuated;
use syn::Ident;

use crate::ast::BitNotImmediate;
use crate::ast::Const;
use crate::ast::ConstDecl;
use crate::ast::Instruction;
use crate::ast::Label;
use crate::ast::NegImmediate;
use crate::ast::Node;
use crate::instructions::*;
use crate::registers::*;
pub fn is_register(token: &str) -> bool {
    REGISTER_PATTERN.is_match(&token.to_string())
}

pub fn is_instruction(token: &str) -> bool {
    INSTRUCTION_SET.contains(&token.to_string().as_str())
}

// /\A[a-zA-Z%]([a-zA-Z0-9_.%]*)\Z/ -> identifier
static IDENTIFIER: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^[a-zA-Z_%]([a-zA-Z0-9_.%]*)").unwrap());

pub fn is_identifier(token: &str) -> bool {
    IDENTIFIER.is_match(&token.to_string()) && !is_keyword(token)
}

static KEYWORDS: [&str; 17] = [
    "true",
    "false",
    "if",
    "then",
    "else",
    "elsif",
    "end",
    "and",
    "or",
    "not",
    "global",
    "macro",
    "const",
    "constexpr",
    "sizeof",
    "error",
    "include",
];

pub fn is_keyword(token: &str) -> bool {
    KEYWORDS.contains(&token) || is_register(token) || is_instruction(token)
}

static LOCAL_LABEL: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"^L([a-zA-Z0-9_%])*").unwrap());

pub fn is_local_label(token: &str) -> bool {
    LOCAL_LABEL.is_match(&token.to_string())
}
mod kw {
    syn::custom_keyword!(export);
}

pub fn is_label(input: &ParseStream) -> bool {
    input.peek(syn::Token![->]) || (input.peek(syn::Ident) && input.peek2(syn::Token![:]))
}
pub fn is_not_operand(input: &ParseStream) -> bool {
    input.peek(syn::Token![;])
        || input.peek(syn::Token![#])
        || peek_instruction(input)
        || input.peek(syn::Token![->])
        || input.peek(syn::Token![const])
        || input.peek(syn::Token![if])
        || input.peek(syn::Token![macro])
        || input.peek(kw::export)
        || is_label(input)
}

pub struct AsmParser<'a> {
    pub settings: &'a HashMap<Ident, bool>,
}
impl<'a> AsmParser<'a> {
    pub fn parse_sequence_braced(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        let mut list = Vec::new();
        let content;
        let _ = syn::braced!(content in input);
        let expr = self.parse_sequence_inner(&mut &content)?;
        list.push(expr);
        Ok(Node::Seq(list))
    }

    pub fn parse_sequence_inner(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        let mut list = Vec::new();

        while !input.is_empty() {
            let mut doc = None;
            if let Some(docstr) = self.maybe_parse_doc(input)? {
                let mut collect = vec![docstr];
                while let Some(docstr) = self.maybe_parse_doc(input)? {
                    collect.push(docstr);
                }
                doc = Some(collect);
            }

            //let _ = input.parse::<syn::Trken![;]>()?;
            if input.peek(syn::Token![const]) {
                let _ = input.parse::<syn::Token![const]>()?;
                if input.peek(syn::Ident) {
                    let variable = input.parse::<syn::Ident>()?;
                    let eq = input.parse::<syn::Token![=]>()?;
                    let value = self.parse_operand(input)?;
                    let _ = input.parse::<syn::Token![;]>()?;
                    list.push(Node::ConstDecl(ConstDecl {
                        variable: Variable {
                            name: variable.clone(),
                            original: None,
                        },
                        documentation: doc.clone(),
                        span: variable.span(),
                        eq,
                        expr: Box::new(value),
                    }));
                } else {
                    let expr = input.parse::<syn::Expr>()?;
                    let _ = input.parse::<syn::Token![;]>()?;
                    list.push(Node::Const(Const { expr }));
                }
            } else if input.peek(syn::Token![if]) {
                let _ = input.parse::<syn::Token![if]>()?;
                let predicate = self.parse_predicate(input)?;
                let then = self.parse_sequence_braced(input)?;
                let mut if_then_else = IfThenElse {
                    predicate: Box::new(predicate),
                    then: Box::new(then),
                    else_case: None,
                };

                list.push(Node::IfThenElse(if_then_else));
                let Node::IfThenElse(ref mut if_then_else_last) = list.last_mut().unwrap() else {
                    return Err(syn::Error::new(
                        input.span(),
                        "invalid if-then-else structure",
                    ));
                };

                let mut if_then_else_last = if_then_else_last;
                while input.peek(syn::Token![else]) && input.peek2(syn::Token![if]) {
                    let _ = input.parse::<syn::Token![else]>()?;
                    let _ = input.parse::<syn::Token![if]>()?;
                    let predicate = self.parse_predicate(input)?;
                    let then = self.parse_sequence_braced(input)?;
                    let else_case = IfThenElse {
                        predicate: Box::new(predicate),
                        then: Box::new(then),
                        else_case: None,
                    };

                    if_then_else_last.else_case = Some(Box::new(Node::IfThenElse(else_case)));
                    if_then_else_last = match if_then_else_last.else_case.as_mut() {
                        Some(node) => match &mut **node {
                            Node::IfThenElse(if_then_else) => if_then_else,
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    };
                }

                if input.peek(syn::Token![else]) {
                    let _ = input.parse::<syn::Token![else]>()?;
                    let else_case = self.parse_sequence_braced(input)?;
                    if_then_else_last.else_case = Some(Box::new(else_case));
                }

                continue;
            } else if input.peek(syn::Token![macro]) {
                let _ = input.parse::<syn::Token![macro]>()?;
                let name = input.parse::<syn::Ident>()?;
                let mut args = Punctuated::new();
                let args_content;
                let _ = syn::parenthesized!(args_content in input);
                while !args_content.is_empty() {
                    let arg = args_content.parse::<syn::Ident>()?;
                    args.push_value(Variable {
                        name: arg,
                        original: None,
                    });
                    if !args_content.is_empty() {
                        args.push_punct(args_content.parse::<syn::Token![,]>()?);
                    }
                }
                let body = self.parse_sequence_braced(input)?;
                list.push(Node::Macro(Macro {
                    name,
                    args,
                    body: Box::new(body),
                }));
                continue;
            } else if input.peek(syn::Token![->]) {
                // global label
                let _ = input.parse::<syn::Token![->]>()?;
                let label = input.parse::<syn::Ident>()?;
                let _ = input.parse::<syn::Token![:]>()?;
                list.push(Node::Label(Label::for_name(&label, true)));
                continue;
            } else if input.peek(syn::Ident) && input.peek2(syn::Token![:]) {
                // local label

                let label = input.parse::<syn::Ident>()?;
                let _ = input.parse::<syn::Token![:]>()?;
                list.push(Node::LocalLabel(LocalLabel::for_name(&label)));
                continue;
            } else if input.peek(syn::Ident) {
                let identifier = input.parse::<syn::Ident>()?;
                let s: &str = &identifier.to_string();

                match s {
                    "export" => {
                        let name = input.parse::<syn::Ident>()?;
                        let _ = input.parse::<syn::Token![as]>()?;
                        let _ = input.parse::<syn::Token![unsafe]>()?;
                        // let _ = input.parse::<syn::Token![extern]>()?;
                        let abi = input.parse::<syn::Abi>()?;
                        let item = input.parse::<syn::ForeignItemFn>()?;
                        list.push(Node::Export(Export {
                            label: Label::for_name(&name, true),
                            item,
                            abi,
                        }));
                        continue;
                    }
                    "global" => {
                        let name = input.parse::<syn::Ident>()?;
                        Label::set_as_global(&name);
                    }

                    "globalexport" => {
                        let name = input.parse::<syn::Ident>()?;
                        Label::set_as_global_export(&name);
                    }
                    "unalignedglobal" => {
                        let name = input.parse::<syn::Ident>()?;

                        Label::set_as_unaligned_global(&name);
                    }

                    "aligned" => {
                        let name = input.parse::<syn::Ident>()?;
                        let align = input.parse::<syn::LitInt>()?.base10_parse::<usize>()?;
                        Label::set_as_aligned(&name, align);
                    }

                    "unalignedglobalexport" => {
                        let name = input.parse::<syn::Ident>()?;
                        Label::set_as_unaligned_global_export(&name);
                    }

                    name if is_instruction(name) => {
                        if input.is_empty() {
                            list.push(Node::Instruction(Instruction::new2(
                                identifier,
                                Punctuated::new(),
                                doc,
                            )));
                        } else if is_not_operand(input) {
                            if input.peek(syn::Token![;]) {
                                let _ = input.parse::<syn::Token![;]>()?;
                            }
                            list.push(Node::Instruction(Instruction::new2(
                                identifier,
                                Punctuated::new(),
                                doc,
                            )));
                        } else {
                            let mut operands = Punctuated::new();
                            let mut end_of_sequence = false;

                            loop {
                                operands.push(self.parse_operand(input)?);
                                if input.is_empty() {
                                    end_of_sequence = true;
                                    break;
                                } else if is_not_operand(input) {
                                    if input.peek(syn::Token![;]) {
                                        let _ = input.parse::<syn::Token![;]>()?;
                                    }
                                    break;
                                } else if input.peek(syn::Token![,]) {
                                    operands.push_punct(input.parse::<syn::Token![,]>()?);
                                } else {
                                    return Err(syn::Error::new(
                                        input.span(),
                                        "invalid operand: expected a `,` or operand",
                                    ));
                                }
                            }

                            list.push(Node::Instruction(Instruction::new2(
                                identifier, operands, doc,
                            )));

                            if end_of_sequence {
                                break;
                            }
                        }
                    }

                    name if is_identifier(name) => {
                        let _name = identifier.to_string();

                        if input.peek(syn::token::Paren) {
                            let mut operands = Punctuated::new();
                            // macro invocation
                            let content;
                            let _ = syn::parenthesized!(content in input);
                            loop {
                                if content.is_empty() {
                                    break;
                                } else if content.peek(syn::Token![macro]) {
                                    // macro lambda
                                    let _ = content.parse::<syn::Token![macro]>()?;
                                    let name = content.parse::<syn::Ident>()?;
                                    let mut args = Punctuated::new();
                                    let args_content;
                                    let _ = syn::parenthesized!(args_content in content);
                                    while !args_content.is_empty() {
                                        let arg = args_content.parse::<syn::Ident>()?;
                                        args.push_value(Variable {
                                            name: arg,
                                            original: None,
                                        });
                                        if !args_content.is_empty() {
                                            args.push_punct(
                                                args_content.parse::<syn::Token![,]>()?,
                                            );
                                        }
                                    }
                                    let body = self.parse_sequence_braced(&mut &content)?;

                                    operands.push_value(Node::Macro(Macro {
                                        name,
                                        args,
                                        body: Box::new(body),
                                    }));
                                } else {
                                    operands.push_value(self.parse_operand(&mut &content)?);
                                }
                                if !content.is_empty() {
                                    let punc = content.parse::<syn::Token![,]>()?;
                                    operands.push_punct(punc);
                                }
                            }
                            list.push(Node::MacroCall(MacroCall {
                                name: identifier,
                                args: operands,
                                original_name: None,
                            }));
                        } else {
                            return Err(syn::Error::new(identifier.span(), "invalid label name"));
                        }
                    }

                    name => {
                        return Err(syn::Error::new(
                            input.span(),
                            &format!("invalid token: {}", name),
                        ))
                    }
                }
            }
        }

        Ok(Node::Seq(list))
    }

    fn could_be_expression(input: &ParseStream) -> bool {
        input.peek(syn::Token![-])
            || input.peek(syn::Token![+])
            || input.peek(syn::Token![%])
            || input.peek(syn::Token![&])
            || input.peek(syn::Token![=>])
            || input.peek(syn::Token![const])
            || input.peek(syn::Ident)
            || input.peek(syn::LitInt)
            || input.peek(syn::token::Paren)
    }

    pub fn parse_operand(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        if Self::could_be_expression(input) {
            let expr = self.parse_expression(input)?;
            if input.peek(syn::token::Bracket) {
                return self.parse_address(expr, input);
            } else {
                return Ok(expr);
            }
        } else if input.peek(syn::token::Bracket) {
            return self.parse_address(Node::Immediate(Immediate { value: 0 }), input);
        } else {
            return Err(syn::Error::new(
                input.span(),
                &format!("invalid operand: {}", input),
            ));
        }
    }

    pub fn parse_const_expr(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        let expr = input.parse::<syn::Expr>()?;
        Ok(Node::Const(Const { expr }))
    }

    pub fn parse_address(&mut self, offset: Node, input: &mut ParseStream) -> syn::Result<Node> {
        let content;
        let bracket_token = syn::bracketed!(content in input);

        // Three possibilities:
        // []       -> AbsoluteAddress
        // [a]      -> Address
        // [a,b]    -> BaseIndex with scale = 1
        // [a,b,c]  -> BaseIndex
        if content.is_empty() {
            return Ok(Node::AbsoluteAddress(AbsoluteAddress {
                base: Box::new(offset),
            }));
        }
        let a = content.parse::<syn::Ident>()?;
        let a = self.parse_variable(a)?;
        if content.is_empty() {
            return Ok(Node::Address(Address {
                base: Box::new(a),
                offset: Box::new(offset),
            }));
        }
        let comma1 = content.parse::<syn::Token![,]>()?;
        let b = content.parse::<syn::Ident>()?;
        let b = self.parse_variable(b)?;

        if content.is_empty() {
            return Ok(Node::BaseIndex(BaseIndex {
                base: Box::new(a),
                index: Box::new(b),
                scale: Box::new(Node::Immediate(Immediate { value: 1 })),
                offset: Box::new(offset),
            }));
        }

        let comma2 = content.parse::<syn::Token![,]>()?;
        let scale = if content.peek(syn::Token![const]) {
            let _ = content.parse::<syn::Token![const]>()?;
            self.parse_const_expr(&mut &content)?
        } else if content.peek(syn::LitInt) {
            let lit = content.parse::<syn::LitInt>()?;
            let val = lit.base10_parse::<u8>()?;
            if matches!(val, 1 | 2 | 4 | 8) {
                Node::Immediate(Immediate {
                    value: val as isize,
                })
            } else {
                return Err(syn::Error::new(lit.span(), "invalid scale"));
            }
        } else {
            self.parse_variable(content.parse::<syn::Ident>()?)?
        };

        Ok(Node::BaseIndex(BaseIndex {
            base: Box::new(a),
            index: Box::new(b),
            scale: Box::new(scale),
            offset: Box::new(offset),
        }))
    }

    pub fn parse_expression(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_expression_and(input)?;

        while input.peek(syn::Token![|]) || input.peek(syn::Token![^]) {
            if input.peek(syn::Token![|]) {
                result = Node::OrImmediate(OrImmediate {
                    left: Box::new(result),
                    or: input.parse()?,
                    right: Box::new(self.parse_expression_and(input)?),
                });
            } else if input.peek(syn::Token![^]) {
                result = Node::XorImmediate(XorImmediate {
                    left: Box::new(result),
                    xor: input.parse()?,
                    right: Box::new(self.parse_expression_and(input)?),
                });
            } else {
                return Err(syn::Error::new(input.span(), "invalid expression"));
            }
        }

        Ok(result)
    }

    fn parse_colon_colon(
        &mut self,
        name: syn::Ident,
        input: &mut ParseStream,
    ) -> syn::Result<syn::Path> {
        let mut names = syn::Path::from(name);

        while input.peek(syn::Token![::]) {
            let colon = input.parse::<syn::Token![::]>()?;
            let name = input.parse::<syn::Ident>()?;
            names.segments.push_punct(colon);
            names.segments.push_value(name.into());
        }

        Ok(names)
    }

    fn parse_variable(&mut self, name: syn::Ident) -> syn::Result<Node> {
        let s = name.to_string();
        if is_register(&s) {
            if VEC_PATTERN.is_match(&s) {
                return Ok(Node::VecRegisterId(VecRegisterId::for_name(&name)));
            } else if GPR_PATTERN.is_match(&s) {
                return Ok(Node::RegisterId(RegisterId::for_name(&name)));
            } else if FPR_PATTERN.is_match(&s) {
                return Ok(Node::FPRegisterId(FPRegisterId::for_name(&name)));
            } else {
                return Err(syn::Error::new(name.span(), "invalid register name"));
            }
        } else if is_identifier(&s) {
            return Ok(Node::Variable(Variable {
                name,
                original: None,
            }));
        } else {
            return Err(syn::Error::new(name.span(), "invalid variable name"));
        }
    }

    pub fn parse_expression_atom(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        if input.peek(syn::Token![-]) {
            Ok(Node::NegImmediate(NegImmediate {
                minus: input.parse()?,
                value: Box::new(self.parse_expression_atom(input)?),
            }))
        } else if input.peek(syn::Token![~]) {
            Ok(Node::BitNotImmediate(BitNotImmediate {
                bitnot: input.parse()?,
                value: Box::new(self.parse_expression_atom(input)?),
            }))
        } else if input.peek(syn::token::Paren) {
            let content;
            let _ = syn::parenthesized!(content in input);
            let expr = self.parse_expression(&mut &content)?;
            Ok(expr)
        } else if input.peek(syn::LitInt) {
            let lit = input.parse::<syn::LitInt>()?;
            let val = lit.base10_parse::<isize>()?;
            Ok(Node::Immediate(Immediate { value: val }))
        } else if input.peek(syn::LitStr) {
            Ok(Node::StringLiteral(StringLiteral {
                string: input.parse()?,
            }))
        } else if input.peek(syn::Token![%]) {
            let _ = input.parse::<syn::Token![%]>()?;
            let ident = input.parse::<syn::Ident>()?;
            let _ = input.parse::<syn::Token![%]>()?;

            return Ok(Node::Variable(Variable {
                name: Ident::new(&format!("%{}%", ident.to_string()), ident.span()),
                original: None,
            }));
        } else if input.peek(syn::Token![const]) {
            let _ = input.parse::<syn::Token![const]>()?;
            let expr = input.parse::<syn::Expr>()?;
            return Ok(Node::Const(Const { expr }));
        } else if input.peek(syn::Token![=>]) {
            let _ = input.parse::<syn::Token![=>]>()?;
            let label = input.parse::<syn::Ident>()?;
            return Ok(Node::LocalLabelReference(LocalLabelReference::new(
                LocalLabel::for_name(&label),
            )));
        } else if input.peek(syn::Token![&]) {
            let _ = input.parse::<syn::Token![&]>()?;
            let label = input.parse::<syn::Ident>()?;
            return Ok(Node::LabelReference(LabelReference::new(
                LabelMapping::Global(Label::for_name(&label, false)),
                0,
            )));
        } else if input.peek(syn::Ident) {
            let id = input.parse::<syn::Ident>()?;

            let name = id.to_string();
            let name = name.as_str();
            if is_identifier(name) {
                let path = self.parse_colon_colon(id.clone(), input)?;
                if path.is_ident(&id) {
                    return Ok(Node::Variable(Variable {
                        name: id.clone(),
                        original: None,
                    }));
                } else {
                    return Ok(Node::StructOffset(StructOffset { path }));
                }
            } else if is_register(name) {
                return self.parse_variable(id);
            } else if name == "sizeof" {
                let ident = input.parse::<syn::Ident>()?;
                let path = self.parse_colon_colon(ident.clone(), input)?;
                return Ok(Node::SizeOf(SizeOf { type_name: path }));
            } else if name == "const" {
                let expr = input.parse::<syn::Expr>()?;
                return Ok(Node::Const(Const { expr }));
            } else {
                return Err(syn::Error::new(id.span(), "invalid label name"));
            }
        } else {
            return Err(syn::Error::new(input.span(), "invalid expression atom"));
        }
    }

    pub fn parse_expression_mul(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_expression_atom(input)?;

        while input.peek(syn::Token![*]) {
            if input.peek(syn::Token![*]) {
                result = Node::MulImmediates(MulImmediates {
                    left: Box::new(result),
                    times: input.parse()?,
                    right: Box::new(self.parse_expression_atom(input)?),
                })
            } else {
                return Err(syn::Error::new(input.span(), "invalid expression"));
            }
        }

        Ok(result)
    }

    pub fn parse_expression_add(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_expression_mul(input)?;

        while input.peek(syn::Token![+]) || input.peek(syn::Token![-]) {
            if input.peek(syn::Token![+]) {
                result = Node::AddImmediates(AddImmediates {
                    left: Box::new(result),
                    plus: input.parse()?,
                    right: Box::new(self.parse_expression_mul(input)?),
                });
            } else if input.peek(syn::Token![-]) {
                result = Node::SubImmediates(SubImmediates {
                    left: Box::new(result),
                    minus: input.parse()?,
                    right: Box::new(self.parse_expression_mul(input)?),
                });
            } else {
                return Err(syn::Error::new(input.span(), "invalid expression"));
            }
        }

        Ok(result)
    }

    pub fn parse_expression_and(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_expression_add(input)?;

        while input.peek(syn::Token![&]) {
            let _ = input.parse::<syn::Token![&]>()?;
            result = Node::AndImmediate(AndImmediate {
                left: Box::new(result),
                and: input.parse()?,
                right: Box::new(self.parse_expression_add(input)?),
            });
        }

        Ok(result)
    }

    pub fn parse_predicate_atom(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        if input.peek(syn::Ident) {
            let id = input.parse::<syn::Ident>()?;
            let name = id.to_string();
            let name = name.as_str();

            return Ok(Node::Setting(id));
        } else if input.peek(syn::Token![!]) {
            let _ = input.parse::<syn::Token![!]>()?;
            return Ok(Node::Not(Box::new(self.parse_predicate_atom(input)?)));
        } else if input.peek(syn::LitBool) {
            let lit = input.parse::<syn::LitBool>()?;
            if lit.value() {
                return Ok(Node::True);
            } else {
                return Ok(Node::False);
            }
        } else if input.peek(syn::token::Paren) {
            let content;
            let _ = syn::parenthesized!(content in input);
            let expr = self.parse_predicate(&mut &content)?;
            return Ok(expr);
        } else {
            return Err(syn::Error::new(input.span(), "invalid predicate atom"));
        }
    }

    pub fn parse_predicate_and(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_predicate_atom(input)?;

        while input.peek(syn::Token![&&]) {
            let _ = input.parse::<syn::Token![&&]>()?;
            result = Node::And(
                Box::new(result),
                Box::new(self.parse_predicate_atom(input)?),
            );
        }

        Ok(result)
    }

    pub fn parse_predicate(&mut self, input: &mut ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_predicate_and(input)?;

        while input.peek(syn::Token![||]) {
            let _ = input.parse::<syn::Token![||]>()?;
            result = Node::Or(Box::new(result), Box::new(self.parse_predicate_and(input)?));
        }

        Ok(result)
    }

    pub fn maybe_parse_doc(&mut self, input: &mut ParseStream) -> syn::Result<Option<String>> {
        if input.peek(syn::Token![#]) {
            let _ = input.parse::<syn::Token![#]>()?;
            let content;
            let _ = syn::bracketed!(content in input);
            let mvalue: syn::MetaNameValue = content.parse::<syn::MetaNameValue>()?;

            if mvalue.path.is_ident("doc") {
                let lit: syn::LitStr = match mvalue.value {
                    syn::Expr::Lit(lit) => match lit.lit {
                        syn::Lit::Str(lit) => lit,
                        _ => return Err(syn::Error::new(input.span(), "invalid doc")),
                    },
                    _ => return Err(syn::Error::new(input.span(), "invalid doc")),
                };

                return Ok(Some(lit.value()));
            }
        }
        Ok(None)
    }
}
