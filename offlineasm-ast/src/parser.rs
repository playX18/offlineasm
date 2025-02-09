use crate::instructions;
use crate::registers;
use std::collections::HashMap;
use std::rc::Rc;

use super::instructions::*;
use super::operands::*;
use super::stmt::*;
use syn::parse::{Parse, ParseStream};

impl Operand {
    pub fn peek_expression(input: ParseStream) -> bool {
        input.peek(syn::Token![-])
            || input.peek(syn::Token![+])
            || input.peek(syn::Token![<])
            || input.peek(syn::Token![&])
            || input.peek(syn::Token![=>])
            || input.peek(syn::Token![const])
            || input.peek(syn::Ident)
            || input.peek(syn::LitInt)
            || input.peek(syn::token::Paren)
    }

    fn parse_variable(input: ParseStream) -> syn::Result<Self> {
        if registers::peek_register(input) {
            if registers::peek_gprs(input) {
                let id = input.parse::<syn::Ident>()?;
                return Ok(GPRegister::new(id).into());
            } else if registers::peek_fprs(input) {
                let id = input.parse::<syn::Ident>()?;
                return Ok(FPRegister::new(id).into());
            } else if registers::peek_vecs(input) {
                let id = input.parse::<syn::Ident>()?;
                return Ok(VecRegister::new(id).into());
            } else {
                return Err(syn::Error::new(input.span(), "invalid register name"));
            }
        } else {
            Name::parse(input).map(Operand::Name)
        }
    }

    fn parse_expression_atom(input: ParseStream) -> syn::Result<Self> {
        let span = input.span();
        if input.peek(syn::Token![-]) {
            let _ = input.parse::<syn::Token![-]>()?;
            let value = Self::parse_expression_atom(input)?;
            return Ok(UnaryExpression {
                span,
                op: UnaryOperator::Neg,
                operand: value,
            }
            .into());
        } else if input.peek(syn::Token![+]) {
            let _ = input.parse::<syn::Token![+]>()?;
            let value = Self::parse_expression_atom(input)?;
            return Ok(value);
        } else if input.peek(syn::Token![!]) {
            let _ = input.parse::<syn::Token![!]>()?;
            let value = Self::parse_expression_atom(input)?;
            return Ok(UnaryExpression {
                span,
                op: UnaryOperator::Not,
                operand: value,
            }
            .into());
        } else if input.peek(syn::token::Paren) {
            let content;
            let _ = syn::parenthesized!(content in input);
            let expr = Self::parse_expression(&mut &content)?;
            return Ok(expr);
        } else if input.peek(syn::LitInt) {
            let lit = input.parse::<syn::LitInt>()?;
            let val = lit.base10_parse::<i64>()?;
            return Ok(val.into());
        } else if input.peek(syn::LitStr) {
            let lit = input.parse::<syn::LitStr>()?;
            return Ok(Constant {
                span,
                value: ConstantValue::String(lit.value().into()),
            }
            .into());
        } else if input.peek(syn::Token![&]) {
            let _ = input.parse::<syn::Token![&]>()?;
            let id = input.parse::<syn::Ident>()?;
            return Ok(LabelReference {
                span,
                label: LabelMapping::Global(Label::for_name(&id, false)?),
            }
            .into());
        } else if input.peek(syn::Token![=>]) {
            let _ = input.parse::<syn::Token![=>]>()?;
            let id = input.parse::<syn::Ident>()?;
            return Ok(LocalLabelReference {
                span,
                name: LocalLabel::for_name(&id)?,
            }
            .into());
        } else if registers::peek_register(input) {
            return Self::parse_variable(input);
        } else if input.peek(syn::Token![const]) {
            let _ = input.parse::<syn::Token![const]>()?;
            let expr = input.parse::<syn::Expr>()?;
            return Ok(Constant {
                span,
                value: ConstantValue::Expression(expr),
            }
            .into());
        } else {
            let id = input.parse::<syn::Ident>()?;
            if input.peek(syn::Token![.]) {
                todo!("struct offset");
            } else {
                return Ok(Name::Variable(Variable::new(id)).into());
            }
        }
    }

    fn parse_expression_mul(input: ParseStream) -> syn::Result<Self> {
        let mut result = Self::parse_expression_atom(input)?;

        while input.peek(syn::Token![*]) {
            let _ = input.parse::<syn::Token![*]>()?;
            let right = Self::parse_expression_atom(input)?;
            result = BinaryExpression {
                span: input.span(),
                op: BinaryOperator::Mul,
                lhs: result,
                rhs: right,
            }
            .into();
        }

        Ok(result)
    }

    fn parse_expression_add(input: ParseStream) -> syn::Result<Self> {
        let mut result = Self::parse_expression_mul(input)?;

        while input.peek(syn::Token![+]) || input.peek(syn::Token![-]) {
            let op = if input.peek(syn::Token![+]) {
                let _ = input.parse::<syn::Token![+]>()?;
                BinaryOperator::Add
            } else {
                let _ = input.parse::<syn::Token![-]>()?;
                BinaryOperator::Sub
            };

            let right = Self::parse_expression_mul(input)?;

            result = BinaryExpression {
                span: input.span(),
                op,
                lhs: result,
                rhs: right,
            }
            .into();
        }

        Ok(result)
    }

    fn parse_expression_and(input: ParseStream) -> syn::Result<Self> {
        let mut result = Self::parse_expression_add(input)?;

        while input.peek(syn::Token![&]) {
            let _ = input.parse::<syn::Token![&]>()?;
            let right = Self::parse_expression_add(input)?;
            result = BinaryExpression {
                span: input.span(),
                op: BinaryOperator::And,
                lhs: result,
                rhs: right,
            }
            .into();
        }

        Ok(result)
    }

    fn parse_expression(input: ParseStream) -> syn::Result<Self> {
        let mut result = Self::parse_expression_and(input)?;

        while input.peek(syn::Token![|]) || input.peek(syn::Token![^]) {
            if input.peek(syn::Token![|]) {
                let _ = input.parse::<syn::Token![|]>()?;
                let right = Self::parse_expression_and(input)?;
                result = BinaryExpression {
                    span: input.span(),
                    op: BinaryOperator::Or,
                    lhs: result,
                    rhs: right,
                }
                .into();
            } else if input.peek(syn::Token![^]) {
                let _ = input.parse::<syn::Token![^]>()?;
                let right = Self::parse_expression_and(input)?;
                result = BinaryExpression {
                    span: input.span(),
                    op: BinaryOperator::Xor,
                    lhs: result,
                    rhs: right,
                }
                .into();
            }
        }

        Ok(result)
    }
}

impl Parse for Operand {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if Operand::peek_expression(input) {
            let expr = Self::parse_expression(input)?;
            return Ok(expr);
        } else if input.peek(syn::token::Bracket) {
            return Address::parse(input).map(Address::into);
        } else {
            return Err(syn::Error::new(input.span(), "invalid operand"));
        }
    }
}

impl PredicateExpr {
    fn parse_atom(input: ParseStream) -> syn::Result<Self> {
        if input.peek(syn::Ident) {
            let name = input.parse::<syn::Ident>()?;
            return Ok(PredicateExpr::Setting(name));
        } else if input.peek(syn::Token![!]) {
            let _ = input.parse::<syn::Token![!]>()?;
            let expr = Self::parse_atom(input)?;
            return Ok(PredicateExpr::Not(Rc::new(expr)));
        } else if input.peek(syn::token::Paren) {
            let content;
            let _ = syn::parenthesized!(content in input);
            let expr = Self::parse(&mut &content)?;
            return Ok(expr);
        } else {
            return Err(syn::Error::new(input.span(), "invalid predicate atom"));
        }
    }

    fn parse_and(input: ParseStream) -> syn::Result<Self> {
        let mut result = Self::parse_atom(input)?;

        while input.peek(syn::Token![&&]) {
            let _ = input.parse::<syn::Token![&&]>()?;
            let right = Self::parse_atom(input)?;
            result = PredicateExpr::And(Rc::new(result), Rc::new(right));
        }

        Ok(result)
    }
}

impl Parse for PredicateExpr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut result = Self::parse_and(input)?;
        while input.peek(syn::Token![||]) {
            let _ = input.parse::<syn::Token![||]>()?;
            let right = Self::parse_and(input)?;
            result = PredicateExpr::Or(Rc::new(result), Rc::new(right));
        }

        Ok(result)
    }
}

pub mod kw {
    syn::custom_keyword!(abs);
    syn::custom_keyword!(settings);
}

impl Parse for Address {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let span = input.span();
        let content;
        let _ = syn::bracketed!(content in input);
        let input = &content;
        if content.peek(kw::abs) {
            let offset = Operand::parse(input)?;
            return Ok(Address {
                kind: AddressKind::Absolute { value: offset },
                span,
            });
        }

        let base = Operand::parse_expression_atom(input)?;

        if content.peek(syn::Token![+]) {
            let _ = content.parse::<syn::Token![+]>()?;
            let offset = Operand::parse_expression_atom(input)?;
            if content.peek(syn::Token![*]) {
                let _ = content.parse::<syn::Token![*]>()?;
                let index = offset;
                let scale: Operand;
                if content.peek(syn::LitInt) {
                    let vscale = content.parse::<syn::LitInt>()?;
                    let vscale = vscale.base10_parse::<u8>()?;
                    if matches!(vscale, 1 | 2 | 4 | 8) {
                        scale = (vscale as isize).into();
                    } else {
                        return Err(syn::Error::new(input.span(), "invalid scale"));
                    }
                } else if content.peek(syn::Token![const]) {
                    scale = content.parse::<Constant>()?.into();
                } else {
                    scale = Operand::parse_variable(input)?;
                };
                let offset;
                if content.peek(syn::Token![+]) | content.peek(syn::Token![-]) {
                    offset = Operand::parse_expression_atom(input)?;
                } else if !content.is_empty() {
                    return Err(syn::Error::new(input.span(), "invalid address"));
                } else {
                    offset = 0isize.into();
                }

                return Ok(Address {
                    kind: AddressKind::BaseIndex {
                        base,
                        index,
                        scale,
                        offset,
                    },
                    span,
                });
            } else if content.peek(syn::Token![-]) || content.peek(syn::Token![+]) {
                if content.peek(syn::Token![+]) {
                    let _ = content.parse::<syn::Token![+]>()?;
                }
                let index = offset;
                let offset = Operand::parse_expression_atom(input)?;
                return Ok(Address {
                    kind: AddressKind::BaseIndex {
                        base,
                        index,
                        scale: 1isize.into(),
                        offset,
                    },
                    span,
                });
            }
        } else if content.peek(syn::Token![-]) {
            let _ = content.parse::<syn::Token![-]>()?;
            let offset = Operand::parse_expression_atom(input)?;
            return Ok(Address {
                kind: AddressKind::Base { base, offset },
                span,
            }
            .into());
        }

        return Err(syn::Error::new(input.span(), "invalid address"));
    }
}

impl Parse for Constant {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(syn::LitInt) {
            let lit = input.parse::<syn::LitInt>()?;
            let val = lit.base10_parse::<i64>()?;
            return Ok(Constant {
                span: input.span(),
                value: ConstantValue::Immediate(val as i64),
            });
        } else if input.peek(syn::LitStr) {
            let lit = input.parse::<syn::LitStr>()?;
            return Ok(Constant {
                span: input.span(),
                value: ConstantValue::String(lit.value().into()),
            });
        } else if input.peek(syn::Token![const]) {
            let expr = input.parse::<syn::Expr>()?;
            return Ok(Constant {
                span: input.span(),
                value: ConstantValue::Expression(expr),
            });
        } else {
            return Err(syn::Error::new(input.span(), "invalid constant"));
        }
    }
}

impl Parse for Macro {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let span = input.span();
        let _ = input.parse::<syn::Token![macro]>()?;
        let name = input.parse::<syn::Ident>()?;

        let content;
        let _ = syn::parenthesized!(content in input);
        /*while !content.is_empty() {
            let arg = content.parse::<syn::Ident>()?;
            args.push(Variable::new(arg));
        }*/
        let args = content
            .parse_terminated(Variable::parse, syn::Token![,])?
            .into_iter()
            .collect();

        let sequence = Sequence::parse(input)?;

        Ok(Self {
            span,
            name,
            args,
            body: sequence,
        })
    }
}

impl Parse for Sequence {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        let _ = syn::braced!(content in input);
        let mut stmts = Vec::new();
        while !content.is_empty() {
            match Stmt::parse(&mut &content)? {
                /* flatten nested sequences */
                Stmt::Sequence(seq) => stmts.extend(seq.stmts.clone().into_iter()),
                stmt => stmts.push(stmt),
            }
        }
        Ok(Self {
            span: input.span(),
            stmts,
        })
    }
}

impl Parse for ConstDecl {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let span = input.span();
        let _ = input.parse::<syn::Token![const]>()?;
        let name = input.parse::<syn::Ident>()?;
        let _ = input.parse::<syn::Token![=]>()?;
        let value = Operand::parse(input)?;
        let _ = input.parse::<syn::Token![;]>()?;
        Ok(Self { span, name, value })
    }
}

impl Parse for Predicate {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let span = input.span();
        let _ = input.parse::<syn::Token![if]>()?;
        let expr = PredicateExpr::parse(input)?;
        let then = Stmt::parse(input)?;
        let else_case = if input.peek(syn::Token![else]) {
            let _ = input.parse::<syn::Token![else]>()?;
            Some(Stmt::parse(input)?)
        } else {
            None
        };
        Ok(Self {
            span,
            expr,
            then,
            else_case,
        })
    }
}

impl Parse for MacroArgument {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(syn::Token![macro]) {
            return input
                .parse::<Macro>()
                .map(Rc::new)
                .map(MacroArgument::Macro);
        } else {
            let variable = Operand::parse(input)?;
            return Ok(MacroArgument::Operand(variable));
        }
    }
}

impl Parse for Variable {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let id = input.parse::<syn::Ident>()?;
        Ok(Self {
            name: id,
            original: None,
        })
    }
}

impl Parse for Name {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(syn::Token![<]) {
            let _ = input.parse::<syn::Token![<]>()?;
            let mut parts = Vec::new();
            while !input.is_empty() || !input.peek(syn::Token![>]) {
                if input.peek(syn::Token![@]) {
                    let _ = input.parse::<syn::Token![@]>()?;
                    let id = Variable::parse(input)?;
                    parts.push(ConcatenationElement::Variable(id));
                } else {
                    let id = input.parse::<syn::Ident>()?;
                    parts.push(ConcatenationElement::Ident(id));
                }
            }
            let _ = input.parse::<syn::Token![>]>()?;
            return Ok(Name::Concatenation(Concatenation {
                span: input.span(),
                elements: parts,
            }));
        } else {
            let id = input.parse::<syn::Ident>()?;
            return Ok(Name::Variable(Variable::new(id)));
        }
    }
}

impl Parse for MacroCall {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let span = input.span();
        let _ = input.parse::<syn::Token![macro]>()?;
        let name = input.parse::<syn::Ident>()?;

        let content;
        let _ = syn::parenthesized!(content in input);

        let args = content.parse_terminated(MacroArgument::parse, syn::Token![,])?;
        Ok(Self {
            span,
            name,
            original_name: None,
            arguments: args.into_iter().collect(),
        })
    }
}

impl Parse for Stmt {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(kw::settings) {
            return Err(syn::Error::new(
                input.span(),
                "settings can only be declared at the top level",
            ));
        }

        if input.peek(syn::Token![macro]) {
            return Macro::parse(input).map(Rc::new).map(Stmt::Macro);
        } else if input.peek(syn::Token![const]) {
            return ConstDecl::parse(input).map(Rc::new).map(Stmt::ConstDecl);
        } else if input.peek(syn::Token![if]) {
            return Predicate::parse(input).map(Rc::new).map(Stmt::Predicate);
        } else if input.peek(syn::Token![move]) {
            let _ = input.parse::<syn::Token![move]>()?;
            let dst = input.parse::<Operand>()?;
            let _ = input.parse::<syn::Token![,]>()?;
            let src = input.parse::<Operand>()?;
            return Ok(Stmt::Instruction(Rc::new(Instruction::Mv(Mv {
                span: input.span(),
                dst,
                src,
            }))));
        } else if instructions::Instruction::peek(input) {
            return Instruction::parse(input)
                .map(Rc::new)
                .map(Stmt::Instruction);
        } else if input.peek(syn::Token![->]) {
            let _ = input.parse::<syn::Token![->]>()?;
            let name = input.parse::<syn::Ident>()?;

            let _ = input.parse::<syn::Token![:]>()?;
            return Label::for_name(&name, true).map(Stmt::Label);
        } else if input.peek(syn::Ident) && input.peek2(syn::Token![:]) {
            let name = input.parse::<syn::Ident>()?;
            let _ = input.parse::<syn::Token![:]>()?;
            return LocalLabel::for_name(&name).map(Stmt::LocalLabel);
        } else if input.peek(syn::token::Brace) {
            return Sequence::parse(input).map(Rc::new).map(Stmt::Sequence);
        } else if input.peek(syn::Ident) && input.peek2(syn::token::Paren) {
            let name = input.parse::<syn::Ident>()?;
            let content;
            let _ = syn::parenthesized!(content in input);
            let args = content.parse_terminated(MacroArgument::parse, syn::Token![,])?;
            return Ok(Stmt::MacroCall(Rc::new(MacroCall {
                span: input.span(),
                name,
                original_name: None,
                arguments: args.into_iter().collect(),
            })));
        } else {
            return Err(syn::Error::new(
                input.span(),
                &format!("invalid statement: {input}"),
            ));
        }
    }
}

impl Parse for Toplevel {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut stmts = Vec::new();
        let mut settings = HashMap::new();
        let mut resolved_settings = HashMap::new();

        if input.peek(kw::settings) {
            let _ = input.parse::<kw::settings>()?;
            let content;
            let _ = syn::braced!(content in input);
            while !content.is_empty() {
                let name = content.parse::<syn::Ident>()?;
                let _ = content.parse::<syn::Token![=]>()?;
                if content.peek(syn::LitBool) {
                    let value = content.parse::<syn::LitBool>()?;
                    resolved_settings.insert(name, value.value());
                } else {
                    let value = content.parse::<syn::Meta>()?;
                    settings.insert(name, value);
                }
            }
        }
        while !input.is_empty() {
            stmts.push(Stmt::parse(input)?);
        }
        Ok(Self {
            stmts,
            settings,
            resolved_settings,
        })
    }
}

pub fn peek_not_operand(input: ParseStream) -> bool {
    Instruction::peek(input)
        || input.peek(syn::Token![->])
        || (input.peek(syn::Ident) && input.peek2(syn::Token![:]))
        || input.peek(syn::Token![macro])
        || input.peek(syn::Token![move])
        || input.peek(syn::Token![if])
        || (input.peek(syn::Token![const])
            && input.peek2(syn::Ident)
            && input.peek3(syn::Token![=]))
        || input.peek(syn::token::Brace)
}
