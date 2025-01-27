use std::{collections::HashMap, rc::Rc};

use proc_macro2::Span;
use syn::Ident;

use crate::{instructions::*, operands::*, stmt::*};

impl Instruction {
    fn substitute(&self, mapping: &HashMap<Variable, Operand>) -> syn::Result<Self> {
        self.try_map_operands(|op| op.substitute(mapping))
    }

    fn rename_labels(&self, mapping: &HashMap<Rc<LocalLabel>, Rc<LocalLabel>>) -> syn::Result<Self> {
        self.try_map_operands(|op| op.rename_labels(mapping))
    }
}

impl Name {
    fn substitute(&self, mapping: &HashMap<Variable, Operand>) -> syn::Result<Operand> {
        match self {
            Self::Variable(var) => {
                if let Some(op) = mapping.get(var) {
                    return Ok(op.clone());
                }

                Ok(self.clone().into())
            }

            Self::Concatenation(concat) => {
                let mut new_concat = vec![];
                let mut has_unresolved = false;
                for op in concat.elements.iter() {
                    match op {
                        ConcatenationElement::Ident(_) => new_concat.push(op.clone()),
                        ConcatenationElement::Variable(var) => {
                            if let Some(Operand::Name(Name::Variable(new_var))) = mapping.get(var) {
                                new_concat.push(ConcatenationElement::Ident(new_var.name.clone()));
                            } else {
                                has_unresolved = true;
                                new_concat.push(op.clone())
                            }
                        }
                    }
                }

                if has_unresolved {
                    return Ok(Operand::Name(Name::Concatenation(Concatenation {
                        span: concat.span.clone(),
                        elements: new_concat,
                    })));
                } else {
                    let mut output = String::new();

                    for op in new_concat.iter() {
                        output.push_str(&op.to_string());
                    }

                    Ok(Operand::Name(Name::Variable(Variable {
                        name: Ident::new(&output, concat.span.clone()),
                        original: None,
                    })))
                }
            }
        }
    }
}

impl Address {
    pub fn substitute(&self, mapping: &HashMap<Variable, Operand>) -> syn::Result<Self> {
        match &self.kind {
            AddressKind::Absolute { value } => {
                let value = value.substitute(mapping)?;
                Ok(Self {
                    kind: AddressKind::Absolute { value },
                    span: self.span.clone(),
                })
            }

            AddressKind::Base { base, offset } => {
                let base = base.substitute(mapping)?;
                let offset = offset.substitute(mapping)?;
                Ok(Self {
                    kind: AddressKind::Base { base, offset },
                    span: self.span.clone(),
                })
            }

            AddressKind::BaseIndex {
                base,
                index,
                scale,
                offset,
            } => {
                let base = base.substitute(mapping)?;
                let index = index.substitute(mapping)?;
                let scale = scale.substitute(mapping)?;
                let offset = offset.substitute(mapping)?;
                Ok(Self {
                    kind: AddressKind::BaseIndex {
                        base,
                        index,
                        scale,
                        offset,
                    },
                    span: self.span.clone(),
                })
            }
        }
    }

    fn rename_labels(
        &self,
        mapping: &HashMap<Rc<LocalLabel>, Rc<LocalLabel>>,
    ) -> syn::Result<Self> {
        match &self.kind {
            AddressKind::Base { base, offset } => {
                let base = base.rename_labels(mapping)?;
                let offset = offset.rename_labels(mapping)?;
                Ok(Self {
                    kind: AddressKind::Base { base, offset },
                    span: self.span.clone(),
                })
            }

            AddressKind::BaseIndex {
                base,
                index,
                scale,
                offset,
            } => {
                let base = base.rename_labels(mapping)?;
                let index = index.rename_labels(mapping)?;
                let scale = scale.rename_labels(mapping)?;
                let offset = offset.rename_labels(mapping)?;
                Ok(Self {
                    kind: AddressKind::BaseIndex {
                        base,
                        index,
                        scale,
                        offset,
                    },
                    span: self.span.clone(),
                })
            }

            AddressKind::Absolute { value } => {
                let value = value.rename_labels(mapping)?;
                Ok(Self {
                    kind: AddressKind::Absolute { value },
                    span: self.span.clone(),
                })
            }
        }
    }
}

impl Operand {
    fn rename_labels(
        &self,
        mapping: &HashMap<Rc<LocalLabel>, Rc<LocalLabel>>,
    ) -> syn::Result<Self> {
        match self {
            Self::Address(addr) => Ok(Self::Address(Rc::new(addr.rename_labels(mapping)?))),
            Self::LabelReference(label_ref) => match &label_ref.label {
                LabelMapping::Global(_) => Ok(self.clone()),
                LabelMapping::Local(local) => {
                    if let Some(new_label) = mapping.get(local) {
                        Ok(Self::LabelReference(Rc::new(LabelReference {
                            label: LabelMapping::Local(new_label.clone()),
                            span: label_ref.span.clone(),
                        })))
                    } else {
                        Ok(self.clone())
                    }
                }
            },
            Self::LocalLabelReference(local_ref) => {
                if let Some(new_label) = mapping.get(&local_ref.name) {
                    Ok(Self::LocalLabelReference(Rc::new(LocalLabelReference {
                        name: new_label.clone(),
                        span: local_ref.span.clone(),
                    })))
                } else {
                    Ok(self.clone())
                }
            }
            _ => Ok(self.clone()),
        }
    }

    fn substitute(&self, mapping: &HashMap<Variable, Operand>) -> syn::Result<Self> {
        Ok(match self {
            Self::Address(addr) => Self::Address(Rc::new(addr.substitute(mapping)?)),
            Self::GPRegister(reg) => Self::GPRegister(reg.clone()),
            Self::FPRegister(reg) => Self::FPRegister(reg.clone()),
            Self::Name(name) => name.substitute(mapping)?,
            _ => self.clone(),
        })
    }

    pub fn try_immediate(&self) -> Option<u64> {
        match self {
            Self::Constant(c) => match c.value {
                ConstantValue::Immediate(i) => Some(i),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn fold(&self, constants: &HashMap<Ident, Operand>) -> syn::Result<Self> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(c.clone())),
            Self::BinaryExpression(expr) => {
                let left = expr.lhs.fold(constants)?;
                let right = expr.rhs.fold(constants)?;

                let left = left.try_immediate().ok_or_else(|| syn::Error::new(expr.span, "Left operand is not an immediate"))?;
                let right = right.try_immediate().ok_or_else(|| syn::Error::new(expr.span, "Right operand is not an immediate"))?;

                match expr.op {
                    BinaryOperator::Add => Ok(Self::Constant(Constant {
                        value: ConstantValue::Immediate(left.wrapping_add(right)),
                        span: expr.span.clone(),
                    })),
                    BinaryOperator::Sub => Ok(Self::Constant(Constant {
                        value: ConstantValue::Immediate(left.wrapping_sub(right)),
                        span: expr.span.clone(),
                    })),
                    BinaryOperator::Mul => Ok(Self::Constant(Constant {
                        value: ConstantValue::Immediate(left.wrapping_mul(right)),
                        span: expr.span.clone(),
                    })),
                    BinaryOperator::And => Ok(Self::Constant(Constant {
                        value: ConstantValue::Immediate(left & right),
                        span: expr.span.clone(),
                    })),

                    BinaryOperator::Or => Ok(Self::Constant(Constant {
                        value: ConstantValue::Immediate(left | right),
                        span: expr.span.clone(),
                    })),

                    BinaryOperator::Xor => Ok(Self::Constant(Constant {
                        value: ConstantValue::Immediate(left ^ right),
                        span: expr.span.clone(),
                    })),

                    _ => Err(syn::Error::new(expr.span, "Unsupported binary operator")),
                }
            }

            Operand::UnaryExpression(expr) => {
                let operand = expr.operand.fold(constants)?;
                let operand = operand.try_immediate().ok_or_else(|| syn::Error::new(expr.span, "Operand is not an immediate"))? as i64;

                match expr.op {
                    UnaryOperator::Neg => Ok(Self::Constant(Constant {
                        value: ConstantValue::Immediate(operand.wrapping_neg() as u64),
                        span: expr.span.clone(),
                    })),
                    UnaryOperator::Not => Ok(Self::Constant(Constant {
                        value: ConstantValue::Immediate(!(operand as u64)),
                        span: expr.span.clone(),
                    })),
                }
            }

            Operand::Address(addr) => {
                match &addr.kind {
                    AddressKind::Absolute { value } => {
                        let value = value.fold(constants)?;
                        Ok(Self::Address(Rc::new(Address {
                            kind: AddressKind::Absolute { value },
                            span: addr.span.clone(),
                        })))
                    }

                    AddressKind::Base { base, offset } => {
                        let base = base.fold(constants)?;
                        let offset = offset.fold(constants)?;
                        Ok(Self::Address(Rc::new(Address {
                            kind: AddressKind::Base { base, offset },
                            span: addr.span.clone(),
                        })))
                    }

                    AddressKind::BaseIndex { base, index, scale, offset } => {
                        let base = base.fold(constants)?;
                        let index = index.fold(constants)?;
                        let scale = scale.fold(constants)?;
                        let offset = offset.fold(constants)?;
                        Ok(Self::Address(Rc::new(Address {
                            kind: AddressKind::BaseIndex { base, index, scale, offset },
                            span: addr.span.clone(),
                        })))
                    }
                }
            }

            Operand::Name(name) => match name {
                Name::Variable(var) => {
                    if let Some(op) = constants.get(&var.name) {
                        Ok(op.clone())
                    } else {
                        Ok(self.clone())
                    }
                }
                _ => Ok(self.clone()),  
            }

            _ => Ok(self.clone()),
        }
    }
}

impl Stmt {
    fn substitute(&self, mapping: &HashMap<Variable, Operand>) -> syn::Result<Self> {
        match self {
            Self::Sequence(seq) => Ok(Self::Sequence(Rc::new(seq.substitute(mapping)?))),
            Self::Instruction(instr) => Ok(Self::Instruction(Rc::new(instr.substitute(mapping)?))),
            _ => Ok(self.clone()),
        }
    }

    pub fn demacroify(&self, macros: &HashMap<Ident, Rc<Macro>>) -> syn::Result<Self> {
        match self {
            Self::MacroCall(call) => {
                let mut mapping = HashMap::new();
                let mut my_macros = macros.clone();
                let macro_ = macros.get(&call.name).ok_or_else(|| {
                    for (name, macro_) in macros.iter() {
                        println!("{} {}", macro_, name == &call.name);
                    }
                    syn::Error::new(call.span, &format!("Macro {} not found", call.name))
                })?;
                if macro_.args.len() != call.arguments.len() {
                    return Err(syn::Error::new(
                        call.span,
                        &format!(
                            "Macro {} has {} arguments, but {} were provided",
                            call.name,
                            macro_.args.len(),
                            call.arguments.len()
                        ),
                    ));
                }

                for (argument, mvar) in call.arguments.iter().zip(macro_.args.iter()) {
                    match argument {
                        MacroArgument::Operand(operand) => match operand {
                            Operand::Name(Name::Variable(var)) => {
                                if let Some(m) = macros.get(&var.name) {
                                    my_macros.insert(mvar.name.clone(), m.clone());
                                } else {
                                    mapping.insert(mvar.clone(), operand.clone());
                                }
                            }
                            _ => {
                                mapping.insert(mvar.clone(), operand.clone());
                            }
                        },

                        MacroArgument::Macro(lambda) => {
                            println!("lambda macro {}", lambda);
                            my_macros.insert(mvar.name.clone(), lambda.clone());
                            mapping.remove(mvar);
                        }
                    }
                }

                let expansion = macro_
                    .body
                    .substitute(&mapping)?
                    .demacroify(&my_macros)?
                    .rename_labels(&HashMap::new())?;

                Ok(Stmt::Sequence(Rc::new(expansion)))
            }

            Self::Sequence(seq) => Ok(Self::Sequence(Rc::new(seq.demacroify(macros)?))),
            _ => Ok(self.clone()),
        }
    }

    fn rename_labels(
        &self,
        mapping: &HashMap<Rc<LocalLabel>, Rc<LocalLabel>>,
    ) -> syn::Result<Self> {
        match self {
            Self::Sequence(seq) => Ok(Self::Sequence(Rc::new(seq.rename_labels(mapping)?))),
            Self::LocalLabel(l) => {
                if let Some(new_label) = mapping.get(l) {
                    Ok(Self::LocalLabel(new_label.clone()))
                } else {
                    Ok(self.clone())
                }
            }
            Self::Instruction(instr) => {
                Ok(Self::Instruction(Rc::new(instr.rename_labels(mapping)?)))
            }
            _ => Ok(self.clone()),
        }
    }

    pub fn fold(&self, constants: &HashMap<Ident, Operand>) -> syn::Result<Self> {
        match self {
            Self::Sequence(seq) => {
                let mut new_list = Vec::new();
                let mut my_constants = constants.clone();
                for item in seq.stmts.iter() {
                    if let Stmt::ConstDecl(decl) = item {
                        my_constants.insert(decl.name.clone(), decl.value.clone());
                    } else {
                        new_list.push(item.fold(&my_constants)?);
                    }
                }
                Ok(Self::Sequence(Rc::new(Sequence {
                    span: seq.span.clone(),
                    stmts: new_list,
                })))
            }

            Self::ConstDecl(decl) => {
                let value = decl.value.fold(constants)?;
                Ok(Self::ConstDecl(Rc::new(ConstDecl {
                    name: decl.name.clone(),
                    value,
                    span: decl.span.clone(),
                })))
            }

            Self::Instruction(instr) => {
                Ok(Self::Instruction(Rc::new(instr.try_map_operands(|op| op.fold(constants))?)))
            }
            _ => Ok(self.clone()),
        }
    }
}

impl Sequence {
    fn substitute(&self, mapping: &HashMap<Variable, Operand>) -> syn::Result<Self> {
        let mut new_list = Vec::new();
        for item in self.stmts.iter() {
            new_list.push(item.substitute(mapping)?);
        }
        Ok(Self {
            span: self.span.clone(),
            stmts: new_list,
        })
    }

    fn demacroify(&self, macros: &HashMap<Ident, Rc<Macro>>) -> syn::Result<Self> {
        let mut new_list = Vec::new();
        let mut my_macros = macros.clone();
        for item in self.stmts.iter() {
            if let Stmt::Macro(m) = item {
                my_macros.insert(m.name.clone(), m.clone());
            }
        }
        for item in self.stmts.iter() {
            let expanded = item.demacroify(&my_macros)?;
            if let Stmt::Sequence(seq) = expanded {
                for stmt in seq.stmts.iter() {
                    new_list.push(stmt.clone());
                }
            } else {
                new_list.push(expanded);
            }
        }
        Ok(Self {
            span: self.span.clone(),
            stmts: new_list,
        })
    }

    fn rename_labels(
        &self,
        mapping: &HashMap<Rc<LocalLabel>, Rc<LocalLabel>>,
    ) -> syn::Result<Self> {
        let mut my_mapping = mapping.clone();

        for item in self.stmts.iter() {
            if let Stmt::LocalLabel(l) = item {
                my_mapping.insert(l.clone(), LocalLabel::unique(&l.name.to_string()));
            }
        }

        let mut new_list = Vec::new();
        for item in self.stmts.iter() {
            new_list.push(item.rename_labels(&my_mapping)?);
        }
        Ok(Self {
            span: self.span.clone(),
            stmts: new_list,
        })
    }
}

pub fn prepass(toplevel: &Toplevel) -> syn::Result<Sequence> {
    let seq = Sequence {
        stmts: toplevel.stmts.clone(),
        span: Span::call_site(),
    };
    
    Ok(seq
        .demacroify(&HashMap::new())?
        .rename_labels(&HashMap::new())?
    )
}
