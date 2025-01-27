use std::{
    collections::HashMap,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, LazyLock,
    },
};

use proc_macro2::Span;
use regex::{Captures, Regex};
use syn::{punctuated::Punctuated, Ident, Path, PathArguments, PathSegment};

use crate::ast::*;

impl From<bool> for Node {
    fn from(value: bool) -> Self {
        if value {
            Node::True
        } else {
            Node::False
        }
    }
}

impl Into<bool> for Node {
    fn into(self) -> bool {
        match self {
            Node::True => true,
            Node::False => false,
            _ => panic!("Cannot convert non-boolean node to bool"),
        }
    }
}

impl Node {
    pub fn resolve_settings(&self, settings: &HashMap<Ident, bool>) -> Node {
        match self {
            Node::Setting(x) => {
                let res = settings.get(&x).copied().unwrap().into();
                println!("resolve {}->{}", x, res);
                res
            }
            Node::True => true.into(),
            Node::False => false.into(),
            Node::And(lhs, rhs) => {
                let lhs: bool = lhs.resolve_settings(settings).into();
                let rhs: bool = rhs.resolve_settings(settings).into();
                (lhs && rhs).into()
            }
            Node::Or(lhs, rhs) => {
                let lhs: bool = lhs.resolve_settings(settings).into();
                let rhs: bool = rhs.resolve_settings(settings).into();
                (lhs || rhs).into()
            }

            Node::Not(x) => {
                let res: bool = x.resolve_settings(settings).into();
                (!res).into()
            }
            Node::IfThenElse(if_then_else) => {
                let mut if_then_else = if_then_else.clone();
                let res = if_then_else.predicate.resolve_settings(settings);
                let res: bool = res.into();
                if res {
                    return if_then_else.then.resolve_settings(settings);
                } else if let Some(else_case) = &mut if_then_else.else_case.as_mut() {
                    return else_case.resolve_settings(settings);
                } else {
                    return Node::Seq(Vec::new());
                }
            }

            Node::Seq(seq) => {
                let mut new_list = Vec::new();

                for item in seq.iter() {
                    let item = item.resolve_settings(settings);
                    if let Node::Seq(seq) = item {
                        for item in seq.iter().cloned() {
                            new_list.push(item);
                        }
                    } else {
                        new_list.push(item.clone());
                    }
                }
                Self::Seq(new_list)
            }
            Node::MacroCall(m) => Node::MacroCall(MacroCall {
                name: m.name.clone(),
                original_name: m.original_name.clone(),
                args: m
                    .args
                    .iter()
                    .map(|arg| arg.resolve_settings(settings))
                    .collect(),
            }),

            Node::Macro(m) => Node::Macro(Macro {
                name: m.name.clone(),
                args: m.args.clone(),
                body: Box::new(m.body.resolve_settings(settings)),
            }),

            _ => self.clone(),
        }
    }
}

static FRESH_VARIABLE_ID: AtomicUsize = AtomicUsize::new(0);

impl Macro {
    pub fn fresh_variables(&self, mapping: &mut HashMap<Variable, Node>) -> Macro {
        let mut my_mapping = mapping.clone();
        let mut new_vars = Punctuated::new();

        self.args.iter().for_each(|var| {
            let id = FRESH_VARIABLE_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let new_var = Variable {
                name: Ident::new(&format!("_var_{id}"), Span::call_site()),
                original: Some(var.original()),
            };
            new_vars.push(new_var.clone());
            my_mapping.insert(var.clone(), Node::Variable(new_var));
        });

        let body = self.body.fresh_variables(&mut my_mapping);
        Macro {
            name: self.name.clone(),
            args: new_vars,
            body: Box::new(body),
        }
    }

    pub fn substitute(&self, mapping: &mut HashMap<Variable, Node>) -> Node {
        let mut my_mapping = HashMap::new();
        for (k, v) in mapping.iter() {
            if !self.args.iter().any(|arg| arg == k) {
                my_mapping.insert(k.clone(), v.clone());
            }
        }

        self.body.substitute(&mut my_mapping)
    }
}

impl MacroCall {
    fn fresh_variables(&self, mapping: &mut HashMap<Variable, Node>) -> MacroCall {
        let mut new_name = Variable {
            name: self.name.clone(),
            original: Some(self.original_name()),
        };
        if let Some(Node::Variable(var)) = mapping.get(&new_name) {
            new_name = var.clone();
        }

        let new_operands = self
            .args
            .iter()
            .map(|arg| arg.fresh_variables(mapping))
            .collect();
        MacroCall {
            name: new_name.name,
            original_name: Some(self.original_name()),
            args: new_operands,
        }
    }
}
static CONCATENATION: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"%([a-zA-Z0-9_]+)%").unwrap());
impl Variable {
    pub fn fresh_variables(&self, mapping: &mut HashMap<Variable, Node>) -> Variable {
        let name_str = self.name.to_string();
        if CONCATENATION.is_match(&name_str) {
            let name = CONCATENATION.replace(&name_str, |captures: &Captures| {
                let var = captures.get(0).unwrap().as_str();
                let var = Variable {
                    name: Ident::new(&format!("_var_{}", var), Span::call_site()),
                    original: None,
                };
                if let Some(Node::Variable(var)) = mapping.get(&var) {
                    return format!("%{}", var.name.to_string());
                }
                var.to_string()
            });

            let mut new_name = Variable {
                name: Ident::new(&name, Span::call_site()),
                original: None,
            };

            new_name
        } else if let Some(Node::Variable(var)) = mapping.get(&self) {
            return var.clone();
        } else {
            return self.clone();
        }
    }

    pub fn substitute(&self, mapping: &mut HashMap<Variable, Node>) -> Node {
        if CONCATENATION.is_match(&self.name.to_string()) {
            let n = self.name.to_string();
            let name = CONCATENATION.replace(&n, |captures: &Captures| {
                let var = captures.get(0).unwrap().as_str();
                let var = Variable {
                    name: Ident::new(&var, Span::call_site()),
                    original: None,
                };
                match mapping.get(&var) {
                    Some(Node::Variable(var)) => return var.name.to_string(),
                    _ => return var.to_string(),
                }
            });

            Node::Variable(Variable {
                name: Ident::new(&name, Span::call_site()),
                original: None,
            })
        } else if let Some(sub) = mapping.get(&self) {
            return sub.clone();
        } else {
            return Node::Variable(self.clone());
        }
    }
}

impl StructOffset {
    pub fn fresh_variables(&self, mapping: &mut HashMap<Variable, Node>) -> StructOffset {
        let mut path = Path {
            leading_colon: None,
            segments: Punctuated::new(),
        };

        for seg in self.path.segments.iter() {
            let name = seg.ident.to_string();
            if CONCATENATION.is_match(&name) {
                let name = CONCATENATION.replace(&name, |captures: &Captures| {
                    let var = captures.get(0).unwrap().as_str();
                    let var = Variable {
                        name: Ident::new(&var, Span::call_site()),
                        original: None,
                    };
                    if let Some(Node::Variable(var)) = mapping.get(&var) {
                        return format!("%{}", var.name.to_string());
                    }
                    var.to_string()
                });

                path.segments.push(PathSegment {
                    ident: Ident::new(&name, Span::call_site()),
                    arguments: PathArguments::None,
                });
            }
        }

        Self { path }
    }

    pub fn substitute(&self, mapping: &mut HashMap<Variable, Node>) -> StructOffset {
        let mut path = self.path.clone();
        for seg in path.segments.iter_mut() {
            let name = seg.ident.to_string();
            if CONCATENATION.is_match(&name) {
                let name = CONCATENATION.replace(&name, |captures: &Captures| {
                    let var = captures.get(0).unwrap().as_str();
                    let var = Variable {
                        name: Ident::new(&var, Span::call_site()),
                        original: None,
                    };
                    match mapping.get(&var) {
                        Some(Node::Variable(var)) => return var.name.to_string(),
                        _ => return var.to_string(),
                    }
                });

                seg.ident = Ident::new(&name, Span::call_site());
            }
        }
        Self { path }
    }
}

impl Label {
    pub fn fresh_variables(self: &Arc<Self>, mapping: &mut HashMap<Variable, Node>) -> Arc<Self> {
        let name = self.name().to_string();
        if CONCATENATION.is_match(&name) {
            let name = CONCATENATION.replace(&name, |captures: &Captures| {
                let var = Variable {
                    name: Ident::new(&captures.get(0).unwrap().as_str(), Span::call_site()),
                    original: None,
                };
                if let Some(Node::Variable(var)) = mapping.get(&var) {
                    return format!("%{}", var.name.to_string());
                }
                var.to_string()
            });

            let result =
                Label::for_name(&Ident::new(&name, Span::call_site()), self.defined_in_macro);
            if self.is_global() {
                result.set_global();
            }

            if !self.is_aligned() && self.is_global() {
                result.aligned.store(false, Ordering::Relaxed);
                result.set_global();
            }
            if self.is_aligned() && self.aligned_to() != 0 {
                result.set_aligned_to(self.aligned_to());
            }

            if !self.is_extern() {
                result.extern_.store(false, Ordering::Relaxed);
            }
            return result;
        }

        self.clone()
    }

    pub fn substitute(self: &Arc<Self>, mapping: &mut HashMap<Variable, Node>) -> Arc<Self> {
        let name = self.name().to_string();
        if CONCATENATION.is_match(&name) {
            let name = CONCATENATION.replace(&name, |captures: &Captures| {
                let var = captures.get(0).unwrap().as_str();
                let var = Variable {
                    name: Ident::new(&var, Span::call_site()),
                    original: None,
                };
                if let Some(Node::Variable(var)) = mapping.get(&var) {
                    return var.name.to_string();
                } else {
                    return var.to_string();
                }
            });

            let result =
                Label::for_name(&Ident::new(&name, Span::call_site()), self.defined_in_macro);
            if self.is_global() {
                result.set_global();
            }

            if !self.is_aligned() && self.is_global() {
                result.aligned.store(false, Ordering::Relaxed);
                result.set_global();
            }
            if self.is_aligned() && self.aligned_to() != 0 {
                result.set_aligned_to(self.aligned_to());
            }

            if !self.is_extern() {
                result.extern_.store(false, Ordering::Relaxed);
            }
            return result;
        }

        self.clone()
    }
}

impl SizeOf {
    pub fn fresh_variables(&self, mapping: &mut HashMap<Variable, Node>) -> SizeOf {
        let mut path = self.type_name.clone();

        for seg in path.segments.iter_mut() {
            let name = seg.ident.to_string();
            if CONCATENATION.is_match(&name) {
                let name = CONCATENATION.replace(&name, |captures: &Captures| {
                    let var = captures.get(0).unwrap().as_str();
                    let var = Variable {
                        name: Ident::new(&var, Span::call_site()),
                        original: None,
                    };
                    if let Some(Node::Variable(var)) = mapping.get(&var) {
                        return format!("%{}", var.name.to_string());
                    } else {
                        return var.to_string();
                    }
                });
                seg.ident = Ident::new(&name, Span::call_site());
            }
        }

        SizeOf { type_name: path }
    }

    pub fn substitute(&self, mapping: &mut HashMap<Variable, Node>) -> SizeOf {
        let mut path = self.type_name.clone();
        for seg in path.segments.iter_mut() {
            let name = seg.ident.to_string();
            if CONCATENATION.is_match(&name) {
                let value = CONCATENATION.replace(&name, |captures: &Captures| {
                    let var = captures.get(0).unwrap().as_str();
                    let var = Variable {
                        name: Ident::new(&var, Span::call_site()),
                        original: None,
                    };
                    if let Some(Node::Variable(var)) = mapping.get(&var) {
                        return var.name.to_string();
                    } else {
                        return var.to_string();
                    }
                });
                seg.ident = Ident::new(&value, Span::call_site());
            }
        }
        SizeOf { type_name: path }
    }
}

impl LocalLabel {
    pub fn substitute_labels(
        self: Arc<Self>,
        mapping: &mut HashMap<Arc<LocalLabel>, Arc<LocalLabel>>,
    ) -> Arc<Self> {
        mapping.get(&self).cloned().unwrap_or(self.clone())
    }
}

impl Node {
    pub fn fresh_variables(&self, mapping: &mut HashMap<Variable, Node>) -> Node {
        match self {
            Self::Seq(seq) => {
                let mut new_list = Vec::new();
                for item in seq.iter() {
                    new_list.push(item.fresh_variables(mapping));
                }
                Self::Seq(new_list)
            }
            Self::AddImmediates(add) => Self::AddImmediates(AddImmediates {
                left: Box::new(add.left.fresh_variables(mapping)),
                plus: add.plus,
                right: Box::new(add.right.fresh_variables(mapping)),
            }),
            Self::AndImmediate(and) => Self::AndImmediate(AndImmediate {
                left: Box::new(and.left.fresh_variables(mapping)),
                and: and.and,
                right: Box::new(and.right.fresh_variables(mapping)),
            }),
            Self::OrImmediate(or) => Self::OrImmediate(OrImmediate {
                left: Box::new(or.left.fresh_variables(mapping)),
                or: or.or,
                right: Box::new(or.right.fresh_variables(mapping)),
            }),
            Self::BitNotImmediate(bit_not) => Self::BitNotImmediate(BitNotImmediate {
                value: Box::new(bit_not.value.fresh_variables(mapping)),
                bitnot: bit_not.bitnot,
            }),

            Self::SubImmediates(sub) => Self::SubImmediates(SubImmediates {
                left: Box::new(sub.left.fresh_variables(mapping)),
                minus: sub.minus,
                right: Box::new(sub.right.fresh_variables(mapping)),
            }),

            Self::MulImmediates(mul) => Self::MulImmediates(MulImmediates {
                left: Box::new(mul.left.fresh_variables(mapping)),
                times: mul.times,
                right: Box::new(mul.right.fresh_variables(mapping)),
            }),

            Self::NegImmediate(neg) => Self::NegImmediate(NegImmediate {
                value: Box::new(neg.value.fresh_variables(mapping)),
                minus: neg.minus,
            }),

            Self::LabelReference(label_ref) => Self::LabelReference(LabelReference {
                label: match &label_ref.label {
                    LabelMapping::Global(global) => {
                        LabelMapping::Global(global.substitute(mapping))
                    }
                    LabelMapping::Local(local) => LabelMapping::Local(local.clone()),
                },
                offset: label_ref.offset,
            }),
            Self::LocalLabelReference(label_ref) => Self::LocalLabelReference(label_ref.clone()),

            Self::Label(label) => Self::Label(label.fresh_variables(mapping)),
            Self::SizeOf(size_of) => Self::SizeOf(size_of.fresh_variables(mapping)),
            Self::MacroCall(call) => Self::MacroCall(call.fresh_variables(mapping)),
            Self::Macro(m) => Self::Macro(m.fresh_variables(mapping)),
            Self::StructOffset(offset) => Self::StructOffset(offset.fresh_variables(mapping)),
            Self::AbsoluteAddress(addr) => Self::AbsoluteAddress(AbsoluteAddress {
                base: Box::new(addr.base.fresh_variables(mapping)),
            }),
            Self::Address(addr) => Self::Address(Address {
                base: Box::new(addr.base.fresh_variables(mapping)),
                offset: Box::new(addr.offset.fresh_variables(mapping)),
            }),
            Self::BaseIndex(base_index) => Self::BaseIndex(BaseIndex {
                base: Box::new(base_index.base.fresh_variables(mapping)),
                index: Box::new(base_index.index.fresh_variables(mapping)),
                offset: Box::new(base_index.offset.fresh_variables(mapping)),
                scale: Box::new(base_index.scale.fresh_variables(mapping)),
            }),

            Self::XorImmediate(xor) => Self::XorImmediate(XorImmediate {
                left: Box::new(xor.left.fresh_variables(mapping)),
                xor: xor.xor,
                right: Box::new(xor.right.fresh_variables(mapping)),
            }),

            Self::Instruction(instr) => Self::Instruction(Instruction {
                opcode: instr.opcode.clone(),
                operands: instr
                    .operands
                    .iter()
                    .map(|op| op.fresh_variables(mapping))
                    .collect(),
                documentation: instr.documentation.clone(),
                span: instr.opcode.span(),
            }),
            Self::Variable(var) => Self::Variable(var.fresh_variables(mapping)),
            _ => self.clone(),
        }
    }

    pub fn substitute(&self, mapping: &mut HashMap<Variable, Node>) -> Node {
        match self {
            Self::Seq(seq) => {
                let mut new_list = Vec::new();
                let mut my_constants = mapping.clone();
                for item in seq.iter() {
                    if let Node::ConstDecl(c) = item {
                        let val = c.expr.substitute(&mut my_constants);
                        my_constants.insert(c.variable.clone(), val);
                    } else {
                        new_list.push(item.substitute(&mut my_constants));
                    }
                }
                Self::Seq(new_list)
            }

            Self::Variable(var) => var.substitute(mapping),
            Self::AbsoluteAddress(addr) => Self::AbsoluteAddress(AbsoluteAddress {
                base: Box::new(addr.base.substitute(mapping)),
            }),

            Self::Address(addr) => Self::Address(Address {
                base: Box::new(addr.base.substitute(mapping)),
                offset: Box::new(addr.offset.substitute(mapping)),
            }),
            Self::BaseIndex(base_index) => Self::BaseIndex(BaseIndex {
                base: Box::new(base_index.base.substitute(mapping)),
                index: Box::new(base_index.index.substitute(mapping)),
                offset: Box::new(base_index.offset.substitute(mapping)),
                scale: Box::new(base_index.scale.substitute(mapping)),
            }),
            Self::AndImmediate(and) => Self::AndImmediate(AndImmediate {
                left: Box::new(and.left.substitute(mapping)),
                and: and.and,
                right: Box::new(and.right.substitute(mapping)),
            }),

            Self::BitNotImmediate(bit_not) => Self::BitNotImmediate(BitNotImmediate {
                value: Box::new(bit_not.value.substitute(mapping)),
                bitnot: bit_not.bitnot,
            }),

            Self::XorImmediate(xor) => Self::XorImmediate(XorImmediate {
                left: Box::new(xor.left.substitute(mapping)),
                xor: xor.xor,
                right: Box::new(xor.right.substitute(mapping)),
            }),

            Self::Instruction(instr) => Self::Instruction(Instruction {
                opcode: instr.opcode.clone(),
                operands: instr
                    .operands
                    .iter()
                    .map(|op| op.substitute(mapping))
                    .collect(),
                documentation: instr.documentation.clone(),
                span: instr.opcode.span(),
            }),

            Self::Label(label) => Self::Label(label.substitute(mapping)),
            Self::SizeOf(size_of) => Self::SizeOf(size_of.substitute(mapping)),
            Self::MacroCall(call) => Self::MacroCall(MacroCall {
                args: call.args.iter().map(|op| op.substitute(mapping)).collect(),
                name: call.name.clone(),
                original_name: call.original_name.clone(),
            }),
            Self::Macro(m) => self.clone(),
            Self::MulImmediates(mul) => Self::MulImmediates(MulImmediates {
                left: Box::new(mul.left.substitute(mapping)),
                times: mul.times,
                right: Box::new(mul.right.substitute(mapping)),
            }),

            Self::NegImmediate(neg) => Self::NegImmediate(NegImmediate {
                value: Box::new(neg.value.substitute(mapping)),
                minus: neg.minus,
            }),

            Self::OrImmediate(or) => Self::OrImmediate(OrImmediate {
                left: Box::new(or.left.substitute(mapping)),
                or: or.or,
                right: Box::new(or.right.substitute(mapping)),
            }),

            Self::SubImmediates(sub) => Self::SubImmediates(SubImmediates {
                left: Box::new(sub.left.substitute(mapping)),
                minus: sub.minus,
                right: Box::new(sub.right.substitute(mapping)),
            }),
            Self::LabelReference(label_ref) => Self::LabelReference(LabelReference {
                label: match &label_ref.label {
                    LabelMapping::Global(global) => {
                        LabelMapping::Global(global.substitute(mapping))
                    }
                    LabelMapping::Local(local) => LabelMapping::Local(local.clone()),
                },
                offset: label_ref.offset,
            }),
            Self::StructOffset(offset) => Self::StructOffset(offset.substitute(mapping)),
            _ => self.clone(),
        }
    }

    pub fn rename_labels(&self) -> Node {
        match self {
            Self::Seq(seq) => {
                let mut mapping = HashMap::new();
                for item in seq.iter() {
                    if let Node::LocalLabel(l) = item {
                        mapping.insert(l.clone(), LocalLabel::unique(&l.clean_name()));
                    }
                }
                self.substitute_labels(&mut mapping)
            }

            _ => self.clone(),
        }
    }

    pub fn substitute_labels(
        &self,
        mapping: &mut HashMap<Arc<LocalLabel>, Arc<LocalLabel>>,
    ) -> Node {
        match self {
            Self::LocalLabelReference(l) => {
                if let Some(new) = mapping.get(&l.label) {
                    return Self::LocalLabelReference(LocalLabelReference { label: new.clone() });
                } else {
                    return self.clone();
                }
            }

            Self::LabelReference(label_ref) => Self::LabelReference(LabelReference {
                label: match &label_ref.label {
                    LabelMapping::Global(global) => LabelMapping::Global(global.clone()),
                    LabelMapping::Local(local) => {
                        LabelMapping::Local(mapping.get(local).cloned().unwrap_or(local.clone()))
                    }
                },
                offset: label_ref.offset,
            }),

            Self::Seq(seq) => {
                let mut new_list = Vec::new();
                for item in seq.iter() {
                    new_list.push(item.substitute_labels(mapping));
                }
                Self::Seq(new_list)
            }

            Self::AbsoluteAddress(addr) => Self::AbsoluteAddress(AbsoluteAddress {
                base: Box::new(addr.base.substitute_labels(mapping)),
            }),

            Self::Address(addr) => Self::Address(Address {
                base: Box::new(addr.base.substitute_labels(mapping)),
                offset: Box::new(addr.offset.substitute_labels(mapping)),
            }),

            Self::BaseIndex(base_index) => Self::BaseIndex(BaseIndex {
                base: Box::new(base_index.base.substitute_labels(mapping)),
                index: Box::new(base_index.index.substitute_labels(mapping)),
                offset: Box::new(base_index.offset.substitute_labels(mapping)),
                scale: Box::new(base_index.scale.substitute_labels(mapping)),
            }),

            Self::MulImmediates(mul) => Self::MulImmediates(MulImmediates {
                left: Box::new(mul.left.substitute_labels(mapping)),
                times: mul.times,
                right: Box::new(mul.right.substitute_labels(mapping)),
            }),

            Self::NegImmediate(neg) => Self::NegImmediate(NegImmediate {
                value: Box::new(neg.value.substitute_labels(mapping)),
                minus: neg.minus,
            }),

            Self::OrImmediate(or) => Self::OrImmediate(OrImmediate {
                left: Box::new(or.left.substitute_labels(mapping)),
                or: or.or,
                right: Box::new(or.right.substitute_labels(mapping)),
            }),

            Self::AndImmediate(and) => Self::AndImmediate(AndImmediate {
                left: Box::new(and.left.substitute_labels(mapping)),
                and: and.and,
                right: Box::new(and.right.substitute_labels(mapping)),
            }),

            Self::BitNotImmediate(bit_not) => Self::BitNotImmediate(BitNotImmediate {
                value: Box::new(bit_not.value.substitute_labels(mapping)),
                bitnot: bit_not.bitnot,
            }),

            Self::SubImmediates(sub) => Self::SubImmediates(SubImmediates {
                left: Box::new(sub.left.substitute_labels(mapping)),
                minus: sub.minus,
                right: Box::new(sub.right.substitute_labels(mapping)),
            }),

            Self::Instruction(instr) => Self::Instruction(Instruction {
                opcode: instr.opcode.clone(),
                operands: instr
                    .operands
                    .iter()
                    .map(|op| op.substitute_labels(mapping))
                    .collect(),
                documentation: instr.documentation.clone(),
                span: instr.opcode.span(),
            }),

            Self::MacroCall(call) => Self::MacroCall(MacroCall {
                args: call
                    .args
                    .iter()
                    .map(|op| op.substitute_labels(mapping))
                    .collect(),
                name: call.name.clone(),
                original_name: call.original_name.clone(),
            }),

            Self::LocalLabel(l) => {
                if let Some(new) = mapping.get(l) {
                    return Self::LocalLabel(new.clone());
                } else {
                    return self.clone();
                }
            }
            _ => self.clone(),
        }
    }

    pub fn demacroify(&self, macros: &HashMap<Ident, Macro>, stack: &mut Vec<Node>) -> Node {
        match self {
            Self::AbsoluteAddress(addr) => Self::AbsoluteAddress(AbsoluteAddress {
                base: Box::new(addr.base.demacroify(macros, stack)),
            }),

            Self::AddImmediates(add) => Self::AddImmediates(AddImmediates {
                left: Box::new(add.left.demacroify(macros, stack)),
                plus: add.plus,
                right: Box::new(add.right.demacroify(macros, stack)),
            }),

            Self::Address(addr) => Self::Address(Address {
                base: Box::new(addr.base.demacroify(macros, stack)),
                offset: Box::new(addr.offset.demacroify(macros, stack)),
            }),

            Self::SubImmediates(sub) => Self::SubImmediates(SubImmediates {
                left: Box::new(sub.left.demacroify(macros, stack)),
                minus: sub.minus,
                right: Box::new(sub.right.demacroify(macros, stack)),
            }),

            Self::OrImmediate(or) => Self::OrImmediate(OrImmediate {
                left: Box::new(or.left.demacroify(macros, stack)),
                or: or.or,
                right: Box::new(or.right.demacroify(macros, stack)),
            }),

            Self::Instruction(instr) => Self::Instruction(Instruction {
                opcode: instr.opcode.clone(),
                operands: instr
                    .operands
                    .iter()
                    .map(|op| op.demacroify(macros, stack))
                    .collect(),
                documentation: instr.documentation.clone(),
                span: instr.opcode.span(),
            }),

            Self::Seq(seq) => {
                let mut my_macros = macros.clone();
                seq.iter().for_each(|item| {
                    if let Node::Macro(m) = item {
                        my_macros.insert(m.name.clone(), m.fresh_variables(&mut HashMap::new()));
                    }
                });

                let mut new_list = Vec::new();

                seq.iter().for_each(|item| {
                    if let Node::Macro(m) = item {
                    } else if let Node::MacroCall(call) = item {
                        //stack.push(item.clone());

                        let mut mapping = HashMap::new();
                        let mut my_my_macros = my_macros.clone();
                        let macros = my_macros
                            .get(&call.name)
                            .expect(&format!("Macro {} not found", call.name));
                        if macros.args.len() != call.args.len() {
                            panic!(
                                "Macro {} has {} arguments, but {} were provided",
                                call.name,
                                macros.args.len(),
                                call.args.len()
                            );
                        }

                        for (operand, var) in call.args.iter().zip(macros.args.iter()) {
                            match operand {
                                Node::Variable(name) if my_macros.get(&name.name).is_some() => {
                                    my_my_macros.insert(
                                        var.name.clone(),
                                        my_macros.get(&name.name).unwrap().clone(),
                                    );
                                }
                                Node::Macro(m) => {
                                    my_my_macros.insert(
                                        var.name.clone(),
                                        m.fresh_variables(&mut HashMap::new()),
                                    );
                                    mapping.remove(var);
                                }
                                _ => {
                                    my_my_macros.remove(&var.name);
                                    mapping.insert(var.clone(), operand.clone());
                                }
                            }
                        }

                        let expansion = macros
                            .body
                            .substitute(&mut mapping)
                            .demacroify(&mut my_my_macros, stack)
                            .rename_labels();
                        match expansion {
                            Node::Seq(seq) => {
                                for item in seq.iter() {
                                    new_list.push(item.clone());
                                }
                            }
                            _ => {
                                new_list.push(expansion);
                            }
                        }
                    } else {
                        new_list.push(item.demacroify(&my_macros, stack));
                    }
                });

                Self::Seq(new_list).substitute(&mut HashMap::new())
            }

            _ => self.clone(),
        }
    }

    pub fn fold(&self) -> syn::Result<Node> {
        match self {
            Self::Seq(seq) => {
                let mut new_list = Vec::new();
                for item in seq.iter() {
                    new_list.push(item.fold()?);
                }
                Ok(Self::Seq(new_list))
            }

            Self::NegImmediate(neg) => {
                let value = neg.value.fold()?;
                if let Node::Immediate(imm) = value {
                    Ok(Self::Immediate(Immediate {
                        value: imm.value.wrapping_neg(),
                    }))
                } else {
                    Err(syn::Error::new(
                        Span::call_site(),
                        "invalid immediate value",
                    ))
                }
            }
            Self::AddImmediates(add) => {
                let left = add.left.fold()?;
                let right = add.right.fold()?;
                Ok(Self::AddImmediates(AddImmediates {
                    left: Box::new(left),
                    plus: add.plus,
                    right: Box::new(right),
                }))
            }
            Self::MulImmediates(mul) => {
                let left = mul.left.fold()?;
                let right = mul.right.fold()?;
                Ok(Self::MulImmediates(MulImmediates {
                    left: Box::new(left),
                    times: mul.times,
                    right: Box::new(right),
                }))
            }

            Self::SubImmediates(sub) => {
                let left = sub.left.fold()?;
                let right = sub.right.fold()?;
                Ok(Self::SubImmediates(SubImmediates {
                    left: Box::new(left),
                    minus: sub.minus,
                    right: Box::new(right),
                }))
            }

            Self::OrImmediate(or) => {
                let left = or.left.fold()?;
                let right = or.right.fold()?;
                Ok(Self::OrImmediate(OrImmediate {
                    left: Box::new(left),
                    or: or.or,
                    right: Box::new(right),
                }))
            }

            Self::AndImmediate(and) => {
                let left = and.left.fold()?;
                let right = and.right.fold()?;
                Ok(Self::AndImmediate(AndImmediate {
                    left: Box::new(left),
                    and: and.and,
                    right: Box::new(right),
                }))
            }

            Self::BitNotImmediate(bit_not) => {
                let value = bit_not.value.fold()?;
                Ok(Self::BitNotImmediate(BitNotImmediate {
                    value: Box::new(value),
                    bitnot: bit_not.bitnot,
                }))
            }

            Self::Instruction(instr) => Ok(Self::Instruction(Instruction {
                opcode: instr.opcode.clone(),
                operands: {
                    let mut punc = Punctuated::new();
                    for op in instr.operands.iter() {
                        punc.push(op.fold()?);
                    }
                    punc
                },
                documentation: instr.documentation.clone(),
                span: instr.opcode.span(),
            })),

            Self::Address(addr) => {
                let base = addr.base.fold()?;
                let offset = addr.offset.fold()?;
                Ok(Self::Address(Address {
                    base: Box::new(base),
                    offset: Box::new(offset),
                }))
            }

            Self::BaseIndex(base_index) => {
                let base = base_index.base.fold()?;
                let index = base_index.index.fold()?;
                let offset = base_index.offset.fold()?;
                Ok(Self::BaseIndex(BaseIndex {
                    base: Box::new(base),
                    index: Box::new(index),
                    offset: Box::new(offset),
                    scale: Box::new(base_index.scale.fold()?),
                }))
            }

            Self::AbsoluteAddress(addr) => {
                let base = addr.base.fold()?;
                Ok(Self::AbsoluteAddress(AbsoluteAddress {
                    base: Box::new(base),
                }))
            }

            Self::ConstDecl(decl) => Ok(Self::ConstDecl(ConstDecl {
                variable: decl.variable.clone(),
                eq: decl.eq,
                expr: Box::new(decl.expr.fold()?),
                span: decl.span,
                documentation: decl.documentation.clone(),
            })),

            _ => Ok(self.clone()),
        }
    }

    pub fn directives(&self) -> (Node, Vec<Ident>) {
        match self {
            Self::Seq(seq) => {
                let mut directives = Vec::new();
                let mut new_list = Vec::new();
                for item in seq.iter() {
                    if let Node::Directive(directive) = item {
                        directives.push(directive.clone());
                    } else {
                        new_list.push(item.clone());
                    }
                }
                (Node::Seq(new_list), directives)
            }

            _ => unreachable!(),
        }
    }
}
