use proc_macro2::Span;
use std::{borrow::Cow, fmt::Display, hash::Hash, rc::Rc};
use syn::Ident;

use crate::stmt::{LabelMapping, LocalLabel};

pub struct StructOffset {
    pub span: Span,
}

#[derive(Clone)]
pub struct Variable {
    pub name: Ident,
    pub original: Option<Ident>,
}

impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Eq for Variable {}

impl Hash for Variable {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl Variable {
    pub fn new(ident: Ident) -> Self {
        Self {
            name: ident,
            original: None,
        }
    }

    pub fn span(&self) -> Span {
        self.original.as_ref().unwrap_or(&self.name).span()
    }
}

impl Into<Ident> for Variable {
    fn into(self) -> Ident {
        self.name
    }
}

impl From<Ident> for Variable {
    fn from(ident: Ident) -> Self {
        Self {
            name: ident,
            original: None,
        }
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// [< $var1 _id ...>]
#[derive(Clone)]
pub struct Concatenation {
    pub span: Span,
    pub elements: Vec<ConcatenationElement>,
}

impl PartialEq for ConcatenationElement {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ConcatenationElement::Variable(v1), ConcatenationElement::Variable(v2)) => v1 == v2,
            (ConcatenationElement::Ident(i1), ConcatenationElement::Ident(i2)) => i1 == i2,
            _ => false,
        }
    }
}

impl Eq for ConcatenationElement {}

impl Hash for ConcatenationElement {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            ConcatenationElement::Variable(v) => v.hash(state),
            ConcatenationElement::Ident(i) => i.hash(state),
        }
    }
}

impl PartialEq for Concatenation {
    fn eq(&self, other: &Self) -> bool {
        self.elements == other.elements
    }
}

impl Eq for Concatenation {}

impl Hash for Concatenation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.elements.hash(state);
    }
}

impl Display for Concatenation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[< {} >]",
            self.elements
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        )
    }
}

#[derive(Clone)]
pub enum ConcatenationElement {
    Variable(Variable),
    Ident(Ident),
}

impl Display for ConcatenationElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConcatenationElement::Variable(v) => write!(f, "@{}", v),
            ConcatenationElement::Ident(i) => write!(f, "{}", i),
        }
    }
}

#[derive(Clone)]
pub struct GPRegister(pub Ident);

impl Display for GPRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl GPRegister {
    pub fn new(ident: Ident) -> Self {
        Self(ident)
    }

    pub fn span(&self) -> Span {
        self.0.span()
    }
}

#[derive(Clone)]
pub struct FPRegister(pub Ident);

impl Display for FPRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FPRegister {
    pub fn new(ident: Ident) -> Self {
        Self(ident)
    }

    pub fn span(&self) -> Span {
        self.0.span()
    }
}

#[derive(Clone)]
pub struct VecRegister(pub Ident);

impl Display for VecRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl VecRegister {
    pub fn new(ident: Ident) -> Self {
        Self(ident)
    }

    pub fn span(&self) -> Span {
        self.0.span()
    }
}

#[derive(Clone)]
pub struct Constant {
    pub span: Span,
    pub value: ConstantValue,
}

impl From<i32> for Constant {
    fn from(value: i32) -> Self {
        Self {
            span: Span::call_site(),
            value: ConstantValue::Immediate(value as i64),
        }
    }
}

impl From<i64> for Constant {
    fn from(value: i64) -> Self {
        Self {
            span: Span::call_site(),
            value: ConstantValue::Immediate(value),
        }
    }
}

impl From<u64> for Constant {
    fn from(value: u64) -> Self {
        Self {
            span: Span::call_site(),
            value: ConstantValue::Immediate(value as i64),
        }
    }
}

impl From<isize> for Constant {
    fn from(value: isize) -> Self {
        Self {
            span: Span::call_site(),
            value: ConstantValue::Immediate(value as i64),
        }
    }
}

impl From<usize> for Constant {
    fn from(value: usize) -> Self {
        Self {
            span: Span::call_site(),
            value: ConstantValue::Immediate(value as i64),
        }
    }
}


impl Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Clone)]
pub enum ConstantValue {
    Immediate(i64),
    Bytes(Cow<'static, [u8]>),
    String(Cow<'static, str>),
    Boolean(bool),
    /// Rust expression as a constant value.
    Expression(syn::Expr),

    /// A global_asm reference, this can be used to
    /// referencce `Expression` constant value or global labels
    /// that are not defined in the current asm.
    ///
    /// This is produced by the transformation passes of offlineasm, users can't create it.
    Reference(usize),
}

impl PartialEq for ConstantValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ConstantValue::Immediate(i1), ConstantValue::Immediate(i2)) => i1 == i2,
            (ConstantValue::Bytes(b1), ConstantValue::Bytes(b2)) => b1 == b2,
            (ConstantValue::String(s1), ConstantValue::String(s2)) => s1 == s2,
            (ConstantValue::Boolean(b1), ConstantValue::Boolean(b2)) => b1 == b2,
            _ => false,
        }
    }
}

impl Eq for ConstantValue {}

impl Display for ConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantValue::Immediate(i) => write!(f, "{}", i),
            ConstantValue::Bytes(b) => write!(f, "{:?}", b),
            ConstantValue::String(s) => write!(f, "{:?}", s),
            ConstantValue::Boolean(b) => write!(f, "{}", b),
            ConstantValue::Expression(_) => write!(f, "constexpr"),
            ConstantValue::Reference(r) => write!(f, "{{ _ref_{} }}", r),
        }
    }
}

#[derive(Clone)]
pub struct BinaryExpression {
    pub span: Span,
    pub lhs: Operand,
    pub rhs: Operand,
    pub op: BinaryOperator,
}

impl Display for BinaryExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.lhs, self.op, self.rhs)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
    Xor,
    Shl,
    Shr,
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Sub => write!(f, "-"),
            BinaryOperator::Mul => write!(f, "*"),
            BinaryOperator::Div => write!(f, "/"),
            BinaryOperator::And => write!(f, "&"),
            BinaryOperator::Or => write!(f, "|"),
            BinaryOperator::Xor => write!(f, "^"),
            BinaryOperator::Shl => write!(f, "<<"),
            BinaryOperator::Shr => write!(f, ">>"),
        }
    }
}

#[derive(Clone)]
pub struct UnaryExpression {
    pub span: Span,
    pub op: UnaryOperator,
    pub operand: Operand,
}

impl Display for UnaryExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.op, self.operand)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum UnaryOperator {
    Neg,
    Not,
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperator::Neg => write!(f, "-"),
            UnaryOperator::Not => write!(f, "!"),
        }
    }
}

#[derive(Clone)]
pub struct Address {
    pub span: Span,
    pub kind: AddressKind,
}

impl Display for Address {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

#[derive(Clone)]
pub enum AddressKind {
    Absolute {
        value: Operand,
    },
    Base {
        base: Operand,
        offset: Operand,
    },
    BaseIndex {
        base: Operand,
        index: Operand,
        /// Scale is 1, 2, 4, 8 or 16.
        ///
        /// Must be resolved to immediate constant.
        scale: Operand,
        /// Offset is isize.
        ///
        /// Must be resolved to immediate constant.
        offset: Operand,
    },
}

impl PartialEq for AddressKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (AddressKind::Absolute { value: v1 }, AddressKind::Absolute { value: v2 }) => v1 == v2,
            (
                AddressKind::Base {
                    base: b1,
                    offset: o1,
                },
                AddressKind::Base {
                    base: b2,
                    offset: o2,
                },
            ) => b1 == b2 && o1 == o2,
            (
                AddressKind::BaseIndex {
                    base: b1,
                    index: i1,
                    scale: s1,
                    offset: o1,
                },
                AddressKind::BaseIndex {
                    base: b2,
                    index: i2,
                    scale: s2,
                    offset: o2,
                },
            ) => b1 == b2 && i1 == i2 && s1 == s2 && o1 == o2,
            _ => false,
        }
    }
}

impl Display for AddressKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AddressKind::Absolute { value } => write!(f, "[abs {}]", value),
            AddressKind::Base { base, offset } => write!(f, "[{base}, {offset}]"),
            AddressKind::BaseIndex {
                base,
                index,
                scale,
                offset,
            } => write!(f, "[{base}+{index}*{scale}+{offset}]"),
        }
    }
}

#[derive(Clone)]
pub struct LabelReference {
    pub span: Span,
    pub label: LabelMapping,
}

impl LabelReference {
    pub fn new(label: LabelMapping) -> Self {
        Self {
            span: Span::call_site(),
            label,
        }
    }

    pub fn with_span(self, span: Span) -> Self {
        Self { span, ..self }
    }

    pub fn name(&self) -> &Ident {
        match &self.label {
            LabelMapping::Local(local) => &local.name,
            LabelMapping::Global(global) => &global.name,
        }
    }

    pub fn is_extern(&self) -> bool {
        match &self.label {
            LabelMapping::Local(_) => false,
            LabelMapping::Global(global) => global.external.get(),
        }
    }

    pub fn is_global(&self) -> bool {
        match &self.label {
            LabelMapping::Local(_) => false,
            LabelMapping::Global(_) => true,
        }
    }

    pub fn is_local(&self) -> bool {
        match &self.label {
            LabelMapping::Local(_) => true,
            LabelMapping::Global(_) => false,
        }
    }
}

impl Display for LabelReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.label {
            LabelMapping::Global(global) => write!(f, "&{}", global.name),
            LabelMapping::Local(local) => write!(f, "=>{}", local.name),
        }
    }
}

#[derive(Clone)]
pub struct LocalLabelReference {
    pub span: Span,
    pub name: Rc<LocalLabel>,
}

impl LocalLabelReference {
    pub fn new(name: Rc<LocalLabel>) -> Self {
        Self {
            span: Span::call_site(),
            name,
        }
    }
}

impl Display for LocalLabelReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "=>{}", self.name.name)
    }
}

#[derive(Clone)]
pub enum Name {
    Variable(Variable),
    Concatenation(Concatenation),
}

impl PartialEq for Name {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Name::Variable(v1), Name::Variable(v2)) => v1 == v2,
            (Name::Concatenation(c1), Name::Concatenation(c2)) => c1 == c2,
            _ => false,
        }
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Name::Variable(v) => write!(f, "{}", v),
            Name::Concatenation(c) => write!(f, "{}", c),
        }
    }
}

#[derive(Clone)]
pub struct SpecialRegister {
    pub name: Ident,
}

impl Display for SpecialRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Clone)]
pub enum Operand {
    Name(Name),
    GPRegister(GPRegister),
    FPRegister(FPRegister),
    VecRegister(VecRegister),
    SpecialRegister(SpecialRegister),

    Constant(Constant),
    Address(Rc<Address>),
    BinaryExpression(Rc<BinaryExpression>),
    UnaryExpression(Rc<UnaryExpression>),
    LabelReference(Rc<LabelReference>),
    LocalLabelReference(Rc<LocalLabelReference>),
}

impl PartialEq for Operand {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Operand::Name(n1), Operand::Name(n2)) => n1 == n2,
            (Operand::GPRegister(r1), Operand::GPRegister(r2)) => r1.0 == r2.0,
            (Operand::FPRegister(r1), Operand::FPRegister(r2)) => r1.0 == r2.0,
            (Operand::VecRegister(r1), Operand::VecRegister(r2)) => r1.0 == r2.0,
            (Operand::SpecialRegister(r1), Operand::SpecialRegister(r2)) => r1.name == r2.name,
            (Operand::Constant(c1), Operand::Constant(c2)) => c1.value == c2.value,
            (Operand::Address(a1), Operand::Address(a2)) => a1.kind == a2.kind,
            _ => false,
        }
    }
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::Name(name) => write!(f, "{}", name),
            Operand::GPRegister(reg) => write!(f, "{}", reg),
            Operand::FPRegister(reg) => write!(f, "{}", reg),
            Operand::VecRegister(reg) => write!(f, "{}", reg),
            Operand::SpecialRegister(reg) => write!(f, "{}", reg),
            Operand::Address(addr) => write!(f, "{}", addr),
            Operand::Constant(c) => write!(f, "{}", c),
            Operand::BinaryExpression(e) => write!(f, "{}", e),
            Operand::UnaryExpression(e) => write!(f, "{}", e),
            Operand::LabelReference(l) => write!(f, "{}", l),
            Operand::LocalLabelReference(l) => write!(f, "{}", l),
        }
    }
}

impl From<isize> for Operand {
    fn from(value: isize) -> Self {
        Operand::Constant(Constant::from(value))
    }
}


impl From<i64> for Operand {
    fn from(value: i64) -> Self {
        Operand::Constant(Constant::from(value))
    }
}

impl From<usize> for Operand {
    fn from(value: usize) -> Self {
        Operand::Constant(Constant::from(value))
    }
}

impl From<Variable> for Operand {
    fn from(value: Variable) -> Self {
        Operand::Name(Name::Variable(value))
    }
}

impl From<LabelReference> for Operand {
    fn from(value: LabelReference) -> Self {
        Operand::LabelReference(Rc::new(value))
    }
}

impl From<LocalLabelReference> for Operand {
    fn from(value: LocalLabelReference) -> Self {
        Operand::LocalLabelReference(Rc::new(value))
    }
}

impl From<GPRegister> for Operand {
    fn from(value: GPRegister) -> Self {
        Operand::GPRegister(value)
    }
}

impl From<FPRegister> for Operand {
    fn from(value: FPRegister) -> Self {
        Operand::FPRegister(value)
    }
}

impl From<VecRegister> for Operand {
    fn from(value: VecRegister) -> Self {
        Operand::VecRegister(value)
    }
}

impl From<Constant> for Operand {
    fn from(value: Constant) -> Self {
        Operand::Constant(value)
    }
}

impl From<BinaryExpression> for Operand {
    fn from(value: BinaryExpression) -> Self {
        Operand::BinaryExpression(Rc::new(value))
    }
}

impl From<UnaryExpression> for Operand {
    fn from(value: UnaryExpression) -> Self {
        Operand::UnaryExpression(Rc::new(value))
    }
}

impl From<Concatenation> for Operand {
    fn from(value: Concatenation) -> Self {
        Operand::Name(Name::Concatenation(value))
    }
}

impl From<Name> for Operand {
    fn from(value: Name) -> Self {
        Operand::Name(value)
    }
}

impl From<Address> for Operand {
    fn from(value: Address) -> Self {
        Operand::Address(Rc::new(value))
    }
}

impl Name {
    pub fn span(&self) -> Span {
        match self {
            Name::Variable(v) => v.span(),
            Name::Concatenation(c) => c.span,
        }
    }
}

impl Operand {
    pub fn span(&self) -> Span {
        match self {
            Operand::Name(name) => name.span(),
            Operand::GPRegister(reg) => reg.span(),
            Operand::FPRegister(reg) => reg.span(),
            Operand::VecRegister(reg) => reg.span(),
            Operand::SpecialRegister(reg) => reg.name.span(),
            Operand::Address(addr) => addr.span,
            Operand::Constant(c) => c.span,
            Operand::BinaryExpression(e) => e.span,
            Operand::UnaryExpression(e) => e.span,
            Operand::LabelReference(l) => l.span,
            Operand::LocalLabelReference(l) => l.span,
        }
    }
}
