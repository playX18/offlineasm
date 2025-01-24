#![allow(dead_code)]
use proc_macro2::Span;
use syn::Abi;
use syn::ForeignItemFn;
use std::cell::Cell;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::hash::Hasher;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;
use syn::punctuated::Punctuated;
use syn::Signature;
use syn::{Ident, LitStr, Path, Token};

use crate::x86::SpecialRegister;

/// StructOffset is a struct that represents the offset of a field in a struct.
///
/// `A::field` or `A::<Isolate>::field`.
#[derive(Clone)]
pub struct StructOffset {
    pub path: Path,
}

impl Display for StructOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, segment) in self.path.segments.iter().enumerate() {
            write!(f, "{}", segment.ident)?;
            if i < self.path.segments.len() - 1 {
                write!(f, "::")?;
            }
        }
        Ok(())
    }
}

/// SizeOf is a struct that represents the size of a type.
///
/// `size_of A::B`
#[derive(Clone)]
pub struct SizeOf {
    pub type_name: Path,
}

impl Display for SizeOf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "sizeof ")?;

        for (i, segment) in self.type_name.segments.iter().enumerate() {
            write!(f, "{}", segment.ident)?;
            if i < self.type_name.segments.len() - 1 {
                write!(f, "::")?;
            }
        }

        Ok(())
    }
}

#[derive(Clone)]
pub struct Immediate {
    pub value: isize,
}

impl Display for Immediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct AddImmediates {
    pub left: Box<Node>,
    pub plus: Token![+],
    pub right: Box<Node>,
}

impl Display for AddImmediates {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} + {}", self.left, self.right)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct SubImmediates {
    pub left: Box<Node>,
    pub minus: Token![-],
    pub right: Box<Node>,
}

impl Display for SubImmediates {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} - {}", self.left, self.right)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct MulImmediates {
    pub left: Box<Node>,
    pub times: Token![*],
    pub right: Box<Node>,
}

impl Display for MulImmediates {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} * {}", self.left, self.right)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct NegImmediate {
    pub minus: Token![-],
    pub value: Box<Node>,
}

impl Display for NegImmediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "-{}", self.value)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct OrImmediate {
    pub left: Box<Node>,
    pub or: Token![|],
    pub right: Box<Node>,
}

impl Display for OrImmediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} | {}", self.left, self.right)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct AndImmediate {
    pub left: Box<Node>,
    pub and: Token![&],
    pub right: Box<Node>,
}

impl Display for AndImmediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} & {}", self.left, self.right)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct XorImmediate {
    pub left: Box<Node>,
    pub xor: Token![^],
    pub right: Box<Node>,
}

impl Display for XorImmediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ^ {}", self.left, self.right)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct BitNotImmediate {
    pub bitnot: Token![~],
    pub value: Box<Node>,
}

impl Display for BitNotImmediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "~{}", self.value)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct StringLiteral {
    pub string: LitStr,
}

impl Display for StringLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.string.value())?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct RegisterId {
    pub name: Ident,
}

impl Display for RegisterId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        Ok(())
    }
}

impl RegisterId {
    pub fn new(name: Ident) -> Self {
        Self { name }
    }

    pub fn for_name(name: &Ident) -> RegisterId {
        RegisterId { name: name.clone() }
    }

    pub fn for_name_str(name: &str) -> RegisterId {
        RegisterId {
            name: Ident::new(name, Span::call_site()),
        }
    }

    pub fn for_name_str_at(name: &str, span: Span) -> RegisterId {
        RegisterId {
            name: Ident::new(name, span),
        }
    }
}

impl Display for FPRegisterId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct FPRegisterId {
    pub name: Ident,
}

impl FPRegisterId {
    pub fn new(name: Ident) -> Self {
        Self { name }
    }

    pub fn for_name(name: &Ident) -> FPRegisterId {
        FPRegisterId { name: name.clone() }
    }
}

impl Display for VecRegisterId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct VecRegisterId {
    pub name: Ident,
}

impl VecRegisterId {
    pub fn new(name: Ident) -> Self {
        Self { name }
    }

    pub fn for_name(name: &Ident) -> VecRegisterId {
        VecRegisterId { name: name.clone() }
    }
}

#[derive(Clone)]
pub struct Address {
    pub offset: Box<Node>,
    pub bracket_token: syn::token::Bracket,
    pub base: Box<Node>,
}

impl Display for Address {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}]", self.offset, self.base)?;
        Ok(())
    }
}

#[derive(Clone)]
/// offset[base, index, scale]
pub struct BaseIndex {
    pub offset: Box<Node>,
    pub bracket_token: syn::token::Bracket,
    pub base: Box<Node>,
    pub comma1: Token![,],
    pub index: Box<Node>,
    pub comma2: Option<Token![,]>,
    pub scale: Box<Node>,
}

impl Display for BaseIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}[{}, {}, {}]",
            self.offset, self.base, self.index, self.scale
        )?;
        Ok(())
    }
}

#[derive(Clone)]
/// [base]
pub struct AbsoluteAddress {
    pub bracket_token: syn::token::Bracket,
    pub base: Box<Node>,
}

impl Display for AbsoluteAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.base)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct Instruction {
    pub span: Span,
    pub documentation: Option<Vec<String>>,
    pub opcode: Ident,
    pub operands: Punctuated<Node, Token![,]>,
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.opcode)?;
        for operand in &self.operands {
            write!(f, ", {}", operand)?;
        }
        Ok(())
    }
}

impl Instruction {
    pub fn new(opcode: Ident, operands: Punctuated<Node, Token![,]>) -> Self {
        Self {
            span: opcode.span(),
            opcode,
            operands,
            documentation: None,
        }
    }

    pub fn new2(
        opcode: Ident,
        operands: Punctuated<Node, Token![,]>,
        documentation: Option<Vec<String>>,
    ) -> Self {
        Self {
            span: opcode.span(),
            opcode,
            operands,
            documentation,
        }
    }
}

#[derive(Clone)]
pub struct Const {
    pub expr: syn::Expr,
}

impl Display for Const {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "constexpr")?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct ConstDecl {
    pub span: Span,
    pub documentation: Option<Vec<String>>,
    pub variable: Variable,
    pub eq: Token![=],
    pub expr: Box<Node>,
}

impl Display for ConstDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "const {} = {}", self.variable, self.expr)?;
        Ok(())
    }
}

#[derive(Clone)]
pub enum LabelMapping {
    Local(Arc<LocalLabel>),
    Global(Arc<Label>),
}

impl PartialEq for LabelMapping {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (LabelMapping::Local(x), LabelMapping::Local(y)) => x.name == y.name,
            (LabelMapping::Global(x), LabelMapping::Global(y)) => x.name() == y.name(),
            _ => false,
        }
    }
}

impl Eq for LabelMapping {}

impl LabelMapping {
    pub fn name(&self) -> &Ident {
        match self {
            LabelMapping::Local(local) => &local.name,
            LabelMapping::Global(global) => &global.name(),
        }
    }

    pub fn unwrap_local(&self) -> Arc<LocalLabel> {
        match self {
            LabelMapping::Local(local) => local.clone(),
            LabelMapping::Global(_) => panic!("Expected local label"),
        }
    }

    pub fn unwrap_global(&self) -> Arc<Label> {
        match self {
            LabelMapping::Local(_) => panic!("Expected global label"),
            LabelMapping::Global(global) => global.clone(),
        }
    }
}

pub struct Label {
    name: Ident,
    pub extern_: AtomicBool,
    pub global: AtomicBool,
    pub aligned: AtomicBool,
    pub aligned_to: AtomicUsize,
    pub export: AtomicBool,
    pub defined_in_macro: bool,
    pub sym_id: Cell<Option<usize>>,
    pub doc: Cell<Option<Vec<String>>>,
    pub doc_span: Cell<Option<Span>>,
}

impl Label {
    pub fn name(&self) -> &Ident {
        &self.name
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:", self.name())?;
        Ok(())
    }
}

struct LabelMappings {
    mappings: HashMap<Ident, LabelMapping>,
}

impl LabelMappings {
    fn get(&self, name: &Ident) -> Option<LabelMapping> {
        self.mappings.get(name).cloned()
    }

    fn insert(&mut self, name: Ident, label: LabelMapping) {
        self.mappings.insert(name, label);
    }

    fn intern_local(&mut self, name: &Ident) -> Arc<LocalLabel> {
        if let Some(label) = self.mappings.get(name) {
            return label.unwrap_local();
        }

        let label = Arc::new(LocalLabel::new(name.clone()));
        self.mappings
            .insert(name.clone(), LabelMapping::Local(label.clone()));
        label
    }

    fn intern_global(&mut self, name: &Ident, defined_in_macro: bool) -> Arc<Label> {
        if let Some(label) = self.mappings.get(name) {
            return label.unwrap_global();
        }

        let label = Arc::new(Label::new(name.clone(), defined_in_macro));
        if defined_in_macro {
            label
                .extern_
                .store(false, std::sync::atomic::Ordering::Relaxed);
        }
        self.mappings
            .insert(name.clone(), LabelMapping::Global(label.clone()));
        label
    }

    fn new() -> Self {
        Self {
            mappings: HashMap::new(),
        }
    }
}

unsafe impl Send for LabelMappings {}
unsafe impl Sync for LabelMappings {}
thread_local! {
    static LABEL_MAPPINGS: std::cell::RefCell<LabelMappings> = std::cell::RefCell::new(LabelMappings::new());
}

impl Label {
    pub fn new(name: Ident, defined_in_macro: bool) -> Self {
        Self {
            name,
            defined_in_macro,
            extern_: AtomicBool::new(!defined_in_macro),
            global: AtomicBool::new(false),
            aligned: AtomicBool::new(false),
            aligned_to: AtomicUsize::new(0),
            export: AtomicBool::new(false),
            sym_id: Cell::new(None),
            doc: Cell::new(None),
            doc_span: Cell::new(None),
        }
    }

    pub fn set_doc(&self, doc: Option<Vec<String>>) {
        self.doc.set(doc);
    }

    pub fn set_sym_id(&self, id: usize) {
        self.sym_id.set(Some(id));
    }

    pub fn get_sym_id(&self) -> Option<usize> {
        self.sym_id.get()
    }

    pub fn for_name(name: &Ident, defined_in_macro: bool) -> Arc<Label> {
        LABEL_MAPPINGS.with(|mappings| mappings.borrow_mut().intern_global(name, defined_in_macro))
    }
    pub fn set_as_global(name: &Ident) {
        let label = Self::for_name(name, false);
        label.set_global();
    }

    pub fn set_as_global_export(name: &Ident) {
        let label = Self::for_name(name, false);
        label.set_global();
        label.set_exported();
    }

    pub fn set_as_unaligned_global(name: &Ident) {
        let label = Self::for_name(name, false);
        label.set_global();
        label.set_aligned(false);
    }

    pub fn set_as_aligned(name: &Ident, to: usize) {
        let label = Self::for_name(name, false);
        label.set_aligned(true);
        label.set_aligned_to(to);
    }

    pub fn set_as_unaligned_global_export(name: &Ident) {
        let label = Self::for_name(name, false);
        label.set_global();
        label.set_aligned(false);
        label.set_exported();
    }

    pub fn is_global(&self) -> bool {
        self.global.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn is_extern(&self) -> bool {
        self.extern_.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn is_aligned(&self) -> bool {
        self.aligned.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn is_exported(&self) -> bool {
        self.export.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn aligned_to(&self) -> usize {
        self.aligned_to.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn set_global(&self) {
        self.global
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }

    pub fn set_extern(&self) {
        self.extern_
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }

    pub fn set_aligned(&self, val: bool) {
        self.aligned
            .store(val, std::sync::atomic::Ordering::Relaxed);
    }

    pub fn set_aligned_to(&self, to: usize) {
        self.aligned_to
            .store(to, std::sync::atomic::Ordering::Relaxed);
    }

    pub fn set_exported(&self) {
        self.export
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }
}

#[derive(Hash, PartialEq, Eq, Clone)]
pub struct LocalLabel {
    pub name: Ident,
}

impl Display for LocalLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:", self.name)?;
        Ok(())
    }
}

static UNIQUE_NAME_COUNTER: AtomicUsize = AtomicUsize::new(0);

impl LocalLabel {
    pub fn new(name: Ident) -> Self {
        Self { name }
    }

    pub fn for_name(name: &Ident) -> Arc<Self> {
        LABEL_MAPPINGS.with(|mappings| {
            let mut mappings = mappings.borrow_mut();
            let label = mappings.get(name);

            if let Some(LabelMapping::Global(global)) = label.as_ref() {
                panic!("label name collision: {}", global.name());
            } else if label.is_none() {
                let label = Arc::new(LocalLabel::new(name.clone()));
                mappings.insert(name.clone(), LabelMapping::Local(label.clone()));
                return label;
            }

            label.unwrap().unwrap_local()
        })
    }

    pub fn unique(comment: &str) -> Arc<Self> {
        let mut new_name = format!("_{comment}");
        LABEL_MAPPINGS.with(|mappings| {
            let mappings = mappings.borrow();
            if mappings
                .get(&Ident::new(&new_name, Span::call_site()))
                .is_some()
            {
                loop {
                    new_name = format!(
                        "_{comment}_{}",
                        UNIQUE_NAME_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                    );

                    if mappings
                        .get(&Ident::new(&new_name, Span::call_site()))
                        .is_none()
                    {
                        break;
                    }
                }
            }
        });

        Self::for_name(&Ident::new(&new_name, Span::call_site()))
    }
}

#[derive(Clone)]
pub struct LabelReference {
    pub label: LabelMapping,
    pub offset: isize,
}

impl Display for LabelReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.label {
            LabelMapping::Local(local) => write!(f, "{}", local.name)?,
            LabelMapping::Global(global) => write!(f, "{}", global.name())?,
        }
        Ok(())
    }
}

impl LabelReference {
    pub fn new(label: LabelMapping, offset: isize) -> Self {
        Self { label, offset }
    }

    pub fn plus_offset(&self, offset: isize) -> Self {
        Self {
            label: self.label.clone(),
            offset: self.offset + offset,
        }
    }

    pub fn name(&self) -> &Ident {
        match &self.label {
            LabelMapping::Local(local) => &local.name,
            LabelMapping::Global(global) => &global.name(),
        }
    }

    pub fn is_extern(&self) -> bool {
        match &self.label {
            LabelMapping::Local(_) => false,
            LabelMapping::Global(global) => global.is_extern(),
        }
    }
}

#[derive(Clone)]
pub struct LocalLabelReference {
    pub label: Arc<LocalLabel>,
}

impl Display for LocalLabelReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.label.name)?;
        Ok(())
    }
}

impl LocalLabelReference {
    pub fn new(label: Arc<LocalLabel>) -> Self {
        Self { label }
    }

    pub fn name(&self) -> &Ident {
        &self.label.name
    }
}

#[derive(Clone)]
pub struct Macro {
    pub name: Ident,
    pub args: Punctuated<Variable, Token![,]>,
    pub body: Box<Node>,
}

impl Display for Macro {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "macro {}({})\n{}\nend",
            self.name,
            self.args
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(","),
            self.body
        )?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct MacroCall {
    pub name: Ident,
    pub original_name: Option<Ident>,
    pub args: Punctuated<Node, Token![,]>,
}

impl MacroCall {
    pub fn new(
        name: Ident,
        original_name: Option<Ident>,
        args: Punctuated<Node, Token![,]>,
    ) -> Self {
        Self {
            name,
            original_name,
            args,
        }
    }

    pub fn original_name(&self) -> Ident {
        self.original_name.as_ref().unwrap_or(&self.name).clone()
    }
}

impl Display for MacroCall {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}({})",
            self.name,
            self.args
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(",")
        )?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct IfThenElse {
    pub predicate: Box<Node>,
    pub then: Box<Node>,
    pub else_case: Option<Box<Node>>,
}

#[derive(Clone)]
pub struct Variable {
    pub name: Ident,
    pub original: Option<Ident>,
}

impl Variable {
    pub fn original(&self) -> Ident {
        self.original.as_ref().unwrap_or(&self.name).clone()
    }
}

impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Eq for Variable {}

impl Hash for Variable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        Ok(())
    }
}

#[derive(Clone)]
pub struct Export {
    pub label: Arc<Label>,
    pub item: ForeignItemFn,
    pub abi: Abi,
}

impl Display for Export {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "export {}", self.label.name())?;
        Ok(())
    }
}

#[derive(Clone)]
pub enum Node {
    Export(Export),
    IfThenElse(IfThenElse),
    Macro(Macro),
    MacroCall(MacroCall),
    StructOffset(StructOffset),
    SizeOf(SizeOf),
    Immediate(Immediate),
    AddImmediates(AddImmediates),
    SubImmediates(SubImmediates),
    MulImmediates(MulImmediates),
    NegImmediate(NegImmediate),
    OrImmediate(OrImmediate),
    AndImmediate(AndImmediate),
    XorImmediate(XorImmediate),
    BitNotImmediate(BitNotImmediate),
    StringLiteral(StringLiteral),
    RegisterId(RegisterId),
    FPRegisterId(FPRegisterId),
    VecRegisterId(VecRegisterId),
    Address(Address),
    BaseIndex(BaseIndex),
    AbsoluteAddress(AbsoluteAddress),
    Instruction(Instruction),
    Const(Const),
    ConstDecl(ConstDecl),
    Variable(Variable),
    Setting(Ident),
    LabelReference(LabelReference),
    LocalLabelReference(LocalLabelReference),
    Label(Arc<Label>),
    LocalLabel(Arc<LocalLabel>),
    Seq(Punctuated<Node, Token![;]>),
    True,
    False,
    And(Box<Node>, Box<Node>),
    Or(Box<Node>, Box<Node>),
    Not(Box<Node>),
    SpecialRegister(SpecialRegister),
    AsmOperand(usize),
}

impl std::fmt::Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AsmOperand(x) => write!(f, "{{_{}}}", x)?,
            Self::SpecialRegister(x) => {
                write!(f, "{}", x.x86_operand(crate::x86::OperandKind::Ptr))?
            }
            Self::Export(x) => write!(f, "{}", x)?,
            Self::IfThenElse(if_then_else) => {
                write!(f, "if {} {{\n", if_then_else.predicate)?;
                write!(f, "{}", if_then_else.then)?;
                if let Some(else_case) = &if_then_else.else_case {
                    write!(f, "\n}} else {{\n{}", else_case)?;
                }
                write!(f, "\n}}")?;
            }
            Self::Setting(x) => write!(f, "{}", x)?,
            Self::Seq(seq) => {
                for (i, node) in seq.iter().enumerate() {
                    match node {
                        Node::Instruction(ins) => {
                            write!(f, "\t{}{}", ins, if i == seq.len() - 1 { "" } else { "\n" })?;
                        }

                        _ => write!(f, "{}{}", node, if i == seq.len() - 1 { "" } else { "\n" })?,
                    }
                }
            }
            Self::Macro(x) => write!(f, "{}", x)?,
            Self::MacroCall(x) => write!(f, "{}", x)?,
            Self::StructOffset(x) => write!(f, "{}", x)?,
            Self::SizeOf(x) => write!(f, "{}", x)?,
            Self::Immediate(x) => write!(f, "{}", x)?,
            Self::AddImmediates(x) => write!(f, "{}", x)?,
            Self::SubImmediates(x) => write!(f, "{}", x)?,
            Self::MulImmediates(x) => write!(f, "{}", x)?,
            Self::NegImmediate(x) => write!(f, "{}", x)?,
            Self::OrImmediate(x) => write!(f, "{}", x)?,
            Self::AndImmediate(x) => write!(f, "{}", x)?,
            Self::XorImmediate(x) => write!(f, "{}", x)?,
            Self::BitNotImmediate(x) => write!(f, "{}", x)?,
            Self::StringLiteral(x) => write!(f, "{}", x)?,
            Self::RegisterId(x) => write!(f, "{}", x)?,
            Self::FPRegisterId(x) => write!(f, "{}", x)?,
            Self::VecRegisterId(x) => write!(f, "{}", x)?,
            Self::Address(x) => write!(f, "{}", x)?,
            Self::BaseIndex(x) => write!(f, "{}", x)?,
            Self::AbsoluteAddress(x) => write!(f, "{}", x)?,
            Self::Instruction(x) => write!(f, "{}", x)?,
            Self::Const(x) => write!(f, "{}", x)?,
            Self::ConstDecl(x) => write!(f, "{}", x)?,
            Self::Variable(x) => write!(f, "{}", x)?,
            Self::LabelReference(x) => write!(f, "{}", x)?,
            Self::LocalLabelReference(x) => write!(f, "{}", x)?,
            Self::Label(x) => write!(f, "{}", x)?,
            Self::LocalLabel(x) => write!(f, "{}", x)?,
            Self::True => write!(f, "true")?,
            Self::False => write!(f, "false")?,
            Self::And(x, y) => write!(f, "({} && {})", x, y)?,
            Self::Or(x, y) => write!(f, "({} || {})", x, y)?,
            Self::Not(x) => write!(f, "!({})", x)?,
        }
        Ok(())
    }
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        // simply compare immediates, constants, labels and registers
        match (self, other) {
            (Self::Immediate(x), Self::Immediate(y)) => x.value == y.value,
            (Self::Label(x), Self::Label(y)) => x.name() == y.name(),
            (Self::LabelReference(x), Self::LabelReference(y)) => {
                x.label == y.label && x.offset == y.offset
            }
            (Self::RegisterId(x), Self::RegisterId(y)) => x.name == y.name,
            (Self::FPRegisterId(x), Self::FPRegisterId(y)) => x.name == y.name,
            (Self::VecRegisterId(x), Self::VecRegisterId(y)) => x.name == y.name,
            _ => false,
        }
    }
}

impl Eq for Node {}
