use std::{
    cell::{Cell, LazyCell, RefCell},
    collections::HashMap,
    fmt::Display,
    hash::Hash,
    rc::Rc,
    sync::atomic::AtomicUsize,
};

use proc_macro2::Span;
use syn::Ident;

use crate::{
    instructions::Instruction,
    operands::{Name, Operand, Variable},
};

pub struct Label {
    pub span: Span,
    pub name: Ident,
    pub external: Cell<bool>,
    pub global: Cell<bool>,
    pub aligned: Cell<bool>,
    pub aligned_to: Cell<Option<usize>>,
    pub export: Cell<bool>,
    pub defined_in_macro: Cell<bool>,
    pub sym_id: Cell<Option<usize>>,
    pub doc: Cell<Option<Vec<String>>>,
    pub doc_span: Cell<Option<Span>>,
}

impl Label {
    pub fn for_name(name: &Ident, defined_in_macro: bool) -> syn::Result<Rc<Self>> {
        MAPPINGS.with(|map| {
            let mapping = map.intern_global(name, defined_in_macro);
            match mapping {
                LabelMapping::Global(label) => Ok(label.clone()),
                _ => Err(syn::Error::new(name.span(), "Expected global label")),
            }
        })
    }
}

impl PartialEq for Label {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Eq for Label {}

impl Hash for Label {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "->{}:", self.name)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum LabelMapping {
    Global(Rc<Label>),
    Local(Rc<LocalLabel>),
}

impl LabelMapping {
    pub fn name(&self) -> &Ident {
        match self {
            Self::Global(x) => &x.name,
            Self::Local(x) => &x.name,
        }
    }
}

impl Display for LabelMapping {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LabelMapping::Global(label) => write!(f, "{}", label),
            LabelMapping::Local(label) => write!(f, "{}", label),
        }
    }
}

impl LabelMapping {
    pub fn is_global(&self) -> bool {
        matches!(self, LabelMapping::Global(_))
    }

    pub fn is_local(&self) -> bool {
        matches!(self, LabelMapping::Local(_))
    }

    pub fn unwrap_global(&self) -> &Rc<Label> {
        match self {
            LabelMapping::Global(label) => label,
            _ => panic!("Expected global label"),
        }
    }

    pub fn unwrap_local(&self) -> &Rc<LocalLabel> {
        match self {
            LabelMapping::Local(label) => label,
            _ => panic!("Expected local label"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct LocalLabel {
    pub name: Ident,
}

impl Display for LocalLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:", self.name)
    }
}

pub struct LabelMappings {
    mappings: RefCell<HashMap<Ident, LabelMapping>>,
}

impl LabelMappings {
    pub fn new() -> Self {
        Self {
            mappings: RefCell::new(HashMap::new()),
        }
    }
    pub fn intern_global(&self, name: &Ident, defined_in_macro: bool) -> LabelMapping {
        if let Some(mapping) = self.mappings.borrow().get(&name) {
            return mapping.clone();
        }
        let label = Rc::new(Label {
            span: name.span(),
            name: name.clone(),
            external: Cell::new(false),
            global: Cell::new(true),
            aligned: Cell::new(false),
            aligned_to: Cell::new(None),
            export: Cell::new(false),
            defined_in_macro: Cell::new(defined_in_macro),
            sym_id: Cell::new(None),
            doc: Cell::new(None),
            doc_span: Cell::new(None),
        });
        let mapping = LabelMapping::Global(label);
        self.mappings
            .borrow_mut()
            .insert(name.clone(), mapping.clone());
        mapping
    }

    pub fn intern_local(&self, name: &Ident) -> LabelMapping {
        if let Some(mapping) = self.mappings.borrow().get(&name) {
            return mapping.clone();
        }
        let label = Rc::new(LocalLabel { name: name.clone() });
        let mapping = LabelMapping::Local(label);
        self.mappings
            .borrow_mut()
            .insert(name.clone(), mapping.clone());
        mapping
    }

    pub fn exists(&self, name: &Ident) -> bool {
        self.mappings.borrow().contains_key(name)
    }
}

thread_local! {
    static MAPPINGS: LazyCell<LabelMappings> = LazyCell::new(LabelMappings::new);
}
static UNIQUE_NAME_COUNTER: AtomicUsize = AtomicUsize::new(0);

impl LocalLabel {
    pub fn unique(comment: &str) -> Rc<Self> {
        let mut new_name = format!("_{comment}");
        MAPPINGS.with(|map| {
            let map = &**map;
            if map.exists(&Ident::new(&new_name, Span::call_site())) {
                loop {
                    new_name = format!(
                        "_{comment}_{}",
                        UNIQUE_NAME_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                    );

                    if !map.exists(&Ident::new(&new_name, Span::call_site())) {
                        break;
                    }
                }
            }
        });
        Self::for_name(&Ident::new(&new_name, Span::call_site())).unwrap()
    }

    pub fn for_name(name: &Ident) -> syn::Result<Rc<Self>> {
        MAPPINGS.with(|map| {
            let map = &**map;
            let mapping = map.intern_local(name);
            match mapping {
                LabelMapping::Local(label) => Ok(label.clone()),
                _ => Err(syn::Error::new(name.span(), "Expected local label")),
            }
        })
    }
}

#[derive(Clone)]
pub struct MacroCall {
    pub span: Span,
    pub name: Ident,
    pub original_name: Option<Name>,
    pub arguments: Vec<MacroArgument>,
}

impl Display for MacroCall {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}({})",
            self.name,
            self.arguments
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(",")
        )?;
        Ok(())
    }
}

#[derive(Clone)]
pub enum MacroArgument {
    Operand(Operand),
    /// Lambda macro
    Macro(Rc<Macro>),
}

impl Display for MacroArgument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MacroArgument::Operand(o) => write!(f, "{}", o),
            MacroArgument::Macro(m) => write!(f, "{}", m),
        }
    }
}

#[derive(Clone)]
pub struct Macro {
    pub span: Span,
    pub name: Ident,
    pub args: Vec<Variable>,
    pub body: Sequence,
}

impl Display for Macro {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "macro {}({}) {}",
            self.name,
            self.args
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(","),
            self.body
        )
    }
}

#[derive(Clone)]
pub struct Sequence {
    pub span: Span,
    pub stmts: Vec<Stmt>,
}

impl Display for Sequence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("{\n")?;
        for stmt in &self.stmts {
            write!(f, "{}\n", stmt)?;
        }
        f.write_str("}\n")?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct ConstDecl {
    pub span: Span,
    pub name: Ident,
    pub value: Operand,
}

impl Display for ConstDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "const {} = {};", self.name, self.value)
    }
}

pub struct Predicate {
    pub span: Span,
    pub expr: PredicateExpr,
    pub then: Stmt,
    pub else_case: Option<Stmt>,
}

impl Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "if ({}) {{\n{}\n}}", self.expr, self.then)?;
        if let Some(else_case) = &self.else_case {
            write!(f, "else {{\n{}\n}}", else_case)?;
        }
        Ok(())
    }
}

#[derive(Clone)]
pub enum Stmt {
    Sequence(Rc<Sequence>),
    Label(Rc<Label>),
    LocalLabel(Rc<LocalLabel>),
    MacroCall(Rc<MacroCall>),
    Macro(Rc<Macro>),
    ConstDecl(Rc<ConstDecl>),
    Instruction(Rc<Instruction>),
    Predicate(Rc<Predicate>),
}

impl From<Rc<LocalLabel>> for Stmt {
    fn from(l: Rc<LocalLabel>) -> Self {
        Self::LocalLabel(l)
    }
}

impl From<Rc<Label>> for Stmt {
    fn from(l: Rc<Label>) -> Self {
        Self::Label(l)
    }
}

impl From<Rc<Instruction>> for Stmt {
    fn from(i: Rc<Instruction>) -> Self {
        Self::Instruction(i)
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stmt::Sequence(s) => write!(f, "{}", s),
            Stmt::Label(l) => write!(f, "{}", l),
            Stmt::LocalLabel(l) => write!(f, "{}", l),
            Stmt::MacroCall(m) => write!(f, "{}", m),
            Stmt::Macro(m) => write!(f, "{}", m),
            Stmt::ConstDecl(c) => write!(f, "{}", c),
            Stmt::Instruction(i) => write!(f, "{}", i),
            Stmt::Predicate(predicate) => {
                write!(f, "{}", predicate)
            }
        }
    }
}

#[derive(Clone)]
pub enum PredicateExpr {
    Setting(Ident),
    And(Rc<PredicateExpr>, Rc<PredicateExpr>),
    Or(Rc<PredicateExpr>, Rc<PredicateExpr>),
    Not(Rc<PredicateExpr>),
}

impl Display for PredicateExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredicateExpr::Setting(ident) => write!(f, "{}", ident),
            PredicateExpr::And(a, b) => write!(f, "{} && {}", a, b),
            PredicateExpr::Or(a, b) => write!(f, "{} || {}", a, b),
            PredicateExpr::Not(a) => write!(f, "!{}", a),
        }
    }
}

pub struct Toplevel {
    pub stmts: Vec<Stmt>,
    pub settings: HashMap<Ident, bool>,
}

impl Display for Toplevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for stmt in &self.stmts {
            writeln!(f, "{}", stmt)?;
        }
        Ok(())
    }
}
