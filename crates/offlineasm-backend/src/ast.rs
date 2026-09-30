//! Defines the offlineasm syntax tree.
//!
//! [`Node`] is the tree. [`LabelTable`] interns labels and their flags while
//! the parser builds it.

use crate::code_origin::CodeOrigin;
use offlineasm_ir::Reach;
use std::collections::{HashMap, HashSet};

/// Returns the origin used for builtin nodes.
pub fn builtin_origin() -> CodeOrigin {
    CodeOrigin {
        file_name: "<builtin>".to_string(),
        basename: "<builtin>".to_string(),
        file_number: 0,
        line: 0,
    }
}

/// Holds the flags recorded for one label.
#[derive(Clone, Debug)]
pub struct LabelFlags {
    /// Whether the label is defined in this file.
    pub defined_in_file: bool,
    /// Whether the label is an unresolved extern reference.
    pub is_extern: bool,
    /// Whether the label was declared global.
    pub global: bool,
    /// Whether the label keeps default alignment.
    pub aligned: bool,
    /// The explicit alignment target, when declared.
    pub align_to: Option<Box<Node>>,
    /// Whether the label was declared a global export.
    pub export: bool,
}

impl LabelFlags {
    fn fresh(defined_in_file: bool) -> Self {
        Self {
            defined_in_file,
            is_extern: true,
            global: false,
            aligned: true,
            align_to: None,
            export: false,
        }
    }
}

/// Interns labels and tracks their flags.
#[derive(Clone, Debug, Default)]
pub struct LabelTable {
    labels: HashMap<String, LabelFlags>,
    local_labels: HashSet<String>,
    /// Maps each local label to its emitted symbol text.
    pub local_strings: HashMap<String, String>,
    unique_counter: usize,
    /// Lists the extern labels recorded as referenced, in first-use order.
    pub referenced_extern: Vec<String>,
    /// Maps each label declared with `extern` to how code reaches it.
    pub declared_externs: HashMap<String, Reach>,
}

impl LabelTable {
    /// Creates an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    fn ensure_label(&mut self, name: &str, defined_in_file: bool) -> Result<(), String> {
        if defined_in_file && self.declared_externs.contains_key(name) {
            return Err(format!(
                "Label: {} is declared extern and cannot be defined",
                name
            ));
        }
        if let Some(flags) = self.labels.get_mut(name) {
            if defined_in_file {
                flags.is_extern = false;
                flags.defined_in_file = true;
            }
            return Ok(());
        }
        if self.local_labels.contains(name) {
            return Err(format!("Label name collision: {}", name));
        }
        let mut flags = LabelFlags::fresh(defined_in_file);
        if defined_in_file {
            flags.is_extern = false;
        }
        self.labels.insert(name.to_string(), flags);
        Ok(())
    }

    /// Interns `name`, marking it defined when `defined_in_file` holds.
    ///
    /// # Errors
    ///
    /// Returns an error if `name` collides with a local label.
    pub fn label_for_name(&mut self, name: &str, defined_in_file: bool) -> Result<(), String> {
        if self.local_labels.contains(name) {
            return Err(format!("Label name collision: {}", name));
        }
        self.ensure_label(name, defined_in_file)
    }

    /// Interns the local label `name` with its emitted symbol text.
    ///
    /// # Errors
    ///
    /// Returns an error if `name` collides with a global label.
    pub fn local_label_for_name(&mut self, origin: &CodeOrigin, name: &str) -> Result<(), String> {
        if self.labels.contains_key(name) {
            return Err(format!("Label name collision: {}", name));
        }
        self.local_labels.insert(name.to_string());
        self.local_strings
            .entry(name.to_string())
            .or_insert_with(|| {
                format!(
                    "__offlineasm_{}_{}",
                    name.get(1..).unwrap_or(""),
                    origin.label_string_extension()
                )
            });
        Ok(())
    }

    /// Carries the flags recorded for `old` over to `new`.
    pub fn apply_substituted_label_flags(&mut self, old: &str, new: &str) {
        if old == new {
            return;
        }
        let source = self.labels.get(old).cloned();
        let entry = self
            .labels
            .entry(new.to_string())
            .or_insert_with(|| match &source {
                Some(flags) => flags.clone(),
                // A reference to a name that was never interned: `Label.forName`
                // creates it fresh (unreferenced, non-global).
                None => LabelFlags::fresh(false),
            });
        if let Some(source) = source {
            if source.global {
                entry.global = true;
            }
            if source.export {
                entry.export = true;
            }
            if !source.aligned {
                entry.global = true;
                entry.aligned = false;
            }
            if source.aligned && source.align_to.is_some() {
                entry.aligned = true;
                entry.align_to = source.align_to.clone();
                entry.global = true;
            }
            if !source.is_extern {
                entry.is_extern = false;
                entry.defined_in_file = true;
            }
        }
    }

    /// Creates a fresh local label derived from `comment`.
    pub fn unique_local_label(&mut self, origin: &CodeOrigin, comment: &str) -> String {
        let mut candidate = format!("_{}", comment);
        if self.labels.contains_key(&candidate) || self.local_labels.contains(&candidate) {
            loop {
                candidate = format!("_{}_{}", self.unique_counter, comment);
                self.unique_counter += 1;
                if !self.labels.contains_key(&candidate) && !self.local_labels.contains(&candidate)
                {
                    break;
                }
            }
        }
        self.local_labels.insert(candidate.clone());
        let _ = origin;
        candidate
    }

    fn mark_global(&mut self, name: &str, f: impl FnOnce(&mut LabelFlags)) -> Result<(), String> {
        if self.declared_externs.contains_key(name) {
            return Err(format!(
                "Label: {} is declared extern and cannot be global",
                name
            ));
        }
        if let Some(flags) = self.labels.get_mut(name) {
            if flags.global {
                return Err(format!("Label: {} declared global multiple times", name));
            }
            f(flags);
        } else {
            if self.local_labels.contains(name) {
                return Err(format!("Label name collision: {}", name));
            }
            let mut flags = LabelFlags::fresh(false);
            f(&mut flags);
            self.labels.insert(name.to_string(), flags);
        }
        Ok(())
    }

    /// Marks `name` as global.
    ///
    /// # Errors
    ///
    /// Returns an error if `name` is already global or collides with a local label.
    pub fn set_as_global(&mut self, name: &str) -> Result<(), String> {
        self.mark_global(name, |fl| fl.global = true)
    }

    /// Marks `name` as a global export.
    ///
    /// # Errors
    ///
    /// Returns an error if `name` is already global or collides with a local label.
    pub fn set_as_global_export(&mut self, name: &str) -> Result<(), String> {
        self.mark_global(name, |fl| {
            fl.global = true;
            fl.export = true;
        })
    }

    /// Marks `name` as an unaligned global.
    ///
    /// # Errors
    ///
    /// Returns an error if `name` is already global or collides with a local label.
    pub fn set_as_unaligned_global(&mut self, name: &str) -> Result<(), String> {
        self.mark_global(name, |fl| {
            fl.global = true;
            fl.aligned = false;
        })
    }

    /// Marks `name` as an unaligned global export.
    ///
    /// # Errors
    ///
    /// Returns an error if `name` is already global or collides with a local label.
    pub fn set_as_unaligned_global_export(&mut self, name: &str) -> Result<(), String> {
        self.mark_global(name, |fl| {
            fl.global = true;
            fl.aligned = false;
            fl.export = true;
        })
    }

    /// Declares `name` an external symbol reached as `reach`.
    ///
    /// # Errors
    ///
    /// Returns an error if `name` is already declared extern, is defined or
    /// declared global in this file, or collides with a local label.
    pub fn set_as_extern(&mut self, name: &str, reach: Reach) -> Result<(), String> {
        if self.declared_externs.contains_key(name) {
            return Err(format!("Label: {} declared extern multiple times", name));
        }
        if let Some(flags) = self.labels.get(name) {
            if flags.defined_in_file {
                return Err(format!(
                    "Label: {} is defined in this file and cannot be extern",
                    name
                ));
            }
            if flags.global {
                return Err(format!(
                    "Label: {} is declared global and cannot be extern",
                    name
                ));
            }
        }
        self.label_for_name(name, false)?;
        self.declared_externs.insert(name.to_string(), reach);
        Ok(())
    }

    /// Marks `name` aligned, optionally to `align_to`.
    ///
    /// # Errors
    ///
    /// Returns an error if `name` is already aligned or collides with a local label.
    pub fn set_as_aligned(&mut self, name: &str, align_to: Option<Node>) -> Result<(), String> {
        if let Some(flags) = self.labels.get_mut(name) {
            if flags.align_to.is_some() {
                return Err(format!("Label: {} declared aligned multiple times", name));
            }
            flags.aligned = true;
            flags.align_to = align_to.map(Box::new);
            flags.global = true;
        } else {
            if self.local_labels.contains(name) {
                return Err(format!("Label name collision: {}", name));
            }
            let mut flags = LabelFlags::fresh(false);
            flags.aligned = true;
            flags.align_to = align_to.map(Box::new);
            flags.global = true;
            self.labels.insert(name.to_string(), flags);
        }
        Ok(())
    }

    /// Returns the flags recorded for `name`, when interned.
    pub fn label_flags(&self, name: &str) -> Option<&LabelFlags> {
        self.labels.get(name)
    }

    /// Reports whether `name` is an extern label.
    pub fn is_extern_label(&self, name: &str) -> bool {
        self.labels.get(name).map(|f| f.is_extern).unwrap_or(false)
    }

    /// Reports whether `name` is a global label.
    pub fn is_global_label(&self, name: &str) -> bool {
        self.labels.get(name).map(|f| f.global).unwrap_or(false)
    }

    /// Clears the referenced-extern list.
    pub fn reset_referenced(&mut self) {
        self.referenced_extern.clear();
    }

    /// Records `name` as referenced when it is extern.
    pub fn mark_used(&mut self, name: &str) {
        let is_extern = self.is_extern_label(name);
        if is_extern && !self.referenced_extern.contains(&name.to_string()) {
            self.referenced_extern.push(name.to_string());
        }
    }
}

/// Holds one offlineasm syntax tree node.
#[derive(Clone, Debug)]
pub enum Node {
    StructOffset {
        origin: CodeOrigin,
        struct_name: String,
        field: String,
    },
    Sizeof {
        origin: CodeOrigin,
        struct_name: String,
    },
    /// Holds an integer literal or folded immediate.
    Immediate {
        origin: CodeOrigin,
        value: i128,
    },
    Add {
        origin: CodeOrigin,
        left: Box<Node>,
        right: Box<Node>,
    },
    Sub {
        origin: CodeOrigin,
        left: Box<Node>,
        right: Box<Node>,
    },
    Mul {
        origin: CodeOrigin,
        left: Box<Node>,
        right: Box<Node>,
    },
    Neg {
        origin: CodeOrigin,
        child: Box<Node>,
    },
    Or {
        origin: CodeOrigin,
        left: Box<Node>,
        right: Box<Node>,
    },
    And {
        origin: CodeOrigin,
        left: Box<Node>,
        right: Box<Node>,
    },
    Xor {
        origin: CodeOrigin,
        left: Box<Node>,
        right: Box<Node>,
    },
    Bitnot {
        origin: CodeOrigin,
        child: Box<Node>,
    },
    StringLiteral {
        origin: CodeOrigin,
        value: String,
    },
    Register {
        origin: CodeOrigin,
        name: String,
    },
    FpRegister {
        origin: CodeOrigin,
        name: String,
    },
    VecRegister {
        origin: CodeOrigin,
        name: String,
    },
    SpecialRegister {
        name: String,
    },
    Variable {
        origin: CodeOrigin,
        name: String,
        original_name: String,
    },
    Address {
        origin: CodeOrigin,
        base: Box<Node>,
        offset: Box<Node>,
    },
    BaseIndex {
        origin: CodeOrigin,
        base: Box<Node>,
        index: Box<Node>,
        scale: Box<Node>,
        offset: Box<Node>,
    },
    AbsoluteAddress {
        origin: CodeOrigin,
        address: Box<Node>,
    },
    Instruction {
        origin: CodeOrigin,
        opcode: String,
        operands: Vec<Node>,
        annotation: Option<String>,
    },
    Error {
        origin: CodeOrigin,
    },
    /// Holds the (possibly `$param`-unsubstituted) tokens of a
    /// `const { ... }` block, or of the narrower `constexpr(...)`/
    /// `constexpr a::b::c` forms used in an address's scale position.
    ConstExpr {
        origin: CodeOrigin,
        value: proc_macro2::TokenStream,
    },
    ConstDecl {
        origin: CodeOrigin,
        variable: Box<Node>,
        value: Box<Node>,
    },
    Label {
        origin: CodeOrigin,
        name: String,
    },
    LocalLabel {
        origin: CodeOrigin,
        name: String,
    },
    LabelReference {
        origin: CodeOrigin,
        label: String,
        offset: i64,
    },
    LocalLabelReference {
        origin: CodeOrigin,
        label: String,
    },
    Sequence {
        origin: CodeOrigin,
        list: Vec<Node>,
    },
    True,
    False,
    Setting {
        origin: CodeOrigin,
        name: String,
    },
    AndPred {
        origin: CodeOrigin,
        left: Box<Node>,
        right: Box<Node>,
    },
    OrPred {
        origin: CodeOrigin,
        left: Box<Node>,
        right: Box<Node>,
    },
    NotPred {
        origin: CodeOrigin,
        child: Box<Node>,
    },
    Skip {
        origin: CodeOrigin,
    },
    IfThenElse {
        origin: CodeOrigin,
        predicate: Box<Node>,
        then_case: Box<Node>,
        else_case: Box<Node>,
    },
    Macro {
        origin: CodeOrigin,
        name: Option<String>,
        variables: Vec<Node>,
        body: Box<Node>,
    },
    MacroCall {
        origin: CodeOrigin,
        name: String,
        operands: Vec<Node>,
        annotation: Option<String>,
        original_name: String,
    },

    RustConst {
        origin: CodeOrigin,
        ident: String,
        expr: syn::Expr,
    },
}

impl Node {
    /// Returns the origin string, or `<builtin>` when absent.
    pub fn origin_string(&self) -> String {
        self.origin()
            .map(|o| o.origin_string())
            .unwrap_or_else(|| "<builtin>".to_string())
    }

    /// Returns the origin, when the node carries one.
    pub fn origin(&self) -> Option<&CodeOrigin> {
        match self {
            Node::StructOffset { origin, .. }
            | Node::Sizeof { origin, .. }
            | Node::Immediate { origin, .. }
            | Node::Add { origin, .. }
            | Node::Sub { origin, .. }
            | Node::Mul { origin, .. }
            | Node::Neg { origin, .. }
            | Node::Or { origin, .. }
            | Node::And { origin, .. }
            | Node::Xor { origin, .. }
            | Node::Bitnot { origin, .. }
            | Node::StringLiteral { origin, .. }
            | Node::Register { origin, .. }
            | Node::FpRegister { origin, .. }
            | Node::VecRegister { origin, .. }
            | Node::Variable { origin, .. }
            | Node::Address { origin, .. }
            | Node::BaseIndex { origin, .. }
            | Node::AbsoluteAddress { origin, .. }
            | Node::Instruction { origin, .. }
            | Node::Error { origin }
            | Node::ConstExpr { origin, .. }
            | Node::ConstDecl { origin, .. }
            | Node::Label { origin, .. }
            | Node::LocalLabel { origin, .. }
            | Node::LabelReference { origin, .. }
            | Node::LocalLabelReference { origin, .. }
            | Node::Sequence { origin, .. }
            | Node::Setting { origin, .. }
            | Node::AndPred { origin, .. }
            | Node::OrPred { origin, .. }
            | Node::NotPred { origin, .. }
            | Node::Skip { origin }
            | Node::IfThenElse { origin, .. }
            | Node::Macro { origin, .. }
            | Node::MacroCall { origin, .. }
            | Node::RustConst { origin, .. } => Some(origin),
            Node::SpecialRegister { .. } | Node::True | Node::False => None,
        }
    }

    /// Clones the origin, or a builtin origin when absent.
    pub fn origin_cloned(&self) -> CodeOrigin {
        self.origin().cloned().unwrap_or_else(builtin_origin)
    }

    /// Lists the direct children.
    pub fn children(&self) -> Vec<&Node> {
        match self {
            Node::Add { left, right, .. }
            | Node::Sub { left, right, .. }
            | Node::Mul { left, right, .. }
            | Node::Or { left, right, .. }
            | Node::And { left, right, .. }
            | Node::Xor { left, right, .. }
            | Node::AndPred { left, right, .. }
            | Node::OrPred { left, right, .. } => vec![left, right],
            Node::Neg { child, .. } | Node::Bitnot { child, .. } | Node::NotPred { child, .. } => {
                vec![child]
            }
            Node::Address { base, offset, .. } => vec![base, offset],
            Node::AbsoluteAddress { address, .. } => vec![address],
            Node::BaseIndex {
                base,
                index,
                offset,
                ..
            } => vec![base, index, offset],
            Node::Instruction { operands, .. } => operands.iter().collect(),
            Node::ConstDecl {
                variable, value, ..
            } => vec![variable, value],
            Node::Sequence { list, .. } => list.iter().collect(),
            Node::IfThenElse {
                predicate,
                then_case,
                else_case,
                ..
            } => vec![predicate, then_case, else_case],
            Node::Macro {
                variables, body, ..
            } => {
                let mut v: Vec<&Node> = variables.iter().collect();
                v.push(body);
                v
            }
            Node::MacroCall { operands, .. } => operands.iter().collect(),
            _ => vec![],
        }
    }

    /// Lists all descendants depth-first.
    pub fn descendants(&self) -> Vec<&Node> {
        let mut out = Vec::new();
        for child in self.children() {
            out.push(child);
            out.extend(child.descendants());
        }
        out
    }

    /// Lists the node plus all descendants.
    pub fn flatten_vec(&self) -> Vec<&Node> {
        let mut out = vec![self];
        out.extend(self.descendants());
        out
    }

    /// Reports whether the node is an address form.
    pub fn is_address(&self) -> bool {
        matches!(
            self,
            Node::Address { .. } | Node::BaseIndex { .. } | Node::AbsoluteAddress { .. }
        )
    }

    /// Reports whether the node references a label.
    pub fn is_label_node(&self) -> bool {
        matches!(
            self,
            Node::LabelReference { .. } | Node::LocalLabelReference { .. }
        )
    }

    /// Reports whether the node is a symbolic Rust const placeholder.
    pub fn is_rust_const(&self) -> bool {
        matches!(self, Node::RustConst { .. })
    }

    /// Reports whether the node is an immediate expression.
    pub fn is_immediate(&self) -> bool {
        matches!(
            self,
            Node::StructOffset { .. }
                | Node::Sizeof { .. }
                | Node::Immediate { .. }
                | Node::Add { .. }
                | Node::Sub { .. }
                | Node::Mul { .. }
                | Node::Neg { .. }
                | Node::Or { .. }
                | Node::And { .. }
                | Node::Xor { .. }
                | Node::Bitnot { .. }
                | Node::ConstExpr { .. }
        )
    }

    /// Reports whether the node names a register.
    pub fn is_register_node(&self) -> bool {
        matches!(
            self,
            Node::Register { .. }
                | Node::FpRegister { .. }
                | Node::VecRegister { .. }
                | Node::SpecialRegister { .. }
        )
    }

    /// Reports whether the node is an immediate operand.
    pub fn is_immediate_operand(&self) -> bool {
        matches!(
            self,
            Node::Immediate { .. }
                | Node::Add { .. }
                | Node::Sub { .. }
                | Node::Address { .. }
                | Node::AbsoluteAddress { .. }
                | Node::LabelReference { .. }
                | Node::LocalLabelReference { .. }
                | Node::RustConst { .. }
        )
    }

    /// Returns the variable name, when the node is a variable.
    pub fn variable_name(&self) -> Option<&str> {
        match self {
            Node::Variable { name, .. } => Some(name),
            _ => None,
        }
    }

    /// Returns the literal value, when the node is an immediate.
    pub fn immediate_value(&self) -> Option<i128> {
        match self {
            Node::Immediate { value, .. } => Some(*value),
            _ => None,
        }
    }

    /// Copies an address node with `extra` added to its offset.
    ///
    /// Returns `None` when the node is not an address form.
    pub fn with_offset(&self, extra: i128) -> Option<Node> {
        let origin = self.origin_cloned();
        match self {
            Node::Address { base, offset, .. } => {
                let base_offset = offset.immediate_value().unwrap_or(0);
                Some(Node::Address {
                    origin,
                    base: base.clone(),
                    offset: Box::new(Node::Immediate {
                        origin: self.origin_cloned(),
                        value: base_offset + extra,
                    }),
                })
            }
            Node::BaseIndex {
                base,
                index,
                scale,
                offset,
                ..
            } => {
                let base_offset = offset.immediate_value().unwrap_or(0);
                Some(Node::BaseIndex {
                    origin,
                    base: base.clone(),
                    index: index.clone(),
                    scale: scale.clone(),
                    offset: Box::new(Node::Immediate {
                        origin: self.origin_cloned(),
                        value: base_offset + extra,
                    }),
                })
            }
            Node::AbsoluteAddress { address, .. } => {
                let base_value = address.immediate_value().unwrap_or(0);
                Some(Node::AbsoluteAddress {
                    origin,
                    address: Box::new(Node::Immediate {
                        origin: self.origin_cloned(),
                        value: base_value + extra,
                    }),
                })
            }
            _ => None,
        }
    }

    /// Copies a label reference with `extra` added to its offset.
    ///
    /// Returns `None` when the node is not a label reference or `extra`
    /// does not fit in an `i64`.
    pub fn plus_offset(&self, extra: i128) -> Option<Node> {
        match self {
            Node::LabelReference {
                origin,
                label,
                offset,
            } => Some(Node::LabelReference {
                origin: origin.clone(),
                label: label.clone(),
                offset: offset + i64::try_from(extra).ok()?,
            }),
            _ => None,
        }
    }

    /// Returns the scale of a `BaseIndex` node.
    ///
    /// # Errors
    ///
    /// Returns an error if the node is not a `BaseIndex`, or if its scale
    /// is not 1, 2, 4, or 8.
    pub fn scale_value(&self) -> Result<i128, String> {
        match self {
            Node::BaseIndex { scale, .. } => match scale.as_ref() {
                Node::Immediate { value, .. } if [1, 2, 4, 8].contains(value) => Ok(*value),
                other => Err(format!(
                    "Bad scale: {} at {}",
                    other.dump(),
                    self.origin_string()
                )),
            },
            _ => Err(format!("Not a BaseIndex at {}", self.origin_string())),
        }
    }

    /// Returns the shift matching the scale of a `BaseIndex` node.
    ///
    /// # Errors
    ///
    /// Returns an error for any reason [`Node::scale_value`] can.
    pub fn scale_shift(&self) -> Result<u32, String> {
        match i64::try_from(self.scale_value()?)
            .map_err(|_| format!("Bad scale at {}", self.origin_string()))?
        {
            1 => Ok(0),
            2 => Ok(1),
            4 => Ok(2),
            8 => Ok(3),
            v => Err(format!("Bad scale: {} at {}", v, self.origin_string())),
        }
    }

    /// Renders the canonical text of the node.
    ///
    /// Offset keys and error messages use this form.
    pub fn dump(&self) -> String {
        match self {
            Node::StructOffset {
                struct_name, field, ..
            } => format!("{}::{}", struct_name, field),
            Node::Sizeof { struct_name, .. } => format!("sizeof {}", struct_name),
            Node::Immediate { value, .. } => format!("{}", value),
            Node::Add { left, right, .. } => format!("({} + {})", left.dump(), right.dump()),
            Node::Sub { left, right, .. } => format!("({} - {})", left.dump(), right.dump()),
            Node::Mul { left, right, .. } => format!("({} * {})", left.dump(), right.dump()),
            Node::Neg { child, .. } => format!("(-{})", child.dump()),
            Node::Or { left, right, .. } => format!("({} | {})", left.dump(), right.dump()),
            Node::And { left, right, .. } => format!("({} & {})", left.dump(), right.dump()),
            Node::Xor { left, right, .. } => format!("({} ^ {})", left.dump(), right.dump()),
            Node::Bitnot { child, .. } => format!("(~{})", child.dump()),
            Node::StringLiteral { value, .. } => value.clone(),
            Node::Register { name, .. }
            | Node::FpRegister { name, .. }
            | Node::VecRegister { name, .. } => name.clone(),
            Node::SpecialRegister { name } => name.clone(),
            Node::Variable { original_name, .. } => original_name.clone(),
            Node::Address { base, offset, .. } => format!("{}[{}]", offset.dump(), base.dump()),
            Node::BaseIndex {
                base,
                index,
                scale,
                offset,
                ..
            } => {
                format!(
                    "{}[{}, {}, {}]",
                    offset.dump(),
                    base.dump(),
                    index.dump(),
                    scale.dump()
                )
            }
            Node::AbsoluteAddress { address, .. } => format!("{}[]", address.dump()),
            Node::Instruction {
                opcode, operands, ..
            } => {
                format!(
                    "\t{} {}",
                    opcode,
                    operands
                        .iter()
                        .map(|o| o.dump())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Node::Error { .. } => "\terror".to_string(),
            Node::ConstExpr { value, .. } => format!("const {{ {} }}", quote::quote!(#value)),
            Node::ConstDecl {
                variable, value, ..
            } => format!("const {} = {}", variable.dump(), value.dump()),
            Node::Label { name, .. } | Node::LocalLabel { name, .. } => format!("{}:", name),
            Node::LabelReference { label, .. } | Node::LocalLabelReference { label, .. } => {
                label.clone()
            }
            Node::Sequence { list, .. } => {
                list.iter().map(|n| n.dump()).collect::<Vec<_>>().join("\n")
            }
            Node::True => "true".to_string(),
            Node::False => "false".to_string(),
            Node::Setting { name, .. } => name.clone(),
            Node::AndPred { left, right, .. } => format!("({} and {})", left.dump(), right.dump()),
            Node::OrPred { left, right, .. } => format!("({} or {})", left.dump(), right.dump()),
            Node::NotPred { child, .. } => format!("(not {})", child.dump()),
            Node::Skip { .. } => "\tskip".to_string(),
            Node::IfThenElse {
                predicate,
                then_case,
                else_case,
                ..
            } => {
                format!(
                    "if {}\n{}\nelse\n{}\nend",
                    predicate.dump(),
                    then_case.dump(),
                    else_case.dump()
                )
            }
            Node::Macro {
                name,
                variables,
                body,
                ..
            } => format!(
                "macro {}({})\n{}\nend",
                name.clone().unwrap_or_default(),
                variables
                    .iter()
                    .map(|v| v.dump())
                    .collect::<Vec<_>>()
                    .join(", "),
                body.dump()
            ),
            Node::MacroCall {
                original_name,
                operands,
                ..
            } => {
                format!(
                    "\t{}({})",
                    original_name,
                    operands
                        .iter()
                        .map(|o| o.dump())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Node::RustConst { ident, .. } => ident.clone(),
        }
    }
}
