//! Rewrites the syntax tree toward lowering.
//!
//! [`resolve_settings`] folds `if` branches, [`demacroify`] expands macros,
//! [`resolve_offsets`] substitutes offsets, and [`fold`] folds constants.
//! [`validate`] checks earlier stages left nothing behind. [`resolve`] runs
//! the demacroify, offset, and fold stages in order.

use crate::ast::Node;
use std::collections::HashMap;

fn predicate_value(node: &Node) -> Result<bool, String> {
    match node {
        Node::True => Ok(true),
        Node::False => Ok(false),
        other => Err(format!(
            "expected predicate, got {} at {}",
            other.dump(),
            other.origin_string()
        )),
    }
}

/// Substitutes each `Node::Setting` in `node` per `settings`.
///
/// Each setting becomes `True` or `False`, then predicates fold.
///
/// # Errors
///
/// - Returns an error if `node` references a setting absent from `settings`.
/// - Returns an error if a predicate does not fold to `True`/`False`.
pub fn resolve_settings(node: &Node, settings: &HashMap<String, bool>) -> Result<Node, String> {
    match node {
        Node::True | Node::False => Ok(node.clone()),
        Node::Setting { origin: _, name } => match settings.get(name) {
            Some(true) => Ok(Node::True),
            Some(false) => Ok(Node::False),
            None => Err(format!(
                "unknown setting {} at {}",
                name,
                node.origin_string()
            )),
        },
        Node::AndPred { left, right, .. } => {
            let l = resolve_settings(left, settings)?;
            let r = resolve_settings(right, settings)?;
            Ok(if predicate_value(&l)? && predicate_value(&r)? {
                Node::True
            } else {
                Node::False
            })
        }
        Node::OrPred { left, right, .. } => {
            let l = resolve_settings(left, settings)?;
            let r = resolve_settings(right, settings)?;
            Ok(if predicate_value(&l)? || predicate_value(&r)? {
                Node::True
            } else {
                Node::False
            })
        }
        Node::NotPred { child, .. } => {
            let c = resolve_settings(child, settings)?;
            Ok(if !predicate_value(&c)? {
                Node::True
            } else {
                Node::False
            })
        }
        Node::IfThenElse {
            predicate,
            then_case,
            else_case,
            ..
        } => {
            let p = resolve_settings(predicate, settings)?;
            if predicate_value(&p)? {
                resolve_settings(then_case, settings)
            } else {
                resolve_settings(else_case, settings)
            }
        }
        Node::Sequence { origin, list } => {
            let mut new_list = Vec::new();
            for item in list {
                let resolved = resolve_settings(item, settings)?;
                match resolved {
                    Node::Sequence { list: inner, .. } => new_list.extend(inner),
                    other => new_list.push(other),
                }
            }
            Ok(Node::Sequence {
                origin: origin.clone(),
                list: new_list,
            })
        }
        _ => map_children(node, &mut |child| resolve_settings(child, settings)),
    }
}

#[allow(clippy::redundant_closure)]
fn map_children(
    node: &Node,
    f: &mut dyn FnMut(&Node) -> Result<Node, String>,
) -> Result<Node, String> {
    match node {
        Node::Add {
            origin,
            left,
            right,
        } => Ok(Node::Add {
            origin: origin.clone(),
            left: Box::new(f(left)?),
            right: Box::new(f(right)?),
        }),
        Node::Sub {
            origin,
            left,
            right,
        } => Ok(Node::Sub {
            origin: origin.clone(),
            left: Box::new(f(left)?),
            right: Box::new(f(right)?),
        }),
        Node::Mul {
            origin,
            left,
            right,
        } => Ok(Node::Mul {
            origin: origin.clone(),
            left: Box::new(f(left)?),
            right: Box::new(f(right)?),
        }),
        Node::Or {
            origin,
            left,
            right,
        } => Ok(Node::Or {
            origin: origin.clone(),
            left: Box::new(f(left)?),
            right: Box::new(f(right)?),
        }),
        Node::And {
            origin,
            left,
            right,
        } => Ok(Node::And {
            origin: origin.clone(),
            left: Box::new(f(left)?),
            right: Box::new(f(right)?),
        }),
        Node::Xor {
            origin,
            left,
            right,
        } => Ok(Node::Xor {
            origin: origin.clone(),
            left: Box::new(f(left)?),
            right: Box::new(f(right)?),
        }),
        Node::Neg { origin, child } => Ok(Node::Neg {
            origin: origin.clone(),
            child: Box::new(f(child)?),
        }),
        Node::Bitnot { origin, child } => Ok(Node::Bitnot {
            origin: origin.clone(),
            child: Box::new(f(child)?),
        }),
        Node::Address {
            origin,
            base,
            offset,
        } => Ok(Node::Address {
            origin: origin.clone(),
            base: Box::new(f(base)?),
            offset: Box::new(f(offset)?),
        }),
        Node::BaseIndex {
            origin,
            base,
            index,
            scale,
            offset,
        } => Ok(Node::BaseIndex {
            origin: origin.clone(),
            base: Box::new(f(base)?),
            index: Box::new(f(index)?),
            scale: Box::new(f(scale)?),
            offset: Box::new(f(offset)?),
        }),
        Node::Instruction {
            origin,
            opcode,
            operands,
            annotation,
        } => Ok(Node::Instruction {
            origin: origin.clone(),
            opcode: opcode.clone(),
            operands: operands
                .iter()
                .map(|c| f(c))
                .collect::<Result<Vec<_>, _>>()?,
            annotation: annotation.clone(),
        }),
        Node::ConstDecl {
            origin,
            variable,
            value,
        } => Ok(Node::ConstDecl {
            origin: origin.clone(),
            variable: Box::new(f(variable)?),
            value: Box::new(f(value)?),
        }),
        Node::Sequence { origin, list } => Ok(Node::Sequence {
            origin: origin.clone(),
            list: list.iter().map(|c| f(c)).collect::<Result<Vec<_>, _>>()?,
        }),
        Node::AndPred {
            origin,
            left,
            right,
        } => Ok(Node::AndPred {
            origin: origin.clone(),
            left: Box::new(f(left)?),
            right: Box::new(f(right)?),
        }),
        Node::OrPred {
            origin,
            left,
            right,
        } => Ok(Node::OrPred {
            origin: origin.clone(),
            left: Box::new(f(left)?),
            right: Box::new(f(right)?),
        }),
        Node::NotPred { origin, child } => Ok(Node::NotPred {
            origin: origin.clone(),
            child: Box::new(f(child)?),
        }),
        Node::IfThenElse {
            origin,
            predicate,
            then_case,
            else_case,
        } => Ok(Node::IfThenElse {
            origin: origin.clone(),
            predicate: Box::new(f(predicate)?),
            then_case: Box::new(f(then_case)?),
            else_case: Box::new(f(else_case)?),
        }),
        Node::Macro {
            origin,
            name,
            variables,
            body,
        } => Ok(Node::Macro {
            origin: origin.clone(),
            name: name.clone(),
            variables: variables
                .iter()
                .map(|c| f(c))
                .collect::<Result<Vec<_>, _>>()?,
            body: Box::new(f(body)?),
        }),
        Node::MacroCall {
            origin,
            name,
            operands,
            annotation,
            original_name,
        } => Ok(Node::MacroCall {
            origin: origin.clone(),
            name: name.clone(),
            operands: operands
                .iter()
                .map(|c| f(c))
                .collect::<Result<Vec<_>, _>>()?,
            annotation: annotation.clone(),
            original_name: original_name.clone(),
        }),
        _ => Ok(node.clone()),
    }
}

/// Substitutes each `$param` reference in `name` that `mapping` covers.
fn expand_concatenation(name: &str, mapping: &HashMap<String, Node>, for_fresh: bool) -> String {
    let mut out = String::new();
    let bytes = name.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'$' {
            let start = i + 1;
            let mut end = start;
            while end < bytes.len() && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_') {
                end += 1;
            }
            if end > start {
                let var = &name[start..end];
                if let Some(rep) = mapping.get(var) {
                    let rep_name = rep.variable_name().unwrap_or(var);
                    if for_fresh {
                        out.push('$');
                        out.push_str(rep_name);
                    } else {
                        out.push_str(rep_name);
                    }
                    i = end;
                    continue;
                }
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }
    out
}

fn contains_concat(s: &str) -> bool {
    s.contains('$')
}

/// Substitutes each `$param` token pair (`Punct('$')` immediately followed
/// by an `Ident`) that `mapping` covers, walking into nested groups. This
/// is the token-level equivalent of `expand_concatenation`, used for
/// `Node::ConstExpr`'s token-stream value (an embedded Rust expression,
/// not a plain name) so substitution never has to round-trip through text.
fn expand_concatenation_tokens(
    tokens: &proc_macro2::TokenStream,
    mapping: &HashMap<String, Node>,
    for_fresh: bool,
) -> proc_macro2::TokenStream {
    use proc_macro2::{Group, TokenTree};
    let mut out = Vec::new();
    let mut iter = tokens.clone().into_iter().peekable();
    while let Some(tt) = iter.next() {
        match tt {
            TokenTree::Punct(p) if p.as_char() == '$' => {
                if let Some(TokenTree::Ident(id)) = iter.peek() {
                    let param = id.to_string();
                    if let Some(rep) = mapping.get(&param) {
                        let rep_name = rep.variable_name().unwrap_or(&param).to_string();
                        let id_span = id.span();
                        iter.next();
                        if for_fresh {
                            out.push(TokenTree::Punct(p));
                        }
                        out.push(TokenTree::Ident(proc_macro2::Ident::new(
                            &rep_name, id_span,
                        )));
                        continue;
                    }
                }
                out.push(TokenTree::Punct(p));
            }
            TokenTree::Group(g) => {
                let inner = expand_concatenation_tokens(&g.stream(), mapping, for_fresh);
                let mut new_group = Group::new(g.delimiter(), inner);
                new_group.set_span(g.span());
                out.push(TokenTree::Group(new_group));
            }
            other => out.push(other),
        }
    }
    out.into_iter().collect()
}

fn fresh_variables(
    node: &Node,
    mapping: &HashMap<String, Node>,
    next_id: &mut usize,
    label_renames: &mut Vec<(String, String)>,
) -> Node {
    match node {
        Node::Macro {
            origin,
            name,
            variables,
            body,
        } => {
            let mut my_mapping = mapping.clone();
            let mut new_vars = Vec::new();
            for var in variables {
                if let Some(var_name) = var.variable_name() {
                    *next_id += 1;
                    let new_name = format!("_var{}", next_id);
                    let new_var = Node::Variable {
                        origin: var
                            .origin()
                            .cloned()
                            .unwrap_or_else(crate::ast::builtin_origin),
                        name: new_name.clone(),
                        original_name: var_name.to_string(),
                    };
                    my_mapping.insert(var_name.to_string(), new_var.clone());
                    new_vars.push(new_var);
                }
            }
            Node::Macro {
                origin: origin.clone(),
                name: name.clone(),
                variables: new_vars,
                body: Box::new(fresh_variables(body, &my_mapping, next_id, label_renames)),
            }
        }
        Node::MacroCall {
            origin,
            name,
            operands,
            annotation,
            original_name,
        } => {
            let new_name = match mapping.get(name) {
                Some(Node::Variable { name: rep, .. }) => rep.clone(),
                _ => name.clone(),
            };
            Node::MacroCall {
                origin: origin.clone(),
                name: new_name,
                operands: operands
                    .iter()
                    .map(|o| fresh_variables(o, mapping, next_id, label_renames))
                    .collect(),
                annotation: annotation.clone(),
                original_name: original_name.clone(),
            }
        }
        Node::Variable {
            origin,
            name,
            original_name,
        } => {
            if contains_concat(name) {
                let expanded = expand_concatenation(name, mapping, true);
                Node::Variable {
                    origin: origin.clone(),
                    name: expanded,
                    original_name: original_name.clone(),
                }
            } else if let Some(rep) = mapping.get(name) {
                rep.clone()
            } else {
                node.clone()
            }
        }
        Node::StructOffset {
            origin,
            struct_name,
            field,
        } => {
            let dump = format!("{}::{}", struct_name, field);
            if contains_concat(&dump) {
                let expanded = expand_concatenation(&dump, mapping, true);
                let mut parts: Vec<&str> = expanded.split("::").collect();
                let f = parts.pop().unwrap_or("").to_string();
                Node::StructOffset {
                    origin: origin.clone(),
                    struct_name: parts.join("::"),
                    field: f,
                }
            } else {
                node.clone()
            }
        }
        Node::Label { origin, name } => {
            // Align data lives in the LabelTable, so only rename `%` names here.
            if contains_concat(name) {
                let new_name = expand_concatenation(name, mapping, true);
                // `Label#freshVariables` re-interns the renamed label through
                // `Label.forName`, carrying the original's flags along.
                label_renames.push((name.clone(), new_name.clone()));
                Node::Label {
                    origin: origin.clone(),
                    name: new_name,
                }
            } else {
                node.clone()
            }
        }
        Node::LabelReference {
            origin,
            label,
            offset,
        } => {
            if contains_concat(label) {
                let new_label = expand_concatenation(label, mapping, true);
                label_renames.push((label.clone(), new_label.clone()));
                Node::LabelReference {
                    origin: origin.clone(),
                    label: new_label,
                    offset: *offset,
                }
            } else {
                node.clone()
            }
        }
        Node::ConstExpr { origin, value } => Node::ConstExpr {
            origin: origin.clone(),
            value: expand_concatenation_tokens(value, mapping, true),
        },
        Node::Sizeof {
            origin,
            struct_name,
        } => {
            if contains_concat(struct_name) {
                Node::Sizeof {
                    origin: origin.clone(),
                    struct_name: expand_concatenation(struct_name, mapping, true),
                }
            } else {
                node.clone()
            }
        }
        _ => match node {
            Node::Add {
                origin,
                left,
                right,
            } => Node::Add {
                origin: origin.clone(),
                left: Box::new(fresh_variables(left, mapping, next_id, label_renames)),
                right: Box::new(fresh_variables(right, mapping, next_id, label_renames)),
            },
            Node::Sequence { origin, list } => Node::Sequence {
                origin: origin.clone(),
                list: list
                    .iter()
                    .map(|n| fresh_variables(n, mapping, next_id, label_renames))
                    .collect(),
            },
            Node::Instruction {
                origin,
                opcode,
                operands,
                annotation,
            } => Node::Instruction {
                origin: origin.clone(),
                opcode: opcode.clone(),
                operands: operands
                    .iter()
                    .map(|n| fresh_variables(n, mapping, next_id, label_renames))
                    .collect(),
                annotation: annotation.clone(),
            },
            _ => map_children(node, &mut |c| {
                Ok(fresh_variables(c, mapping, next_id, label_renames))
            })
            .unwrap_or_else(|_| node.clone()),
        },
    }
}

fn substitute(
    node: &Node,
    mapping: &HashMap<String, Node>,
    label_renames: &mut Vec<(String, String)>,
) -> Node {
    match node {
        Node::Variable { origin, name, .. } => {
            if contains_concat(name) {
                let expanded = expand_concatenation(name, mapping, false);
                Node::Variable {
                    origin: origin.clone(),
                    name: expanded.clone(),
                    original_name: expanded,
                }
            } else if let Some(rep) = mapping.get(name) {
                rep.clone()
            } else {
                node.clone()
            }
        }
        Node::StructOffset {
            origin,
            struct_name,
            field,
        } => {
            let dump = format!("{}::{}", struct_name, field);
            if contains_concat(&dump) {
                let expanded = expand_concatenation(&dump, mapping, false);
                let mut parts: Vec<&str> = expanded.split("::").collect();
                let f = parts.pop().unwrap_or("").to_string();
                Node::StructOffset {
                    origin: origin.clone(),
                    struct_name: parts.join("::"),
                    field: f,
                }
            } else {
                node.clone()
            }
        }
        Node::Macro {
            origin,
            name,
            variables,
            body,
        } => {
            let var_names: Vec<String> = variables
                .iter()
                .filter_map(|v| v.variable_name().map(|s| s.to_string()))
                .collect();
            let mut my_mapping = HashMap::new();
            for (k, v) in mapping {
                if !var_names.contains(k) {
                    my_mapping.insert(k.clone(), v.clone());
                }
            }
            Node::Macro {
                origin: origin.clone(),
                name: name.clone(),
                variables: variables.clone(),
                body: Box::new(substitute(body, &my_mapping, label_renames)),
            }
        }
        Node::LabelReference {
            origin,
            label,
            offset,
        } => {
            if contains_concat(label) {
                let new_label = expand_concatenation(label, mapping, false);
                label_renames.push((label.clone(), new_label.clone()));
                Node::LabelReference {
                    origin: origin.clone(),
                    label: new_label,
                    offset: *offset,
                }
            } else {
                node.clone()
            }
        }
        Node::ConstExpr { origin, value } => Node::ConstExpr {
            origin: origin.clone(),
            value: expand_concatenation_tokens(value, mapping, false),
        },
        Node::Sizeof {
            origin,
            struct_name,
        } => {
            if contains_concat(struct_name) {
                Node::Sizeof {
                    origin: origin.clone(),
                    struct_name: expand_concatenation(struct_name, mapping, false),
                }
            } else {
                node.clone()
            }
        }
        Node::Label { origin, name } => {
            if contains_concat(name) {
                let new_name = expand_concatenation(name, mapping, false);
                label_renames.push((name.clone(), new_name.clone()));
                Node::Label {
                    origin: origin.clone(),
                    name: new_name,
                }
            } else {
                node.clone()
            }
        }
        Node::Sequence { origin, list } => {
            // ConstDecls substitute lexically here.
            let mut my_constants = mapping.clone();
            let mut new_list = Vec::new();
            for item in list {
                if let Node::ConstDecl {
                    variable, value, ..
                } = item
                {
                    if let Some(name) = variable.variable_name() {
                        let resolved = substitute(value, &my_constants, label_renames);
                        my_constants.insert(name.to_string(), resolved);
                    }
                } else {
                    new_list.push(substitute(item, &my_constants, label_renames));
                }
            }
            Node::Sequence {
                origin: origin.clone(),
                list: new_list,
            }
        }
        _ => map_children(node, &mut |c| Ok(substitute(c, mapping, label_renames)))
            .unwrap_or_else(|_| node.clone()),
    }
}

fn substitute_labels(
    node: &Node,
    mapping: &HashMap<String, String>,
    seq_origin: &crate::code_origin::CodeOrigin,
) -> Node {
    match node {
        Node::LocalLabel { name, .. } => {
            let new_name = mapping.get(name).cloned().unwrap_or_else(|| name.clone());
            Node::LocalLabel {
                origin: seq_origin.clone(),
                name: new_name,
            }
        }
        Node::LocalLabelReference { origin, label } => {
            let new_label = mapping.get(label).cloned().unwrap_or_else(|| label.clone());
            Node::LocalLabelReference {
                origin: origin.clone(),
                label: new_label,
            }
        }
        _ => map_children(node, &mut |c| Ok(substitute_labels(c, mapping, seq_origin)))
            .unwrap_or_else(|_| node.clone()),
    }
}

/// Tracks macro-expansion state across recursive calls.
#[derive(Default)]
struct DemacroState {
    next_var_id: usize,
    stack: Vec<Node>,
    label_names: std::collections::HashSet<String>,
    next_unique_label_id: usize,
    /// Records `(old, new)` pairs `substitute` makes for `%...%` label names.
    label_renames: Vec<(String, String)>,
}

impl DemacroState {
    fn unique_local_label(&mut self, comment: &str) -> String {
        let mut candidate = format!("_{}", comment);
        if self.label_names.contains(&candidate) {
            loop {
                candidate = format!("_{}_{}", self.next_unique_label_id, comment);
                if !self.label_names.contains(&candidate) {
                    break;
                }
                self.next_unique_label_id += 1;
            }
        }
        self.label_names.insert(candidate.clone());
        candidate
    }
}

#[derive(Default)]
struct MacroEnv {
    scopes: Vec<HashMap<String, std::rc::Rc<Node>>>,
}

impl MacroEnv {
    fn push(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop(&mut self) {
        self.scopes.pop();
    }

    fn insert(&mut self, name: String, macro_node: std::rc::Rc<Node>) {
        match self.scopes.last_mut() {
            Some(scope) => {
                scope.insert(name, macro_node);
            }
            None => {
                let mut scope = HashMap::new();
                scope.insert(name, macro_node);
                self.scopes.push(scope);
            }
        }
    }

    fn lookup(&self, name: &str) -> Option<std::rc::Rc<Node>> {
        for scope in self.scopes.iter().rev() {
            if let Some(found) = scope.get(name) {
                return Some(found.clone());
            }
        }
        None
    }
}

/// Expands every macro invocation in `node`.
///
/// Inlines `const` declarations. Only core instruction and
/// control-flow nodes remain.
///
/// # Errors
///
/// - Returns an error if a macro call passes the wrong number of arguments.
/// - Returns an error if an unresolved variable or macro name survives expansion.
/// - Returns an error if a settings predicate does not fold to `True`/`False`.
pub fn demacroify(node: &Node) -> Result<Node, String> {
    Ok(demacroify_recording(node)?.0)
}

/// Expands macros like [`demacroify`], also returning label renames.
///
/// Each `(old, new)` pair records a local label freshened per call site.
///
/// # Errors
///
/// Returns an error for any reason [`demacroify`] can.
pub fn demacroify_recording(node: &Node) -> Result<(Node, Vec<(String, String)>), String> {
    let mut state = DemacroState::default();
    collect_local_label_names(node, &mut state.label_names);
    let mut env = MacroEnv::default();
    let result = demacroify_with(node, &mut env, &mut state)?;
    Ok((result, state.label_renames))
}

fn collect_local_label_names(node: &Node, out: &mut std::collections::HashSet<String>) {
    if let Node::LocalLabel { name, .. } = node {
        out.insert(name.clone());
    }
    for child in node.children() {
        collect_local_label_names(child, out);
    }
}

fn demacroify_with(
    node: &Node,
    env: &mut MacroEnv,
    state: &mut DemacroState,
) -> Result<Node, String> {
    match node {
        Node::Sequence { origin, list } => {
            env.push();
            for item in list {
                if let Node::Macro {
                    name: Some(name), ..
                } = item
                {
                    let fresh = fresh_variables(
                        item,
                        &HashMap::new(),
                        &mut state.next_var_id,
                        &mut state.label_renames,
                    );
                    env.insert(name.clone(), std::rc::Rc::new(fresh));
                }
            }
            let mut new_list = Vec::new();
            for item in list {
                match item {
                    Node::Macro { .. } => {}
                    Node::MacroCall {
                        origin: call_origin,
                        name,
                        operands,
                        annotation,
                        original_name,
                    } => {
                        state.stack.push(item.clone());
                        let def = env.lookup(name).ok_or_else(|| {
                            format!(
                                "Could not find macro {} at {}",
                                original_name,
                                call_origin.origin_string()
                            )
                        })?;
                        let (params, body) = match def.as_ref() {
                            Node::Macro {
                                variables, body, ..
                            } => (variables.clone(), body.clone()),
                            _ => {
                                return Err(format!(
                                    "macro {} is not a macro at {}",
                                    name,
                                    call_origin.origin_string()
                                ))
                            }
                        };
                        if operands.len() != params.len() {
                            return Err(format!(
                                "Argument count mismatch for call to {} (expected {} but got {}) at {}",
                                original_name,
                                params.len(),
                                operands.len(),
                                call_origin.origin_string()
                            ));
                        }
                        let mut mapping: HashMap<String, Node> = HashMap::new();
                        env.push();
                        for (idx, param) in params.iter().enumerate() {
                            let param_name = param
                                .variable_name()
                                .ok_or_else(|| {
                                    format!("bad macro param at {}", param.origin_string())
                                })?
                                .to_string();
                            let arg = &operands[idx];
                            if let Some(arg_name) = arg.variable_name() {
                                if let Some(target) = env.lookup(arg_name) {
                                    env.insert(param_name.clone(), target);
                                    continue;
                                }
                            }
                            if matches!(arg, Node::Macro { .. }) {
                                let fresh = fresh_variables(
                                    arg,
                                    &HashMap::new(),
                                    &mut state.next_var_id,
                                    &mut state.label_renames,
                                );
                                // The passed macro may be anonymous (e.g.
                                // `forEachGPCalleeSave(macro (reg, index) ... end)`),
                                // so it cannot be keyed by name. It is bound
                                // under the *parameter's* (freshened) name.
                                env.insert(param_name.clone(), std::rc::Rc::new(fresh));
                                continue;
                            }
                            // Value arguments bind in `mapping` only. The macro
                            // environment stays untouched so an outer macro
                            // of the same name survives.
                            mapping.insert(param_name, arg.clone());
                        }
                        if let Some(ann) = annotation {
                            new_list.push(Node::Instruction {
                                origin: call_origin.clone(),
                                opcode: "localAnnotation".to_string(),
                                operands: vec![],
                                annotation: Some(ann.clone()),
                            });
                        }
                        let expanded = substitute(&body, &mapping, &mut state.label_renames);
                        let expanded = demacroify_with(&expanded, env, state)?;
                        env.pop();
                        let renamed = rename_labels(&expanded, Some(original_name), state);
                        match renamed {
                            Node::Sequence { list: inner, .. } => new_list.extend(inner),
                            other => new_list.push(other),
                        }
                        state.stack.pop();
                    }
                    other => new_list.push(demacroify_with(other, env, state)?),
                }
            }
            env.pop();
            let seq = Node::Sequence {
                origin: origin.clone(),
                list: new_list,
            };
            Ok(substitute(&seq, &HashMap::new(), &mut state.label_renames))
        }
        _ => map_children(node, &mut |c| demacroify_with(c, env, state)),
    }
}

fn rename_labels(node: &Node, comment: Option<&str>, state: &mut DemacroState) -> Node {
    let (seq_origin, seq) = match node {
        Node::Sequence { origin, list } => (origin, list),
        _ => return node.clone(),
    };
    let mut mapping: HashMap<String, String> = HashMap::new();
    for item in seq {
        if let Node::LocalLabel { name, .. } = item {
            // `LocalLabel#cleanName`: `.foo` -> `_foo`, otherwise unchanged.
            let clean = match name.strip_prefix('.') {
                Some(rest) => format!("_{}", rest),
                None => name.clone(),
            };
            let comment_prefix = match comment {
                Some(c) => format!("{}_", c),
                None => String::new(),
            };
            let new_name = state.unique_local_label(&format!("{}{}", comment_prefix, clean));
            mapping.insert(name.clone(), new_name);
        }
    }
    substitute_labels(node, &mapping, seq_origin)
}

fn offset_key(node: &Node) -> String {
    node.dump()
}

/// Collects the offset, size, and const keys `node` references.
///
/// Groups run offsets, then sizes, then consts. Keys are node dumps, sorted
/// within each group.
pub fn offset_keys(node: &Node) -> Vec<String> {
    let mut offsets = std::collections::BTreeSet::new();
    let mut sizes = std::collections::BTreeSet::new();
    let mut consts = std::collections::BTreeSet::new();
    collect_offset_keys(node, &mut offsets, &mut sizes, &mut consts);
    let mut out: Vec<String> = offsets.into_iter().chain(sizes).chain(consts).collect();
    let _ = &mut out;
    out
}

fn collect_offset_keys(
    node: &Node,
    offsets: &mut std::collections::BTreeSet<String>,
    sizes: &mut std::collections::BTreeSet<String>,
    consts: &mut std::collections::BTreeSet<String>,
) {
    match node {
        Node::StructOffset { .. } => {
            offsets.insert(offset_key(node));
        }
        Node::Sizeof { .. } => {
            sizes.insert(offset_key(node));
        }
        Node::ConstExpr { .. } => {
            consts.insert(offset_key(node));
        }
        _ => {}
    }
    for child in node.children() {
        collect_offset_keys(child, offsets, sizes, consts);
    }
}

/// Substitutes each offset node in `node` with the integer `map` holds.
///
/// Offset nodes are `StructOffset`, `Sizeof`, and `ConstExpr`, keyed by node
/// dump.
///
/// # Errors
///
/// Returns an error if `map` lacks the key for an offset node.
pub fn resolve_offsets(node: &Node, map: &HashMap<String, i64>) -> Result<Node, String> {
    match node {
        Node::StructOffset { .. } | Node::Sizeof { .. } | Node::ConstExpr { .. } => {
            let key = offset_key(node);
            match map.get(&key) {
                Some(v) => Ok(Node::Immediate {
                    origin: node.origin_cloned(),
                    value: *v as i128,
                }),
                None => Err(format!(
                    "Could not find {} in offsets map at {}",
                    node.dump(),
                    node.origin_string()
                )),
            }
        }
        _ => map_children(node, &mut |c| resolve_offsets(c, map)),
    }
}
fn symbolic_operand(node: &Node) -> Option<String> {
    match node {
        Node::RustConst { expr, .. } => Some(quote::quote!(#expr).to_string()),
        Node::Immediate { value, .. } => Some(value.to_string()),
        _ => None,
    }
}

/// Builds the `Node::RustConst` for a folded symbolic expression. The ident
/// is derived from the expression text so identical sub-expressions share one
/// `global_asm!` const argument.
///
/// `expr` is built by this module purely from immediate values and other
/// `RustConst` expressions rendered back to text (see `symbolic_operand`),
/// so it is always syntactically valid Rust; the `Verbatim` fallback below
/// only guards against that invariant somehow not holding, rather than
/// being an expected path.
fn symbolic_fold(origin: &crate::code_origin::CodeOrigin, expr: String) -> Node {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in expr.as_bytes() {
        hash ^= *byte as u64;
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    let parsed = syn::parse_str::<syn::Expr>(&expr)
        .unwrap_or_else(|_| syn::Expr::Verbatim(expr.parse().unwrap_or_default()));
    Node::RustConst {
        origin: origin.clone(),
        ident: format!("OFFLINE_ASM_EXPR_{:016x}", hash),
        expr: parsed,
    }
}

/// Folds constant sub-expressions in `node` with wrapping arithmetic.
///
/// Label-relative additions fold into the reference offset. Symbolic operands
/// fold into shared `Node::RustConst` nodes.
pub fn fold(node: &Node) -> Node {
    match node {
        Node::Add {
            origin,
            left,
            right,
        } => {
            let l = fold(left);
            let r = fold(right);
            match (&l, &r) {
                (Node::Immediate { value: lv, .. }, Node::LabelReference { .. }) => {
                    return r.plus_offset(*lv).unwrap_or_else(|| node.clone())
                }
                (Node::LabelReference { .. }, Node::Immediate { value: rv, .. }) => {
                    return l.plus_offset(*rv).unwrap_or_else(|| node.clone())
                }
                _ => {}
            }
            match (l.immediate_value(), r.immediate_value()) {
                (Some(a), Some(b)) => Node::Immediate {
                    origin: origin.clone(),
                    value: a.wrapping_add(b),
                },
                _ => match (symbolic_operand(&l), symbolic_operand(&r)) {
                    (Some(a), Some(b)) => symbolic_fold(origin, format!("({} + {})", a, b)),
                    _ => Node::Add {
                        origin: origin.clone(),
                        left: Box::new(l),
                        right: Box::new(r),
                    },
                },
            }
        }
        Node::Sub {
            origin,
            left,
            right,
        } => {
            let l = fold(left);
            let r = fold(right);
            if let (Node::LabelReference { .. }, Some(b)) = (&l, r.immediate_value()) {
                return l.plus_offset(-b).unwrap_or_else(|| node.clone());
            }
            match (l.immediate_value(), r.immediate_value()) {
                (Some(a), Some(b)) => Node::Immediate {
                    origin: origin.clone(),
                    value: a.wrapping_sub(b),
                },
                _ => match (symbolic_operand(&l), symbolic_operand(&r)) {
                    (Some(a), Some(b)) => symbolic_fold(origin, format!("({} - {})", a, b)),
                    _ => Node::Sub {
                        origin: origin.clone(),
                        left: Box::new(l),
                        right: Box::new(r),
                    },
                },
            }
        }
        Node::Mul {
            origin,
            left,
            right,
        } => {
            let (l, r) = (fold(left), fold(right));
            match (l.immediate_value(), r.immediate_value()) {
                (Some(a), Some(b)) => Node::Immediate {
                    origin: origin.clone(),
                    value: a.wrapping_mul(b),
                },
                _ => match (symbolic_operand(&l), symbolic_operand(&r)) {
                    (Some(a), Some(b)) => symbolic_fold(origin, format!("({} * {})", a, b)),
                    _ => Node::Mul {
                        origin: origin.clone(),
                        left: Box::new(l),
                        right: Box::new(r),
                    },
                },
            }
        }
        Node::Neg { origin, child } => {
            let c = fold(child);
            match c.immediate_value() {
                Some(v) => Node::Immediate {
                    origin: origin.clone(),
                    value: v.wrapping_neg(),
                },
                None => match symbolic_operand(&c) {
                    Some(v) => symbolic_fold(origin, format!("-({})", v)),
                    None => Node::Neg {
                        origin: origin.clone(),
                        child: Box::new(c),
                    },
                },
            }
        }
        Node::Or {
            origin,
            left,
            right,
        } => {
            let (l, r) = (fold(left), fold(right));
            match (l.immediate_value(), r.immediate_value()) {
                (Some(a), Some(b)) => Node::Immediate {
                    origin: origin.clone(),
                    value: a | b,
                },
                _ => match (symbolic_operand(&l), symbolic_operand(&r)) {
                    (Some(a), Some(b)) => symbolic_fold(origin, format!("({} | {})", a, b)),
                    _ => Node::Or {
                        origin: origin.clone(),
                        left: Box::new(l),
                        right: Box::new(r),
                    },
                },
            }
        }
        Node::And {
            origin,
            left,
            right,
        } => {
            let (l, r) = (fold(left), fold(right));
            match (l.immediate_value(), r.immediate_value()) {
                (Some(a), Some(b)) => Node::Immediate {
                    origin: origin.clone(),
                    value: a & b,
                },
                _ => match (symbolic_operand(&l), symbolic_operand(&r)) {
                    (Some(a), Some(b)) => symbolic_fold(origin, format!("({} & {})", a, b)),
                    _ => Node::And {
                        origin: origin.clone(),
                        left: Box::new(l),
                        right: Box::new(r),
                    },
                },
            }
        }
        Node::Xor {
            origin,
            left,
            right,
        } => {
            let (l, r) = (fold(left), fold(right));
            match (l.immediate_value(), r.immediate_value()) {
                (Some(a), Some(b)) => Node::Immediate {
                    origin: origin.clone(),
                    value: a ^ b,
                },
                _ => match (symbolic_operand(&l), symbolic_operand(&r)) {
                    (Some(a), Some(b)) => symbolic_fold(origin, format!("({} ^ {})", a, b)),
                    _ => Node::Xor {
                        origin: origin.clone(),
                        left: Box::new(l),
                        right: Box::new(r),
                    },
                },
            }
        }
        Node::Bitnot { origin, child } => {
            let c = fold(child);
            match c.immediate_value() {
                Some(v) => Node::Immediate {
                    origin: origin.clone(),
                    value: !v,
                },
                None => match symbolic_operand(&c) {
                    Some(v) => symbolic_fold(origin, format!("!({})", v)),
                    None => Node::Bitnot {
                        origin: origin.clone(),
                        child: Box::new(c),
                    },
                },
            }
        }
        _ => map_children(node, &mut |c| Ok(fold(c))).unwrap_or_else(|_| node.clone()),
    }
}

/// Runs [`demacroify`], then [`resolve_offsets`], then constant-folds the
/// result.
///
/// # Errors
///
/// Returns an error for any reason [`demacroify`] or [`resolve_offsets`] can.
pub fn resolve(node: &Node, map: &HashMap<String, i64>) -> Result<Node, String> {
    let demacroed = demacroify(node)?;
    let resolved = resolve_offsets(&demacroed, map)?;
    Ok(fold(&resolved))
}

/// Checks that expansion and offset stages already ran over `node`.
///
/// Rejects any surviving macro, offset, or settings node.
///
/// # Errors
///
/// Returns an error naming the first node an earlier stage should have
/// eliminated.
pub fn validate(node: &Node) -> Result<(), String> {
    match node {
        Node::Sequence { list, .. } => {
            for item in list {
                validate(item)?;
                match item {
                    Node::Instruction { .. }
                    | Node::Label { .. }
                    | Node::LocalLabel { .. }
                    | Node::Skip { .. } => {}
                    other => {
                        return Err(format!(
                            "Unexpected {} at {}",
                            other.dump(),
                            other.origin_string()
                        ))
                    }
                }
            }
            Ok(())
        }
        Node::Immediate { .. }
        | Node::StringLiteral { .. }
        | Node::Register { .. }
        | Node::FpRegister { .. }
        | Node::VecRegister { .. }
        | Node::SpecialRegister { .. }
        | Node::Error { .. }
        | Node::LabelReference { .. }
        | Node::LocalLabelReference { .. }
        | Node::Skip { .. }
        | Node::Label { .. }
        | Node::LocalLabel { .. }
        | Node::RustConst { .. } => {
            if let Node::Label { name, .. } = node {
                if name.contains('%') {
                    return Err(format!(
                        "Unresolved substitution in Label {} at {}",
                        name,
                        node.origin_string()
                    ));
                }
            }
            Ok(())
        }
        Node::Address { base, offset, .. } => {
            validate(base)?;
            validate(offset)?;
            Ok(())
        }
        Node::BaseIndex {
            base,
            index,
            scale,
            offset,
            ..
        } => {
            validate(base)?;
            validate(index)?;
            validate(scale)?;
            validate(offset)?;
            Ok(())
        }
        Node::AbsoluteAddress { address, .. } => validate(address),
        Node::Instruction { operands, .. } => {
            for op in operands {
                validate(op)?;
            }
            Ok(())
        }
        Node::Sub { left, right, .. } => {
            if !left.is_immediate_operand() {
                return Err(format!(
                    "Invalid operand {} to immediate subtraction",
                    left.dump()
                ));
            }
            if !right.is_immediate_operand() {
                return Err(format!(
                    "Invalid operand {} to immediate subtraction",
                    right.dump()
                ));
            }
            Ok(())
        }
        Node::Variable { name, .. } if is_bare_arg_name(name) => Err(format!(
            "{name} is not a register; offlineasm has no built-in argument-register \
             aliases, declare it yourself, e.g. `const {name} = t6`"
        )),
        other => Err(format!(
            "Unresolved '{}' at {}",
            other.dump(),
            other.origin_string()
        )),
    }
}

/// Whether `name` is exactly `arg0`-`arg7`: the removed non-upstream ABI
/// aliases, called out with a specific hint instead of the generic
/// "Unresolved" error an arbitrary unbound variable gets.
fn is_bare_arg_name(name: &str) -> bool {
    matches!(
        name,
        "arg0" | "arg1" | "arg2" | "arg3" | "arg4" | "arg5" | "arg6" | "arg7"
    )
}
