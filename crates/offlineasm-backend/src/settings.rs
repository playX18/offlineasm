//! Enumerates and resolves offlineasm setting combinations.
//!
//! [`compute_settings_combinations`] lists every backend crossed with every
//! non-backend setting the source uses. [`for_settings`] resolves one
//! combination against the tree.

use crate::ast::Node;
use crate::backends::{is_backend, is_valid_backend, BACKENDS};
use crate::transform::resolve_settings;
use std::collections::HashMap;

/// Maps every setting to its concrete `true` or `false` value.
pub type SettingsMap = HashMap<String, bool>;

/// Lists the non-backend settings `ast` mentions, in first-use order.
pub fn non_backend_settings(ast: &Node) -> Vec<String> {
    let mut seen = Vec::new();
    collect_settings(ast, &mut seen);
    seen.into_iter().filter(|s| !is_backend(s)).collect()
}

fn collect_settings(node: &Node, out: &mut Vec<String>) {
    if let Node::Setting { name, .. } = node {
        if !out.contains(name) {
            out.push(name.clone());
        }
    }
    for child in node.children() {
        collect_settings(child, out);
    }
}

/// Lists every backend crossed with every true/false assignment of the
/// non-backend settings.
pub fn compute_settings_combinations(ast: &Node) -> Vec<SettingsMap> {
    let non_backend = non_backend_settings(ast);
    let mut out = Vec::new();
    for backend in BACKENDS {
        let mut base: SettingsMap = HashMap::new();
        for b in BACKENDS {
            base.insert(b.to_string(), *b == *backend);
        }
        combinator(&mut out, base, &non_backend);
    }
    out
}

fn combinator(out: &mut Vec<SettingsMap>, so_far: SettingsMap, remaining: &[String]) {
    if remaining.is_empty() {
        out.push(so_far);
        return;
    }
    let mut with_true = so_far.clone();
    with_true.insert(remaining[0].clone(), true);
    combinator(out, with_true, &remaining[1..]);
    let mut with_false = so_far;
    with_false.insert(remaining[0].clone(), false);
    combinator(out, with_false, &remaining[1..]);
}

/// Holds one resolved settings combination.
#[derive(Clone, Debug)]
pub struct ResolvedConfig {
    /// Holds the combination that produced this config.
    pub settings: SettingsMap,
    /// Holds the tree with settings resolved.
    pub low_level_ast: Node,
    /// Names the selected backend.
    pub backend: String,
}

/// Resolves `ast` under one concrete `settings` assignment.
///
/// Returns `None` when `settings` selects no backend or an unsupported one.
/// Not every enumerated combination is meant to compile.
///
/// # Errors
///
/// - Returns an error if `settings` selects more than one backend.
/// - Returns an error if settings resolution against `ast` fails.
pub fn for_settings(settings: &SettingsMap, ast: &Node) -> Result<Option<ResolvedConfig>, String> {
    let mut selected: Option<String> = None;
    for backend in BACKENDS {
        if settings.get(*backend) == Some(&true) {
            if selected.is_some() {
                return Err("multiple backends selected".to_string());
            }
            selected = Some(backend.to_string());
        }
    }
    let backend = match selected {
        Some(b) => b,
        None => return Ok(None),
    };
    if !is_valid_backend(&backend) {
        return Ok(None);
    }
    let low_level_ast = resolve_settings(ast, settings)?;
    Ok(Some(ResolvedConfig {
        settings: settings.clone(),
        low_level_ast,
        backend,
    }))
}

/// Resolves `ast` under each valid combination, calling `f` per combination.
///
/// Uses `combinations` when given, else [`compute_settings_combinations`].
/// `f` receives the settings, the resolved tree, the backend name, and the
/// combination index.
///
/// # Errors
///
/// Returns an error if [`for_settings`] fails for a combination.
pub fn for_each_valid_settings_combination(
    ast: &Node,
    combinations: Option<&[SettingsMap]>,
    mut f: impl FnMut(&SettingsMap, &Node, &str, usize),
) -> Result<(), String> {
    let owned;
    let combos: &[SettingsMap] = match combinations {
        Some(c) => c,
        None => {
            owned = compute_settings_combinations(ast);
            // Borrow dance: call with owned value via recursion-free loop.
            for (index, settings) in owned.iter().enumerate() {
                if let Some(resolved) = for_settings(settings, ast)? {
                    f(
                        &resolved.settings,
                        &resolved.low_level_ast,
                        &resolved.backend,
                        index,
                    );
                }
            }
            return Ok(());
        }
    };
    for (index, settings) in combos.iter().enumerate() {
        if let Some(resolved) = for_settings(settings, ast)? {
            f(
                &resolved.settings,
                &resolved.low_level_ast,
                &resolved.backend,
                index,
            );
        }
    }
    Ok(())
}

/// Renders `settings` as a C preprocessor `#if` test.
pub fn cpp_settings_test(settings: &SettingsMap) -> String {
    let mut pairs: Vec<(&String, &bool)> = settings.iter().collect();
    pairs.sort_by(|a, b| a.0.cmp(b.0));
    let parts: Vec<String> = pairs
        .iter()
        .map(|(k, v)| {
            if **v {
                format!("OFFLINE_ASM_{}", k)
            } else {
                format!("!OFFLINE_ASM_{}", k)
            }
        })
        .collect();
    format!("#if {}", parts.join(" && "))
}

/// Renders `settings` as a Rust `cfg` predicate.
///
/// Terms follow `non_backend_order` after the backend terms.
pub fn rust_cfg_predicate(settings: &SettingsMap, non_backend_order: &[String]) -> String {
    let mut terms: Vec<String> = Vec::new();
    for backend in BACKENDS {
        if let Some(v) = settings.get(*backend) {
            terms.push(cfg_term(backend, *v));
        }
    }
    for name in non_backend_order {
        if is_backend(name) {
            continue;
        }
        if let Some(v) = settings.get(name) {
            terms.push(cfg_term(name, *v));
        }
    }
    format!("all({})", terms.join(", "))
}

fn cfg_term(name: &str, value: bool) -> String {
    let ident = format!("offline_asm_{}", name.to_lowercase());
    if value {
        ident
    } else {
        format!("not({})", ident)
    }
}

/// Reports whether `ast` holds a `Node::Error` after macro expansion.
///
/// # Errors
///
/// Returns an error if macro expansion fails.
pub fn is_ast_erroneous(ast: &Node) -> Result<bool, String> {
    let demacroed = crate::transform::demacroify(ast)?;
    Ok(contains_error(&demacroed))
}

fn contains_error(node: &Node) -> bool {
    if matches!(node, Node::Error { .. }) {
        return true;
    }
    node.children().iter().any(|c| contains_error(c))
}
