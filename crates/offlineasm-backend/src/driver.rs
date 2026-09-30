//! Compiles parsed offlineasm into emitted output.

use crate::ast::Node;
use crate::backends::text::TextTarget;
use crate::backends::{lower_node, Backend, BackendSet, LowerCtx, WORKING_BACKENDS};
use crate::parser::{parse_data, parse_file, parse_tokens, ParseSession, ParserOptions};
use crate::settings::{
    compute_settings_combinations, for_settings, is_ast_erroneous, non_backend_settings,
    rust_cfg_predicate, SettingsMap,
};
use crate::transform::{fold, resolve_offsets, validate};
use std::collections::HashMap;
use std::path::Path;

/// Returns the text target `backend` prints for, or `None` for the interpreter.
fn text_target(backend: Backend) -> Option<TextTarget> {
    match backend {
        Backend::X86_64 => Some(TextTarget::X86_64),
        Backend::Arm64 | Backend::Arm64e => Some(TextTarget::Aarch64),
        Backend::Riscv64 => Some(TextTarget::Riscv64),
        Backend::RLoop => None,
    }
}

#[derive(Debug, Default)]
pub struct AsmEmitter {
    pub lines: Vec<String>,
    pub rust_lines: Vec<String>,
    comment: Option<String>,
    annotation: Option<String>,
    code_origin: Option<String>,
    internal_comment: Option<String>,
    pub num_local_labels: usize,
    pub num_global_labels: usize,
    pub enable_label_count_comments: bool,
    pub enable_code_origin_comments: bool,
    pub enable_instr_annotations: bool,
    pub emit_elf_debug_directives: bool,
    comment_column: usize,
    uid_counter: usize,
}

impl AsmEmitter {
    pub fn new() -> Self {
        Self {
            comment_column: 40,
            enable_code_origin_comments: true,
            ..Default::default()
        }
    }

    fn last_comment(&mut self) -> String {
        let mut result = String::new();
        if let Some(c) = self.comment.take() {
            result = c;
        }
        if self.enable_instr_annotations {
            if let Some(a) = self.annotation.take() {
                if !result.is_empty() {
                    result.push(' ');
                }
                result.push_str(&a);
            } else {
                self.annotation = None;
            }
        } else {
            self.annotation = None;
        }
        if let Some(ic) = self.internal_comment.take() {
            if !result.is_empty() {
                result.push(' ');
            }
            result.push_str(&ic);
        }
        if self.enable_code_origin_comments {
            if let Some(co) = self.code_origin.take() {
                if !result.is_empty() {
                    result.push(' ');
                }
                result.push_str(&co);
            }
        }
        self.comment = None;
        self.code_origin = None;
        if result.is_empty() {
            result
        } else {
            format!("// {}", result)
        }
    }

    fn format_dump(&self, dump: &str, comment: &str) -> String {
        if comment.is_empty() {
            dump.to_string()
        } else {
            format!("{:<width$} {}", dump, comment, width = self.comment_column)
        }
    }

    pub fn puts(&mut self, line: &str) {
        let comment = self.last_comment();
        self.lines
            .push(self.format_dump(&format!("\t{}", line), &comment));
    }

    pub fn put_str(&mut self, line: &str) {
        let _ = self.last_comment();
        self.lines.push(line.to_string());
    }

    pub fn put_rust(&mut self, line: &str) {
        let comment = self.last_comment();
        self.rust_lines
            .push(self.format_dump(&format!("    {}", line), &comment));
    }

    pub fn rust_source(&self) -> String {
        self.rust_lines.join("\n")
    }

    pub fn puts_label(
        &mut self,
        label: &str,
        is_global: bool,
        is_export: bool,
        is_aligned: bool,
        align_to: Option<String>,
    ) {
        self.num_global_labels += 1;
        if self.enable_label_count_comments {
            self.internal_comment = Some(format!("Global Label {}", self.num_global_labels));
        }
        let comment = self.last_comment();
        let mut emit = |line: String| {
            if comment.is_empty() {
                self.lines.push(line);
            } else {
                self.lines.push(format!(
                    "{:<width$} {}",
                    line,
                    comment,
                    width = self.comment_column
                ));
            }
        };
        if is_global {
            if !is_aligned {
                let _ = is_export;
                emit(format!(".globl {}", label));
                if let Some(a) = align_to {
                    emit(format!(".p2align {}", a));
                }
                emit(format!("{}:", label));
            } else if let Some(a) = align_to {
                emit(format!(".globl {}", label));
                emit(format!(".p2align {}", a));
                emit(format!("{}:", label));
            } else {
                emit(format!(".globl {}", label));
                emit(format!("{}:", label));
            }
            if is_export {
                // todo
            }
            if self.emit_elf_debug_directives {
                emit(format!(".type {}, @function", label));
                emit(format!(".size {}, . - {}", label, label));
            }
        } else {
            if let Some(a) = align_to {
                emit(format!(".p2align {}", a));
            }
            emit(format!("{}:", label));
        }
    }

    pub fn puts_local_label(&mut self, label: &str) {
        self.num_local_labels += 1;
        if self.enable_label_count_comments {
            self.internal_comment = Some(format!("Local Label {}", self.num_local_labels));
        }
        let comment = self.last_comment();
        self.lines.push(String::new());
        let line = format!("  {}:", label);
        if comment.is_empty() {
            self.lines.push(line);
        } else {
            self.lines.push(format!(
                "{:<width$} {}",
                line,
                comment,
                width = self.comment_column
            ));
        }
    }

    pub fn code_origin(&mut self, text: String) {
        self.code_origin = Some(text);
    }

    pub fn comment(&mut self, text: String) {
        self.comment = Some(text);
    }

    pub fn annotation(&mut self, text: String) {
        self.annotation = Some(text);
    }

    pub fn put_local_annotation(&mut self) {
        if self.enable_instr_annotations {
            if let Some(a) = self.annotation.take() {
                self.lines.push(format!("    // {}", a));
            }
        } else {
            self.annotation = None;
        }
    }

    pub fn put_global_annotation(&mut self) {
        if self.enable_instr_annotations {
            if let Some(a) = self.annotation.take() {
                self.lines.push(String::new());
                self.lines.push(format!("// {}", a));
            }
        } else {
            self.annotation = None;
        }
    }

    pub fn new_uid(&mut self) -> usize {
        self.uid_counter += 1;
        self.uid_counter
    }

    pub fn template(&self) -> String {
        self.lines.join("\n")
    }
}

pub const MACHO: &str = "Mach-O";

#[derive(Clone, Debug, Default)]
pub struct CompileOptions {
    pub backend: Option<Backend>,
    pub platform: Option<String>,
    pub binary_format: Option<String>,
    pub globals: Vec<String>,
    pub global_exports: Vec<String>,
    pub integer_offsets: HashMap<String, i64>,
    pub auto_rust_offsets: bool,
    pub settings_overrides: HashMap<String, bool>,
}

impl CompileOptions {
    pub fn with_auto_rust_offsets(mut self, v: bool) -> Self {
        self.auto_rust_offsets = v;
        self
    }
}

#[derive(Clone, Debug)]
pub struct CompiledAsm {
    pub template: String,
    pub const_args: Vec<(String, String)>,
    pub referenced_externs: Vec<String>,
    pub backend: Backend,
    pub rust_lines: Vec<String>,
}

/// Compiles offlineasm source text to a `global_asm!` template.
///
/// # Errors
///
/// - Returns an error if `src` fails to parse.
/// - Returns an error if `options.globals` or `options.global_exports`
///   conflict with declared labels.
/// - Returns an error if no valid settings combination selects the backend.
/// - Returns an error if lowering the resolved tree fails.
pub fn compile_str(
    src: &str,
    file_name: &str,
    options: &CompileOptions,
    parser_options: &ParserOptions,
) -> Result<CompiledAsm, String> {
    let mut session = ParseSession::new(parser_options.clone());
    let ast = parse_data(src, file_name, &mut session).map_err(|e| e.to_string())?;
    compile_ast(&ast, &mut session, options)
}

/// Compiles offlineasm source already tokenized as a
/// [`proc_macro2::TokenStream`] (the inline `offlineasm!{ ... }` macro
/// form) to a `global_asm!` template.
///
/// # Errors
///
/// Same conditions as [`compile_str`].
pub fn compile_tokens(
    tokens: proc_macro2::TokenStream,
    file_name: &str,
    options: &CompileOptions,
    parser_options: &ParserOptions,
) -> Result<CompiledAsm, String> {
    let mut session = ParseSession::new(parser_options.clone());
    let ast = parse_tokens(tokens, file_name, &mut session).map_err(|e| e.to_string())?;
    compile_ast(&ast, &mut session, options)
}

/// Compiles an offlineasm file, tracking includes relative to it.
///
/// # Errors
///
/// - Returns an error if the file or one of its `include`s cannot be read
///   or parsed.
/// - Returns an error if `options.globals` or `options.global_exports`
///   conflict with declared labels.
/// - Returns an error if no valid settings combination selects the backend.
/// - Returns an error if lowering the resolved tree fails.
pub fn compile_file(
    path: &Path,
    options: &CompileOptions,
    parser_options: &ParserOptions,
) -> Result<CompiledAsm, String> {
    let mut session = ParseSession::new(parser_options.clone());
    let ast = parse_file(path, &mut session).map_err(|e| e.to_string())?;
    compile_ast(&ast, &mut session, options)
}

fn compile_ast(
    ast: &Node,
    session: &mut ParseSession,
    options: &CompileOptions,
) -> Result<CompiledAsm, String> {
    for g in &options.globals {
        session
            .labels
            .set_as_global(g)
            .map_err(|e| format!("globals: {}", e))?;
    }
    for g in &options.global_exports {
        session
            .labels
            .set_as_global_export(g)
            .map_err(|e| format!("exports: {}", e))?;
    }
    let backend = options.backend.unwrap_or(Backend::X86_64);
    let mut combinations = compute_settings_combinations(ast);

    let undeclared: Vec<(String, bool)> = options
        .settings_overrides
        .iter()
        .filter(|(k, _)| !combinations.iter().any(|c| c.contains_key(*k)))
        .map(|(k, v)| (k.clone(), *v))
        .collect();
    if !undeclared.is_empty() {
        for combination in &mut combinations {
            for (k, v) in &undeclared {
                combination.insert(k.clone(), *v);
            }
        }
    }

    let mut chosen: Option<(SettingsMap, Node)> = None;
    for settings in &combinations {
        if settings.get(backend.name()) != Some(&true) {
            continue;
        }
        let mut ok = true;
        for (k, v) in &options.settings_overrides {
            if settings.get(k) != Some(v) {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        if let Some(resolved) = for_settings(settings, ast)? {
            // Default overrides imply all non-backend settings false.
            if options.settings_overrides.is_empty() {
                let non_backend_set = resolved
                    .settings
                    .iter()
                    .any(|(k, v)| *k != backend.name() && !crate::backends::is_backend(k) && *v);
                if non_backend_set {
                    continue;
                }
            }
            chosen = Some((resolved.settings, resolved.low_level_ast));
            break;
        }
    }
    let (chosen_settings, low_level) = chosen.ok_or_else(|| {
        format!(
            "no valid settings combination for backend {}",
            backend.name()
        )
    })?;
    compile_resolved(&low_level, backend, session, options, &chosen_settings)
}

fn compile_resolved(
    low_level: &Node,
    backend: Backend,
    session: &mut ParseSession,
    options: &CompileOptions,
    settings: &SettingsMap,
) -> Result<CompiledAsm, String> {
    let (demacroed, label_renames) = crate::transform::demacroify_recording(low_level)?;

    for (old, new) in &label_renames {
        session.labels.apply_substituted_label_flags(old, new);
    }

    let (with_offsets, mut const_args) = resolve_offsets_ergo(&demacroed, options)?;
    let folded = fold(&with_offsets);

    for (ident, expr) in collect_rust_consts(&folded) {
        if !const_args.iter().any(|(existing, _)| *existing == ident) {
            const_args.push((ident, expr));
        }
    }
    validate(&folded)?;
    let mut emitter = AsmEmitter::new();
    emitter.emit_elf_debug_directives =
        options.binary_format.as_deref() == Some("ELF") && backend != Backend::RLoop;
    if let Some(target) = text_target(backend) {
        // x86-64 output is Intel syntax (the dialect is destination-first).
        let mut prologue_ctx = LowerCtx::new(backend, &mut emitter);
        target.prologue(&mut prologue_ctx);
    }
    let label_snapshot = session.labels.clone();
    let label_flags = |name: &str| -> (bool, bool, bool, bool, Option<String>) {
        match label_snapshot.label_flags(name) {
            Some(fl) => (
                fl.global,
                fl.export,
                fl.aligned,
                fl.is_extern,
                fl.align_to.as_ref().map(|n| n.dump()),
            ),
            None => (false, false, true, true, None),
        }
    };
    let referenced;
    {
        let mut ctx = LowerCtx::new(backend, &mut emitter);
        ctx.is_win = options.platform.as_deref() == Some("Windows");
        ctx.macho = options.binary_format.as_deref() == Some(MACHO);
        ctx.set_settings(settings.clone());
        ctx.declared_externs = session.labels.declared_externs.clone();

        for (name, string) in &session.labels.local_strings {
            ctx.local_strings.insert(name.clone(), string.clone());
            ctx.known_labels.insert(name.clone());
        }
        collect_label_info(&folded, &mut ctx);
        lower_node(&folded, &mut ctx, &label_flags).map_err(|e| e.to_string())?;
        referenced = ctx.referenced_extern.clone();
    }
    Ok(CompiledAsm {
        template: emitter.template(),
        const_args,
        referenced_externs: referenced,
        backend,
        rust_lines: emitter.rust_lines.clone(),
    })
}

/// Holds one compiled settings configuration.
#[derive(Clone, Debug)]
pub struct ConfiguredAsm {
    /// Holds the `cfg` predicate selecting this configuration.
    pub cfg_predicate: String,
    /// Holds the resolved settings.
    pub settings: SettingsMap,
    /// Names the backend used.
    pub backend: Backend,
    /// Holds the compiled output.
    pub compiled: CompiledAsm,
}

/// Compiles source text once per valid settings combination.
///
/// # Errors
///
/// - Returns an error if `src` fails to parse.
/// - Returns an error if `options.globals` or `options.global_exports` name
///   a label already declared incompatibly.
/// - Returns an error if lowering a combination's resolved tree fails.
pub fn compile_all_configurations(
    src: &str,
    file_name: &str,
    options: &CompileOptions,
    parser_options: &ParserOptions,
) -> Result<Vec<ConfiguredAsm>, String> {
    let mut session = ParseSession::new(parser_options.clone());
    let ast = parse_data(src, file_name, &mut session).map_err(|e| e.to_string())?;
    compile_all_configurations_ast(&ast, &mut session, options)
}

/// Compiles already-tokenized offlineasm source (the inline
/// `offlineasm!{ ... }` macro form) once per valid settings combination.
///
/// # Errors
///
/// Same conditions as [`compile_all_configurations`].
pub fn compile_all_configurations_tokens(
    tokens: proc_macro2::TokenStream,
    file_name: &str,
    options: &CompileOptions,
    parser_options: &ParserOptions,
) -> Result<Vec<ConfiguredAsm>, String> {
    let mut session = ParseSession::new(parser_options.clone());
    let ast = parse_tokens(tokens, file_name, &mut session).map_err(|e| e.to_string())?;
    compile_all_configurations_ast(&ast, &mut session, options)
}

/// Compiles a file via [`compile_all_configurations`].
///
/// Tracks includes relative to the file.
///
/// # Errors
///
/// - Returns an error if the file or one of its `include`s cannot be read
///   or parsed.
/// - Returns an error if `options.globals` or `options.global_exports` name
///   a label already declared incompatibly.
/// - Returns an error if lowering a combination's resolved tree fails.
pub fn compile_all_configurations_file(
    path: &Path,
    options: &CompileOptions,
    parser_options: &ParserOptions,
) -> Result<Vec<ConfiguredAsm>, String> {
    let mut session = ParseSession::new(parser_options.clone());
    let ast = parse_file(path, &mut session).map_err(|e| e.to_string())?;
    compile_all_configurations_ast(&ast, &mut session, options)
}

fn compile_all_configurations_ast(
    ast: &Node,
    session: &mut ParseSession,
    options: &CompileOptions,
) -> Result<Vec<ConfiguredAsm>, String> {
    for g in &options.globals {
        session
            .labels
            .set_as_global(g)
            .map_err(|e| format!("globals: {}", e))?;
    }
    for g in &options.global_exports {
        session
            .labels
            .set_as_global_export(g)
            .map_err(|e| format!("exports: {}", e))?;
    }
    let non_backend_order = non_backend_settings(ast);
    let combinations = compute_settings_combinations(ast);
    let mut out = Vec::new();
    for settings in &combinations {
        let resolved = match for_settings(settings, ast)? {
            Some(r) => r,
            None => continue,
        };

        if is_ast_erroneous(&resolved.low_level_ast)? {
            eprintln!(
                "offlineasm: skipping configuration {}: invalid configuration (error node present)",
                crate::settings::cpp_settings_test(&resolved.settings)
            );
            continue;
        }

        if !WORKING_BACKENDS.contains(&resolved.backend.as_str()) {
            eprintln!(
                "offlineasm: skipping configuration {}: backend {} is not supported yet",
                crate::settings::cpp_settings_test(&resolved.settings),
                resolved.backend
            );
            continue;
        }
        let backend = Backend::parse(&resolved.backend)?;
        let cfg_predicate = rust_cfg_predicate(&resolved.settings, &non_backend_order);
        let compiled = compile_resolved(
            &resolved.low_level_ast,
            backend,
            session,
            options,
            &resolved.settings,
        )?;
        out.push(ConfiguredAsm {
            cfg_predicate,
            settings: resolved.settings,
            backend,
            compiled,
        });
    }
    Ok(out)
}

fn resolve_offsets_ergo(
    ast: &Node,
    options: &CompileOptions,
) -> Result<(Node, Vec<(String, String)>), String> {
    // Collect keys in order: sorted offsets, sizes, consts.
    let offsets = crate::offsets::offsets_list(ast);
    let sizes = crate::offsets::sizes_list(ast);
    let consts = crate::offsets::consts_list(ast);
    let mut map: HashMap<String, i64> = HashMap::new();
    let mut const_args: Vec<(String, String)> = Vec::new();
    let mut symbolic: HashMap<String, (String, String)> = HashMap::new();
    let mut counter = 0usize;

    let mut rust_expr_for = |key: &str| -> (String, String) {
        counter += 1;
        let ident = format!("OFFLINE_ASM_CONST_{}", counter);
        let expr = rust_expr_for_key(key);
        (ident, expr)
    };

    for key in offsets.iter().chain(sizes.iter()).chain(consts.iter()) {
        if let Some(v) = options.integer_offsets.get(key) {
            map.insert(key.clone(), *v);
        } else if options.auto_rust_offsets {
            let (ident, expr) = rust_expr_for(key);
            symbolic.insert(key.clone(), (ident.clone(), expr.clone()));
            const_args.push((ident, expr));
        } else {
            return Err(format!("Could not find {} in offsets map", key));
        }
    }
    if symbolic.is_empty() {
        let resolved = resolve_offsets(ast, &map)?;
        return Ok((resolved, vec![]));
    }

    let with_symbols = replace_with_symbols(ast, &symbolic)?;
    let resolved = resolve_offsets_partial(&with_symbols, &map)?;
    Ok((resolved, const_args))
}

/// Maps an offset key to its Rust const expression.
///
/// `sizeof T` becomes `size_of::<T>()`, `Struct::field` becomes
/// `offset_of!(Struct, field)`, and const forms pass their expr as is.
pub fn rust_expr_for_key(key: &str) -> String {
    if let Some(rest) = key.strip_prefix("sizeof ") {
        return format!("::core::mem::size_of::<{}>()", rest.trim());
    }
    if let Some(rest) = key
        .strip_prefix("const { ")
        .and_then(|s| s.strip_suffix(" }"))
    {
        return rest.trim().to_string();
    }
    if let Some(rest) = key
        .strip_prefix("constexpr (")
        .and_then(|s| s.strip_suffix(')'))
    {
        return rest.trim().to_string();
    }
    if let Some(pos) = key.rfind("::") {
        let (s, f) = key.split_at(pos);
        let field = &f[2..];
        return format!("::core::mem::offset_of!({}, {})", s, field);
    }
    key.to_string()
}

fn replace_with_symbols(
    ast: &Node,
    symbolic: &HashMap<String, (String, String)>,
) -> Result<Node, String> {
    match ast {
        Node::StructOffset { .. } | Node::Sizeof { .. } | Node::ConstExpr { .. } => {
            let key = ast.dump();
            if let Some((ident, expr)) = symbolic.get(&key) {
                let expr = syn::parse_str::<syn::Expr>(expr).map_err(|e| e.to_string())?;
                Ok(Node::RustConst {
                    origin: ast
                        .origin()
                        .cloned()
                        .unwrap_or_else(crate::ast::builtin_origin),
                    ident: ident.clone(),
                    expr,
                })
            } else {
                Ok(ast.clone())
            }
        }
        _ => {
            let res: Result<Node, String> = (|| match ast {
                Node::Add {
                    origin,
                    left,
                    right,
                } => Ok(Node::Add {
                    origin: origin.clone(),
                    left: Box::new(replace_with_symbols(left, symbolic)?),
                    right: Box::new(replace_with_symbols(right, symbolic)?),
                }),
                Node::Sub {
                    origin,
                    left,
                    right,
                } => Ok(Node::Sub {
                    origin: origin.clone(),
                    left: Box::new(replace_with_symbols(left, symbolic)?),
                    right: Box::new(replace_with_symbols(right, symbolic)?),
                }),
                Node::Mul {
                    origin,
                    left,
                    right,
                } => Ok(Node::Mul {
                    origin: origin.clone(),
                    left: Box::new(replace_with_symbols(left, symbolic)?),
                    right: Box::new(replace_with_symbols(right, symbolic)?),
                }),
                Node::Neg { origin, child } => Ok(Node::Neg {
                    origin: origin.clone(),
                    child: Box::new(replace_with_symbols(child, symbolic)?),
                }),
                Node::Or {
                    origin,
                    left,
                    right,
                } => Ok(Node::Or {
                    origin: origin.clone(),
                    left: Box::new(replace_with_symbols(left, symbolic)?),
                    right: Box::new(replace_with_symbols(right, symbolic)?),
                }),
                Node::And {
                    origin,
                    left,
                    right,
                } => Ok(Node::And {
                    origin: origin.clone(),
                    left: Box::new(replace_with_symbols(left, symbolic)?),
                    right: Box::new(replace_with_symbols(right, symbolic)?),
                }),
                Node::Xor {
                    origin,
                    left,
                    right,
                } => Ok(Node::Xor {
                    origin: origin.clone(),
                    left: Box::new(replace_with_symbols(left, symbolic)?),
                    right: Box::new(replace_with_symbols(right, symbolic)?),
                }),
                Node::Bitnot { origin, child } => Ok(Node::Bitnot {
                    origin: origin.clone(),
                    child: Box::new(replace_with_symbols(child, symbolic)?),
                }),
                Node::Address {
                    origin,
                    base,
                    offset,
                } => Ok(Node::Address {
                    origin: origin.clone(),
                    base: Box::new(replace_with_symbols(base, symbolic)?),
                    offset: Box::new(replace_with_symbols(offset, symbolic)?),
                }),
                Node::BaseIndex {
                    origin,
                    base,
                    index,
                    scale,
                    offset,
                } => Ok(Node::BaseIndex {
                    origin: origin.clone(),
                    base: Box::new(replace_with_symbols(base, symbolic)?),
                    index: Box::new(replace_with_symbols(index, symbolic)?),
                    scale: Box::new(replace_with_symbols(scale, symbolic)?),
                    offset: Box::new(replace_with_symbols(offset, symbolic)?),
                }),
                Node::AbsoluteAddress { origin, address } => Ok(Node::AbsoluteAddress {
                    origin: origin.clone(),
                    address: Box::new(replace_with_symbols(address, symbolic)?),
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
                        .map(|o| replace_with_symbols(o, symbolic))
                        .collect::<Result<Vec<_>, _>>()?,
                    annotation: annotation.clone(),
                }),
                Node::Sequence { origin, list } => Ok(Node::Sequence {
                    origin: origin.clone(),
                    list: list
                        .iter()
                        .map(|n| replace_with_symbols(n, symbolic))
                        .collect::<Result<Vec<_>, _>>()?,
                }),
                Node::ConstDecl {
                    origin,
                    variable,
                    value,
                } => Ok(Node::ConstDecl {
                    origin: origin.clone(),
                    variable: variable.clone(),
                    value: Box::new(replace_with_symbols(value, symbolic)?),
                }),
                _ => Ok(ast.clone()),
            })();
            res
        }
    }
}

fn resolve_offsets_partial(ast: &Node, map: &HashMap<String, i64>) -> Result<Node, String> {
    match ast {
        Node::RustConst { .. } => Ok(ast.clone()),
        Node::StructOffset { .. } | Node::Sizeof { .. } | Node::ConstExpr { .. } => {
            let key = ast.dump();
            match map.get(&key) {
                Some(v) => Ok(Node::Immediate {
                    origin: ast
                        .origin()
                        .cloned()
                        .unwrap_or_else(crate::ast::builtin_origin),
                    value: *v as i128,
                }),
                None => Err(format!("Could not find {} in offsets map", key)),
            }
        }
        Node::Add {
            origin,
            left,
            right,
        } => Ok(Node::Add {
            origin: origin.clone(),
            left: Box::new(resolve_offsets_partial(left, map)?),
            right: Box::new(resolve_offsets_partial(right, map)?),
        }),
        Node::Sub {
            origin,
            left,
            right,
        } => Ok(Node::Sub {
            origin: origin.clone(),
            left: Box::new(resolve_offsets_partial(left, map)?),
            right: Box::new(resolve_offsets_partial(right, map)?),
        }),
        Node::Mul {
            origin,
            left,
            right,
        } => Ok(Node::Mul {
            origin: origin.clone(),
            left: Box::new(resolve_offsets_partial(left, map)?),
            right: Box::new(resolve_offsets_partial(right, map)?),
        }),
        Node::Neg { origin, child } => Ok(Node::Neg {
            origin: origin.clone(),
            child: Box::new(resolve_offsets_partial(child, map)?),
        }),
        Node::Or {
            origin,
            left,
            right,
        } => Ok(Node::Or {
            origin: origin.clone(),
            left: Box::new(resolve_offsets_partial(left, map)?),
            right: Box::new(resolve_offsets_partial(right, map)?),
        }),
        Node::And {
            origin,
            left,
            right,
        } => Ok(Node::And {
            origin: origin.clone(),
            left: Box::new(resolve_offsets_partial(left, map)?),
            right: Box::new(resolve_offsets_partial(right, map)?),
        }),
        Node::Xor {
            origin,
            left,
            right,
        } => Ok(Node::Xor {
            origin: origin.clone(),
            left: Box::new(resolve_offsets_partial(left, map)?),
            right: Box::new(resolve_offsets_partial(right, map)?),
        }),
        Node::Bitnot { origin, child } => Ok(Node::Bitnot {
            origin: origin.clone(),
            child: Box::new(resolve_offsets_partial(child, map)?),
        }),
        Node::Address {
            origin,
            base,
            offset,
        } => Ok(Node::Address {
            origin: origin.clone(),
            base: Box::new(resolve_offsets_partial(base, map)?),
            offset: Box::new(resolve_offsets_partial(offset, map)?),
        }),
        Node::BaseIndex {
            origin,
            base,
            index,
            scale,
            offset,
        } => Ok(Node::BaseIndex {
            origin: origin.clone(),
            base: Box::new(resolve_offsets_partial(base, map)?),
            index: Box::new(resolve_offsets_partial(index, map)?),
            scale: Box::new(resolve_offsets_partial(scale, map)?),
            offset: Box::new(resolve_offsets_partial(offset, map)?),
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
                .map(|o| resolve_offsets_partial(o, map))
                .collect::<Result<Vec<_>, _>>()?,
            annotation: annotation.clone(),
        }),
        Node::Sequence { origin, list } => Ok(Node::Sequence {
            origin: origin.clone(),
            list: list
                .iter()
                .map(|n| resolve_offsets_partial(n, map))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        _ => Ok(ast.clone()),
    }
}

/// Registers every label `ast` defines in `ctx`.
pub fn collect_label_info(ast: &Node, ctx: &mut crate::backends::LowerCtx) {
    match ast {
        Node::Label { name, .. } => {
            ctx.known_labels.insert(name.clone());
        }
        Node::LocalLabel { name, origin } => {
            ctx.known_labels.insert(name.clone());

            ctx.local_strings
                .entry(name.clone())
                .or_insert_with(|| crate::backends::LowerCtx::local_label_string(name, origin));
        }
        _ => {}
    }
    for child in ast.children() {
        collect_label_info(child, ctx);
    }
}

fn collect_rust_consts(node: &Node) -> Vec<(String, String)> {
    let mut out = Vec::new();
    collect_rust_consts_into(node, &mut out);
    out
}

fn collect_rust_consts_into(node: &Node, out: &mut Vec<(String, String)>) {
    if let Node::RustConst { ident, expr, .. } = node {
        out.push((ident.clone(), quote::quote!(#expr).to_string()));
    }
    for child in node.children() {
        collect_rust_consts_into(child, out);
    }
}

#[allow(dead_code)]
fn backend_set() -> BackendSet {
    BackendSet::new()
}
