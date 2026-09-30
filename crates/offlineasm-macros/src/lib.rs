//! Provides the `offlineasm!` proc macros.
//!
//! Both macros accept a file path (as a string literal) or the offlineasm
//! code written inline as ordinary tokens. The inline form takes no string
//! wrapper:
//!
//! ```ignore
//! offlineasm!("asm/program.asm");
//!
//! offlineasm! {
//!     global _offlineasmTest
//!     _offlineasmTest:
//!         move t0, 42
//!         ret
//! }
//! ```
//!
//! # Choosing a configuration
//!
//! Offlineasm sources are compiled once per *settings configuration* (`#if`
//! style: which backend, whether pointers are 64-bit, ...). There are two
//! modes:
//!
//! * `settings { ... }` (recommended). Each entry maps an offlineasm setting
//!   to a Rust `cfg` predicate, which is resolved at compile time:
//!
//!   ```ignore
//!   offlineasm! {
//!       settings {
//!           X86_64 = target_arch = "x86_64",
//!           ARM64 = target_arch = "aarch64",
//!           HAS_AVX = target_feature = "avx",
//!       }
//!       global _offlineasmTest
//!       _offlineasmTest:
//!           ret
//!   }
//!   ```
//!
//!   Exactly one configuration is compiled: the one in which the listed
//!   settings hold the values their predicates resolved to, and every other
//!   offlineasm setting is false. The emitted items are not gated, so the
//!   generated symbols can be used directly.
//!
//! * Without a `settings` block, every valid, non-erroneous, working-backend
//!   settings combination is emitted, each guarded by a `#[cfg(...)]`
//!   predicate standing in for the preprocessor `#if OFFLINE_ASM_...` /
//!   `#endif` test:
//!     * non-RLoop backends emit `#[cfg(predicate)] global_asm!(TEMPLATE, ident = const EXPR, ...)`.
//!     * the RLoop (portable interpreter loop) backend emits Rust source
//!       lines rather than a `global_asm!`, so it becomes
//!       `#[cfg(predicate)] mod <unique> { ...rust lines... }`.
//!
//! `offlineasm_include!` additionally registers the file's directory (or, for
//! inline input, the invoking crate's `CARGO_MANIFEST_DIR`) as an offlineasm
//! `-I` include directory.
//!
//! Compile-time failures (parse errors, lowering errors, a configuration
//! whose generated Rust doesn't tokenize) become `compile_error!(...)` in the
//! macro's expansion rather than a proc-macro panic, so they show up as
//! ordinary, readable build errors / IDE diagnostics.

use offlineasm_backend::backends::{is_backend, Backend};
use offlineasm_backend::driver::{
    compile_all_configurations_file, compile_all_configurations_tokens, compile_file,
    compile_tokens, CompileOptions, ConfiguredAsm, MACHO,
};
use offlineasm_backend::parser::{parse_file, parse_tokens, ParseSession, ParserOptions};
use offlineasm_backend::settings::non_backend_settings;
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use syn::parse::{Parse, ParseStream};
use syn::{braced, Ident, LitBool, LitStr, Meta, Token};

static CHECK_MACRO_UID: AtomicUsize = AtomicUsize::new(0);

enum Body {
    Path(LitStr),
    Inline(TokenStream2),
}

impl Body {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(LitStr) {
            let fork = input.fork();
            let _: LitStr = fork.parse()?;
            if fork.is_empty() {
                return Ok(Body::Path(input.parse()?));
            }
        }
        Ok(Body::Inline(input.parse()?))
    }

    fn tokens(&self) -> TokenStream2 {
        match self {
            Body::Path(lit) => lit.to_token_stream(),
            Body::Inline(tokens) => tokens.clone(),
        }
    }
}

struct MacroInput {
    settings: Vec<(Ident, Meta)>,
    body: Body,
}

impl Parse for MacroInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut settings = Vec::new();
        if input.peek(Ident) {
            let fork = input.fork();
            let keyword: Ident = fork.parse()?;
            if keyword == "settings" && fork.peek(syn::token::Brace) {
                let _: Ident = input.parse()?;
                let content;
                braced!(content in input);
                while !content.is_empty() {
                    let name: Ident = content.parse()?;
                    let _: Token![=] = content.parse()?;
                    let predicate: Meta = content.parse()?;
                    settings.push((name, predicate));
                    if content.peek(Token![,]) {
                        let _: Token![,] = content.parse()?;
                    }
                }
            }
        }
        let body = Body::parse(input)?;
        Ok(MacroInput { settings, body })
    }
}
struct InnerInput {
    include_dir: bool,
    settings: Vec<(Ident, bool)>,
    body: Body,
}

impl Parse for InnerInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let flag: Ident = input.parse()?;
        let include_dir = match flag.to_string().as_str() {
            "include" => true,
            "no_include" => false,
            other => {
                return Err(syn::Error::new(
                    flag.span(),
                    format!("expected `include` or `no_include`, found `{}`", other),
                ))
            }
        };
        let keyword: Ident = input.parse()?;
        if keyword != "settings" {
            return Err(syn::Error::new(keyword.span(), "expected `settings`"));
        }
        let content;
        braced!(content in input);
        let mut settings = Vec::new();
        while !content.is_empty() {
            let name: Ident = content.parse()?;
            let _: Token![=] = content.parse()?;
            let value: LitBool = content.parse()?;
            settings.push((name, value.value));
            if content.peek(Token![,]) {
                let _: Token![,] = content.parse()?;
            }
        }
        let body = Body::parse(input)?;
        Ok(InnerInput {
            include_dir,
            settings,
            body,
        })
    }
}

/// Resolves a macro-supplied path against the invoking crate's
/// `CARGO_MANIFEST_DIR`.
///
/// Falls back to `.` when unset, as under `rustc` invoked outside cargo.
fn resolve_path(lit: &str) -> PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let mut path = PathBuf::from(manifest_dir);
    path.push(lit);
    path
}

fn compile_error(msg: impl Into<String>) -> TokenStream2 {
    let msg = msg.into();
    quote! { ::core::compile_error!(#msg); }
}

/// Expands the `backend = native | rloop` shorthand of a `settings` block.
///
/// `native` maps each architecture-specific backend to the Rust `cfg` that
/// selects it and leaves the portable backend off. `rloop` selects the
/// portable backend unconditionally. Values are `cfg` predicates, so the
/// caller can switch between the generated assembly and the portable Rust
/// interpreter loop with one setting.
fn expand_backend_shorthand(settings: Vec<(Ident, Meta)>) -> Result<Vec<(Ident, Meta)>, String> {
    let mut out: Vec<(Ident, Meta)> = Vec::new();
    let mut native = false;
    let mut rloop = false;
    for (name, predicate) in settings {
        if name == "backend" {
            match predicate {
                Meta::Path(path) => {
                    let keyword = path
                        .get_ident()
                        .map(|ident| ident.to_string())
                        .ok_or_else(|| "`backend` expects `native` or `rloop`".to_string())?;
                    match keyword.as_str() {
                        "native" | "auto" => native = true,
                        "rloop" | "portable" => rloop = true,
                        other => {
                            return Err(format!(
                                "unknown backend `{}` (expected `native` or `rloop`)",
                                other
                            ))
                        }
                    }
                }
                other => {
                    return Err(format!(
                        "`backend` expects `native` or `rloop`, found `{}`",
                        other.to_token_stream()
                    ))
                }
            }
            continue;
        }
        out.push((name, predicate));
    }
    let push = |out: &mut Vec<(Ident, Meta)>, name: &str, predicate: TokenStream2| {
        let meta: Meta = syn::parse2(quote!(#predicate)).expect("well-formed cfg predicate");
        out.push((Ident::new(name, Span::call_site()), meta));
    };
    if rloop {
        // `all()` is the always-true cfg predicate.
        push(&mut out, "RLOOP", quote!(all()));
    }
    if native {
        push(&mut out, "X86_64", quote!(target_arch = "x86_64"));
        push(&mut out, "ARM64", quote!(target_arch = "aarch64"));
        push(&mut out, "RISCV64", quote!(target_arch = "riscv64"));
    }
    if !native
        && !rloop
        && !out
            .iter()
            .any(|(name, _)| is_backend(&name.to_string().to_uppercase()))
    {
        return Err(
            "no backend selected: add `backend = native` or `backend = rloop` to the settings block"
                .to_string(),
        );
    }
    Ok(out)
}

/// Names where the offlineasm text comes from.
enum Source {
    File(PathBuf),
    Tokens {
        tokens: TokenStream2,
        file_name: String,
    },
}

struct Loaded {
    source: Source,
    parser_options: ParserOptions,
    describe: String,
}

impl Loaded {
    /// Parses this source, keeping the real `syn::Error` (and its span) a
    /// parse failure carries, so callers can render it via
    /// `syn::Error::to_compile_error()` for span-highlighted diagnostics
    /// instead of a generic call-site `compile_error!`.
    fn parse(&self) -> syn::Result<offlineasm_backend::ast::Node> {
        let mut session = ParseSession::new(self.parser_options.clone());
        match &self.source {
            Source::File(path) => parse_file(path, &mut session),
            Source::Tokens { tokens, file_name } => {
                parse_tokens(tokens.clone(), file_name, &mut session)
            }
        }
    }
}

fn inline_file_name(tokens: &TokenStream2) -> String {
    tokens
        .clone()
        .into_iter()
        .next()
        .map(|tt| tt.span().file())
        .filter(|f| !f.is_empty())
        .unwrap_or_else(|| "<inline offlineasm>".to_string())
}

fn load(body: &Body, include_dir: bool) -> Result<Loaded, String> {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    match body {
        Body::Path(lit) => {
            let path = resolve_path(&lit.value());
            let mut parser_options = ParserOptions::default();
            if include_dir {
                if let Some(parent) = path.parent() {
                    parser_options
                        .include_dirs
                        .push(parent.to_string_lossy().to_string());
                }
            }
            Ok(Loaded {
                describe: format!("`{}`", path.display()),
                source: Source::File(path),
                parser_options,
            })
        }
        Body::Inline(tokens) => {
            if tokens.is_empty() {
                return Err("inline offlineasm input is empty".to_string());
            }
            let file_name = inline_file_name(tokens);
            let mut parser_options = ParserOptions::default();
            if include_dir {
                parser_options.include_dirs.push(manifest_dir);
            }
            Ok(Loaded {
                describe: format!("inline offlineasm in {}", file_name),
                source: Source::Tokens {
                    tokens: tokens.clone(),
                    file_name,
                },
                parser_options,
            })
        }
    }
}

/// Pairs the configurations compiled for ELF and for Mach-O: each native
/// one gets both, guarded by whether the target is an Apple platform. RLoop
/// output is plain Rust, so it is kept once.
fn split_by_object_format(
    elf: Vec<ConfiguredAsm>,
    macho: Vec<ConfiguredAsm>,
) -> Vec<ConfiguredAsm> {
    let mut out = Vec::with_capacity(elf.len() * 2);
    for (mut elf, mut macho) in elf.into_iter().zip(macho) {
        if elf.backend == Backend::RLoop {
            out.push(elf);
            continue;
        }
        macho.cfg_predicate = format!("all({}, target_vendor = \"apple\")", macho.cfg_predicate);
        elf.cfg_predicate = format!("all({}, not(target_vendor = \"apple\"))", elf.cfg_predicate);
        out.push(elf);
        out.push(macho);
    }
    out
}

/// Emits every valid settings configuration, each guarded by
/// a `#[cfg(...)]` predicate.
fn expand_all(body: &Body, include_dir: bool) -> TokenStream2 {
    let loaded = match load(body, include_dir) {
        Ok(loaded) => loaded,
        Err(e) => return compile_error(format!("offlineasm!: {}", e)),
    };
    // A parse failure caught here keeps its real span, so the error
    // underlines the exact offending token in the source; `compile_all_*`
    // below would otherwise re-parse internally and only surface a
    // stringified, call-site-spanned message.
    if let Err(e) = loaded.parse() {
        return e.to_compile_error();
    }
    let compile = |binary_format: Option<String>| {
        let options = CompileOptions {
            binary_format,
            ..CompileOptions::default().with_auto_rust_offsets(true)
        };
        match &loaded.source {
            Source::File(path) => {
                compile_all_configurations_file(path, &options, &loaded.parser_options)
            }
            Source::Tokens { tokens, file_name } => compile_all_configurations_tokens(
                tokens.clone(),
                file_name,
                &options,
                &loaded.parser_options,
            ),
        }
    };
    let configured = compile(None).and_then(|elf| Ok((elf, compile(Some(MACHO.to_string()))?)));
    let configured = match configured {
        Ok((elf, macho)) => split_by_object_format(elf, macho),
        Err(e) => {
            return compile_error(format!(
                "offlineasm!: failed to compile {}: {}",
                loaded.describe, e
            ))
        }
    };
    if configured.is_empty() {
        return compile_error(format!(
            "offlineasm!: {} produced no valid (working-backend, non-erroneous) settings configuration",
            loaded.describe
        ));
    }
    emit_items(&configured, &loaded.describe, true)
}

/// The hidden setting that tells [`compile_selected`] whether the target
/// uses Mach-O.
const MACHO_SETTING: &str = "__offlineasm_macho";

/// Compiles the single configuration a `settings` block selects.
fn compile_selected(loaded: &Loaded, settings: &[(Ident, bool)]) -> Result<ConfiguredAsm, String> {
    let mut backend: Option<Backend> = None;
    let mut requested: BTreeMap<String, bool> = BTreeMap::new();
    let mut macho = false;
    for (name, value) in settings {
        if name == MACHO_SETTING {
            macho = *value;
            continue;
        }
        // all settings are uppercase by default
        let name = name.to_string().to_uppercase();
        if is_backend(&name) {
            if *value {
                let parsed = Backend::parse(&name)?;
                if let Some(existing) = backend {
                    return Err(format!(
                        "multiple backends selected ({} and {}); exactly one backend setting must resolve to true",
                        existing.name(),
                        parsed.name()
                    ));
                }
                backend = Some(parsed);
            }
        } else {
            requested.insert(name, *value);
        }
    }
    let backend = backend.ok_or_else(|| {
        "no backend setting resolved to true: add e.g. `X86_64 = target_arch = \"x86_64\"` to the settings block"
            .to_string()
    })?;

    let ast = loaded.parse().map_err(|e| e.to_string())?;
    let mut settings_overrides = std::collections::HashMap::new();
    for name in non_backend_settings(&ast) {
        let value = requested.get(&name).copied().unwrap_or(false);
        settings_overrides.insert(name, value);
    }

    let options = CompileOptions {
        backend: Some(backend),
        settings_overrides,
        binary_format: macho.then(|| MACHO.to_string()),
        ..CompileOptions::default().with_auto_rust_offsets(true)
    };
    let compiled = match &loaded.source {
        Source::File(path) => compile_file(path, &options, &loaded.parser_options),
        Source::Tokens { tokens, file_name } => {
            compile_tokens(tokens.clone(), file_name, &options, &loaded.parser_options)
        }
    }
    .map_err(|e| format!("failed to compile {}: {}", loaded.describe, e))?;

    let mut settings = std::collections::HashMap::new();
    settings.insert(backend.name().to_string(), true);
    for (name, value) in requested {
        settings.insert(name, value);
    }
    Ok(ConfiguredAsm {
        cfg_predicate: String::new(),
        settings,
        backend,
        compiled,
    })
}

/// Resolves the `settings { ... }` predicates at compile time for
/// [`offlineasm_inner!`].
///
/// A proc macro cannot evaluate `cfg(...)` predicates itself, so this emits a
/// chain of `macro_rules!` helpers, one pair per setting, each gated on the
/// predicate (or its negation), which appends `NAME = true`/`NAME = false`
/// to an accumulator and forwards the original input to the next helper. The
/// last one calls the inner proc macro with the fully resolved settings.
fn expand_settings_chain(
    settings: &[(Ident, Meta)],
    body: &Body,
    include_dir: bool,
) -> TokenStream2 {
    let mut sorted: Vec<&(Ident, Meta)> = settings.iter().collect();
    sorted.sort_by_key(|(name, _)| name.to_string());
    for pair in sorted.windows(2) {
        if pair[0].0 == pair[1].0 {
            return compile_error(format!("offlineasm!: setting `{}` listed twice", pair[0].0));
        }
    }

    let uid = CHECK_MACRO_UID.fetch_add(1, Ordering::Relaxed);
    let include_flag = if include_dir {
        quote!(include)
    } else {
        quote!(no_include)
    };
    let mut next: TokenStream2 = quote!(::offlineasm::__offlineasm_inner);

    let mut definitions = TokenStream2::new();
    for (name, predicate) in sorted.iter().rev() {
        let check = Ident::new(
            &format!("__offlineasm_check_{}_{}", uid, name),
            Span::call_site(),
        );
        let define = |value: bool, condition: TokenStream2| {
            quote! {
                #[cfg(#condition)]
                #[allow(unused_macros)]
                macro_rules! #check {
                    ( $flag:ident settings { $($acc:tt)* } $($args:tt)* ) => {
                        #next!( $flag settings { $($acc)* #name = #value } $($args)* );
                    };
                }
            }
        };
        definitions.extend(define(true, quote!(#predicate)));
        definitions.extend(define(false, quote!(not(#predicate))));
        next = quote!(#check);
    }

    let first = next;
    let body_tokens = body.tokens();
    let mut out = definitions;
    out.extend(quote! { #first!( #include_flag settings { } #body_tokens ); });

    out
}

/// Turns each lowered configuration into its items.
fn emit_items(configured: &[ConfiguredAsm], describe: &str, guarded: bool) -> TokenStream2 {
    let mut items = Vec::with_capacity(configured.len());
    for (index, cfg) in configured.iter().enumerate() {
        let predicate_tokens: TokenStream2 = if guarded {
            match syn::parse_str(&cfg.cfg_predicate) {
                Ok(t) => t,
                Err(e) => {
                    items.push(compile_error(format!(
                        "offlineasm!: internal error: bad cfg predicate `{}`: {}",
                        cfg.cfg_predicate, e
                    )));
                    continue;
                }
            }
        } else {
            TokenStream2::new()
        };
        let guard = |item: TokenStream2| {
            if guarded {
                quote! {
                    #[cfg(#predicate_tokens)]
                    #item
                }
            } else {
                item
            }
        };

        if cfg.backend == Backend::RLoop {
            let mod_ident = Ident::new(
                &format!("offlineasm_rloop_config_{}", index),
                Span::call_site(),
            );
            let rust_src = cfg.compiled.rust_lines.join("\n");
            let body: TokenStream2 = match syn::parse_str(&rust_src) {
                Ok(t) => t,
                Err(e) => {
                    items.push(compile_error(format!(
                        "offlineasm!: RLoop output for {} (config {}) failed to parse as Rust: {}",
                        describe, index, e
                    )));
                    continue;
                }
            };
            // The RLoop backend emits Rust that refers to the companion
            // runtime's `Machine` state by name, so pull in whatever the
            // caller has in scope (typically `use offlineasm::rt::*;`).
            items.push(guard(quote! {
                mod #mod_ident {
                    // The generated program is safe code over the caller's
                    // owned `Machine`: no global register file is involved.
                    #[allow(unused_imports)]
                    use super::*;
                    #body
                }
            }));
        } else {
            let template = &cfg.compiled.template;
            let mut const_arg_tokens = Vec::with_capacity(cfg.compiled.const_args.len());
            let mut bad = false;
            for (ident, expr) in &cfg.compiled.const_args {
                let ident = Ident::new(ident, Span::call_site());
                let expr_tokens: TokenStream2 = match syn::parse_str(expr) {
                    Ok(t) => t,
                    Err(e) => {
                        items.push(compile_error(format!(
                            "offlineasm!: bad const expr `{}` for {}: {}",
                            expr, describe, e
                        )));
                        bad = true;
                        break;
                    }
                };
                const_arg_tokens.push(quote! { , #ident = const #expr_tokens });
            }
            if bad {
                continue;
            }
            // Selects the initial `global_asm!` dialect on x86. The template
            // itself opens with `.intel_syntax noprefix`, which governs the
            // emitted lines.
            let options = if cfg.backend == Backend::X86_64 {
                quote! { , options(att_syntax) }
            } else {
                quote! {}
            };
            items.push(guard(quote! {
                ::std::arch::global_asm!(#template #(#const_arg_tokens)* #options);
            }));
        }
    }
    quote! { #(#items)* }
}

/// Parses macro input and dispatches to the settings or all-configurations path.
fn expand(input: TokenStream, include_dir: bool) -> TokenStream {
    let parsed = match syn::parse::<MacroInput>(input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    if parsed.settings.is_empty() {
        return expand_all(&parsed.body, include_dir).into();
    }
    let mut settings = match expand_backend_shorthand(parsed.settings) {
        Ok(settings) => settings,
        Err(e) => return compile_error(format!("offlineasm!: {}", e)).into(),
    };
    // Resolved with the user's settings, so the object format follows the
    // crate being compiled.
    settings.push((
        Ident::new(MACHO_SETTING, Span::call_site()),
        syn::parse_quote!(target_vendor = "apple"),
    ));
    expand_settings_chain(&settings, &parsed.body, include_dir).into()
}

/// Compiles offlineasm source given as a path or inline tokens.
///
/// Accepts `offlineasm!("path/to/file.asm")` or `offlineasm! { <code> }`,
/// each optionally preceded by a `settings { ... }` preamble. See the module
/// docs.
#[proc_macro]
pub fn offlineasm(input: TokenStream) -> TokenStream {
    expand(input, false)
}

/// Compiles offlineasm like [`offlineasm!`], with an include directory registered.
#[proc_macro]
pub fn offlineasm_include(input: TokenStream) -> TokenStream {
    expand(input, true)
}

#[proc_macro]
#[doc(hidden)]
pub fn offlineasm_inner(input: TokenStream) -> TokenStream {
    let parsed = match syn::parse::<InnerInput>(input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    let loaded = match load(&parsed.body, parsed.include_dir) {
        Ok(loaded) => loaded,
        Err(e) => return compile_error(e).into(),
    };

    if let Err(e) = loaded.parse() {
        return e.to_compile_error().into();
    }
    match compile_selected(&loaded, &parsed.settings) {
        Ok(configured) => emit_items(&[configured], &loaded.describe, false).into(),
        Err(e) => compile_error(e).into(),
    }
}
