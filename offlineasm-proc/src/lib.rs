#![allow(dead_code, unused_mut, unused_variables)]
use std::{collections::HashMap, str::FromStr, sync::LazyLock};

use asm::Assembler;
use ast::Node;
use parking_lot::Mutex;
use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::{braced, parse::Parse, punctuated::Punctuated, Ident, LitBool, Meta, Token};

mod risc;
mod asm;
mod ast;
mod doc;
mod instructions;
mod parser;
mod registers;
mod transforms;
mod x86;
mod opt;

struct ParseAsm {
    cond_constants: HashMap<Ident, bool>,
    toplevel: Node,
}

impl Parse for ParseAsm {
    fn parse(mut input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut conds = HashMap::new();
        let content;
        let _ = braced!(content in input);
        loop {
            if content.is_empty() {
                break;
            }

            let name = content.parse::<Ident>()?;
            let _ = content.parse::<Token![=]>()?;
            let value = content.parse::<LitBool>()?;
            content.parse::<Token![;]>()?;
            conds.insert(name, value.value);
        }

        *AUTO_CFG_STORAGE.lock() = conds
            .iter()
            .map(|(name, value)| (name.to_string(), *value))
            .collect();

        let mut parser = parser::AsmParser { settings: &conds };
        let mut node = parser.parse_sequence_inner(&mut input)?;
        node = node.resolve_settings(&conds);
        Ok(ParseAsm {
            cond_constants: HashMap::new(),
            toplevel: node,
        })
    }
}

#[proc_macro]
pub fn offlineasm_expand(input: TokenStream) -> TokenStream {
    let node = match syn::parse::<ParseAsm>(input) {
        Ok(node) => node,
        Err(e) => {
            return e.to_compile_error().into();
        }
    };

    let node = node
        .toplevel
        .demacroify(&mut HashMap::new(), &mut Vec::new())
        .rename_labels();
    let mut asm = Assembler::new();

    match node
        .resolve_constants(&mut asm)
        .documented(&mut asm)
        .lower(&mut asm)
    {
        Ok(_) => (),
        Err(e) => return e.to_compile_error().into(),
    }

    asm.compile().into()
}

struct CollectCfgs {
    cfgs: Vec<(Ident, Meta)>,
    rest: TokenStream,
}

static AUTO_CFG: &[(&str, &str)] = &[
    ("x86", "target_arch=\"x86\""),
    ("x86_64", "target_arch=\"x86_64\""),
    ("aarch64", "target_arch=\"aarch64\""),
    ("arm", "target_arch=\"arm\""),
    ("mips64", "target_arch=\"mips64\""),
    ("riscv64", "target_arch=\"riscv64\""),
    ("windows", "target_os=\"windows\""),
    ("linux", "target_os=\"linux\""),
    ("macos", "target_os=\"macos\""),
    ("ios", "target_os=\"ios\""),
    ("android", "target_os=\"android\""),
    ("freebsd", "target_os=\"freebsd\""),
    ("openbsd", "target_os=\"openbsd\""),
    ("netbsd", "target_os=\"netbsd\""),
    ("dragonfly", "target_os=\"dragonfly\""),
    ("haiku", "target_os=\"haiku\""),
    ("solaris", "target_os=\"solaris\""),
    ("illumos", "target_os=\"illumos\""),
    ("unix", "unix"),
];

static AUTO_CFG_STORAGE: LazyLock<Mutex<HashMap<String, bool>>> = LazyLock::new(|| {
    Mutex::new(
        AUTO_CFG
            .iter()
            .map(|(name, _cfg)| (name.to_string(), false))
            .collect(),
    )
});

pub(crate) fn get_auto_cfg(name: &str) -> bool {
    AUTO_CFG_STORAGE.lock().get(name).copied().unwrap_or(false)
}

pub(crate) fn auto_cfg_str() -> Vec<(String, String)> {
    AUTO_CFG_STORAGE
        .lock()
        .iter()
        .map(|(name, cfg)| (name.to_string(), cfg.to_string()))
        .collect()
}

pub(crate) fn is_windows() -> bool {
    get_auto_cfg("windows")
}

pub(crate) fn is_linux() -> bool {
    get_auto_cfg("linux")
}

pub(crate) fn is_macos() -> bool {
    get_auto_cfg("macos")
}

pub(crate) fn is_ios() -> bool {
    get_auto_cfg("ios")
}

pub(crate) fn is_android() -> bool {
    get_auto_cfg("android")
}

pub(crate) fn is_unix() -> bool {
    get_auto_cfg("unix")
}

pub(crate) fn is_bsd() -> bool {
    get_auto_cfg("bsd")
}

pub(crate) fn is_x86() -> bool {
    get_auto_cfg("x86")
}

pub(crate) fn is_x86_64() -> bool {
    get_auto_cfg("x86_64")
}

pub(crate) fn is_aarch64() -> bool {
    get_auto_cfg("aarch64")
}

pub(crate) fn is_arm() -> bool {
    get_auto_cfg("arm")
}

pub(crate) fn is_mips64() -> bool {
    get_auto_cfg("mips64")
}

pub(crate) fn is_riscv64() -> bool {
    get_auto_cfg("riscv64")
}

impl Parse for CollectCfgs {
    fn parse(mut input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut cfgs = Vec::new();
        if input.peek(syn::token::Brace) {
            let content;
            let braced = braced!(content in input);
            loop {
                if content.is_empty() {
                    break;
                }

                let name = content.parse::<Ident>().unwrap();
                let _ = content.parse::<Token![=]>();
                let value = content.parse::<Meta>()?;
                content.parse::<Token![;]>()?;

                cfgs.push((name, value));
            }
        }
        for (name, cfg) in AUTO_CFG.iter() {
            if !cfgs.iter().any(|(n, _)| n == name) {
                let ident = Ident::new(name, Span::call_site());
                let cfg = TokenStream::from_str(cfg).map_err(|e| {
                    syn::Error::new(
                        Span::call_site(),
                        format!("failed to parse auto-cfg: {}", e),
                    )
                })?;
                cfgs.push((ident, syn::parse::<Meta>(cfg)?));
            } else {
                return Err(syn::Error::new(
                    Span::call_site(),
                    format!("attempt to override auto-cfg {}", name),
                ));
            }
        }

        cfgs.sort_by(|a, b| a.0.cmp(&b.0));
        let rest = input.parse::<proc_macro2::TokenStream>()?;
        Ok(CollectCfgs {
            cfgs,
            rest: rest.into(),
        })
    }
}

/// Collect all the Cfgs in the input which is valid OfflineASM syntax.
///
/// Generates an induction chain of `macro_rules` to serially
/// evaluate them and produce a list of `true` or `false` as a tuple.
#[proc_macro]
pub fn offlineasm_internal(input: TokenStream) -> TokenStream {
    let CollectCfgs { cfgs, rest } = match syn::parse::<CollectCfgs>(input) {
        Ok(cfgs) => cfgs,
        Err(e) => return e.to_compile_error().into(),
    };

    let rest: proc_macro2::TokenStream = rest.into();

    let mut output = proc_macro2::TokenStream::new();

    for (i, (name, cfg)) in cfgs.iter().enumerate() {
        let check_name = Ident::new(&format!("__offlineasm_check_{}", name), Span::call_site());
        let macro_to_call = if i == cfgs.len() - 1 {
            Ident::new("offlineasm_expand", Span::mixed_site())
        } else {
            Ident::new(
                &format!("__offlineasm_check_{}", cfgs[i + 1].0),
                Span::call_site(),
            )
        };

        output.extend(quote::quote! {
            #[cfg(#cfg)]
            #[doc(hidden)]
            macro_rules! #check_name {
                ({$($n: ident = $v: expr;)*} $($args:tt)*) => {
                    #macro_to_call! {{ $($n = $v;)* #name = true; } $($args)* }
                }
            }

            #[cfg(not(#cfg))]
            #[doc(hidden)]
            macro_rules! #check_name {
                ({$($n: ident = $v: expr;)*} $($args:tt)*) => {
                    #macro_to_call! {{ $($n = $v;)* #name = false; } $($args)* }
                }
            }
        });
    }
    let first = match cfgs.first() {
        Some((name, _cfg)) => {
            let macro_name = Ident::new(&format!("__offlineasm_check_{}", name), Span::call_site());
            quote::quote! {
                #macro_name! { {} #rest }
            }
        }

        None => quote::quote! {
            $crate::offlineasm_expand! { {} #rest }
        },
    };

    output.extend(first);
    output.into()
}

pub(crate) fn id(name: impl AsRef<str>) -> Ident {
    Ident::new(name.as_ref(), Span::call_site())
}

pub(crate) fn punc_from_vec<T, P: Default>(vec: Vec<T>) -> Punctuated<T, P> {
    let mut punc = Punctuated::new();
    for x in vec {
        punc.push(x);
    }
    punc
}
