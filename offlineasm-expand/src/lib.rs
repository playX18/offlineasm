use offlineasm_ast::{stmt::Toplevel, target::Assembler, transforms::prepass};
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use std::collections::HashMap;
use syn::Ident;
#[proc_macro]
pub fn offlineasm_inner(input: TokenStream) -> TokenStream {
    let toplevel = match syn::parse::<Toplevel>(input) {
        Ok(toplevel) => toplevel,
        Err(e) => {
            return e.to_compile_error().into();
        }
    };

    if !toplevel.settings.is_empty() {
        return syn::Error::new(Span::call_site(), "unresolved settings in toplevel")
            .to_compile_error()
            .into();
    }

    let sequence = match prepass(&toplevel) {
        Ok(toplevel) => toplevel,
        Err(e) => {
            return e.to_compile_error().into();
        }
    };

    for (setting, val) in toplevel.resolved_settings.iter() {
        offlineasm_ast::target::set_setting(&setting.to_string(), *val);
    }

    let mut asm = Assembler::new();

    match sequence.collect_constants(&mut asm).lower(&mut asm) {
        Ok(()) => (),
        Err(e) => {
            return e.to_compile_error().into();
        }
    }

    println!("{}", asm.assembler_output);

    asm.compile().into()
}

struct ParseSettings {
    resolved_settings: HashMap<Ident, bool>,
    settings: HashMap<Ident, syn::Meta>,
    rest: TokenStream,
}

impl syn::parse::Parse for ParseSettings {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut resolved_settings = HashMap::new();
        let mut settings = HashMap::new();

        if input.peek(offlineasm_ast::parser::kw::settings) {
            let _ = input.parse::<offlineasm_ast::parser::kw::settings>()?;
            let content;
            let _ = syn::braced!(content in input);
            let input = &content;
            while !input.is_empty() {
                let name = input.parse::<Ident>()?;
                let _ = input.parse::<syn::Token![=]>()?;
                if input.peek(syn::LitBool) {
                    let value = input.parse::<syn::LitBool>()?;
                    resolved_settings.insert(name, value.value);
                } else {
                    let value = input.parse::<syn::Meta>()?;
                    settings.insert(name, value);
                }
            }
        }

        Ok(Self {
            resolved_settings,
            settings,
            rest: input.parse::<proc_macro2::TokenStream>()?.into(),
        })
    }
}

#[proc_macro]
pub fn offlineasm(input: TokenStream) -> TokenStream {
    let ParseSettings {
        resolved_settings,
        settings,
        rest,
    } = match syn::parse::<ParseSettings>(input) {
        Ok(settings) => settings,
        Err(e) => {
            return e.to_compile_error().into();
        }
    };

    let mut settings = settings.iter().collect::<Vec<_>>();
    settings.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));

    let mut output = proc_macro2::TokenStream::new();

    for (i, (name, value)) in settings.iter().enumerate() {
        let check_name = Ident::new(&format!("__offlineasm_check_{}", name), Span::call_site());
        let macro_to_call = if i == settings.len() - 1 {
            Ident::new("offlineasm_inner", Span::call_site())
        } else {
            Ident::new(
                &format!("__offlineasm_check_{}", settings[i + 1].0),
                Span::call_site(),
            )
        };

        output.extend(quote! {
            #[cfg(#value)]
            #[doc(hidden)]
            macro_rules! #check_name {
                (settings { $($n: ident = $v: literal)* } $($args:tt)* ) => {
                    #macro_to_call!(
                        settings {
                            $($n = $v)*
                            #name = true
                        }
                        $($args)*
                    );
                };
            }


            #[cfg(not(#value))]
            #[doc(hidden)]
            macro_rules! #check_name {
                (settings { $($n: ident = $v: literal)* } $($args:tt)* ) => {
                    #macro_to_call!(
                        settings {
                            $($n = $v)*
                            #name = false
                        }
                        $($args)*
                    );
                };
            }
        });
    }
    let rest: proc_macro2::TokenStream = rest.into();
    let first = settings.first();

    let mut resolved = proc_macro2::TokenStream::new();

    for (name, value) in resolved_settings {
        resolved.extend(quote! {
            #name = #value
        });
    }

    match first {
        Some((name, _)) => {
            let macro_name = Ident::new(&format!("__offlineasm_check_{}", name), Span::call_site());
            output.extend(quote! {
                #macro_name!(settings { #resolved} #rest);
            });
        }

        _ => output.extend(quote! {
            offlineasm_inner!(settings {} #rest);
        }),
    }

    output.into()
}
