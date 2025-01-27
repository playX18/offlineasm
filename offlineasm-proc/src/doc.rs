//! Transforms that produce documentation for the generated code.

use std::sync::atomic::AtomicUsize;

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{parse_quote, spanned::Spanned, Ident, LitStr};

use crate::{
    asm::Assembler,
    ast::{Instruction, LabelMapping, Node},
};

static INSTRUCTION_INDEX: AtomicUsize = AtomicUsize::new(0);
static LABEL_INDEX: AtomicUsize = AtomicUsize::new(0);
static MACRO_INDEX: AtomicUsize = AtomicUsize::new(0);
static CONST_INDEX: AtomicUsize = AtomicUsize::new(0);

impl Node {
    pub fn documented(&self, asm: &mut Assembler) -> Node {
        match self {
            Node::Seq(seq) => Node::Seq(seq.iter().map(|node| node.documented(asm)).collect()),

            Node::Instruction(instr) => {
                let mut comments = TokenStream::new();

                if let Some(doc) = instr.documentation.as_ref() {
                    for doc in doc {
                        let lit_str = LitStr::new(&doc, Span::call_site());
                        comments.extend(quote::quote! {
                            #[doc = #lit_str]
                        });
                    }
                    /*let link = LitStr::new(&format!(
                        "\ninstruction: [{}](offlineasm::instructions::{})",
                        instr.opcode, instr.opcode
                    ), Span::call_site());

                    comments.extend(quote::quote! {
                        #[doc = #link]
                    });*/
                }

                let name = &instr.opcode;
                let index = INSTRUCTION_INDEX.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let const_name = Ident::new(&format!("INSTRUCTION_{}", index), name.span());
                let path: syn::Path = parse_quote!(offlineasm::instructions::#name);
                asm.doc.extend(quote_spanned! {Span::mixed_site() =>
                    #comments
                    pub const #const_name: #path = #path;
                });

                return Node::Instruction(Instruction {
                    span: const_name.span(),
                    opcode: Ident::new(&name.to_string(), path.span()),
                    operands: instr.operands.clone(),
                    documentation: None,
                });
            }

            Node::Label(label) => {
                let mut comments = TokenStream::new();
                if let Some(doc) = label.doc.take() {
                    for doc in doc {
                        let lit_str = LitStr::new(&doc, Span::call_site());
                        comments.extend(quote::quote! {
                            #[doc = #lit_str]
                        });
                    }
                }

                let index = LABEL_INDEX.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let const_name = Ident::new(
                    &format!("LABEL_{}_{}", label.name(), index),
                    label.name().span(),
                );
                let lit = LitStr::new(
                    &format!("global label '{}'", label.name()),
                    label.name().span(),
                );
                comments.extend(quote! {
                    #[doc = #lit]
                });
                asm.doc.extend(quote_spanned! {Span::mixed_site() =>
                    #comments
                    pub const #const_name: () = ();
                });

                self.clone()
            }

            Node::LabelReference(lref) => match &lref.label {
                LabelMapping::Global(global) => self.clone(),

                _ => self.clone(),
            },

            _ => self.clone(),
        }
    }
}
