use std::{borrow::Cow, sync::Arc};

use proc_macro2::{Span, TokenStream};
use syn::{Ident, LitStr};

use crate::{ast::*, auto_cfg_str, is_ios, is_macos, is_riscv64, is_x86_64};

pub struct Assembler {
    comment: String,
    num_local_labels: usize,
    num_global_labels: usize,
    deferred_next_label_actions: Vec<Box<dyn FnOnce(&mut Assembler) -> syn::Result<()>>>,
    pub output: String,
    pub rust_out: TokenStream,
    pub constants: Vec<syn::Expr>,
    pub symbols: Vec<Arc<Label>>,
    pub doc: TokenStream,
}

fn asm_text_section() -> &'static str {
    if is_macos() || is_ios() {
        return ".section __TEXT";
    } else {
        return ".text";
    }
}

fn asm_global_label_impl(
    label: &str,
    alt_entry: impl FnOnce(&str) -> Cow<'_, str>,
    alignment: &str,
    vis: impl FnOnce(&str) -> Cow<'_, str>,
) -> String {
    let mut output = String::new();
    if is_riscv64() {
        output.push_str(asm_text_section());
        output.push_str("\n");
        output.push_str(alignment);
        output.push_str(&alt_entry(label));
        output.push_str("\n");
        output.push_str(&format!(".globl {}\n", label));
        output.push_str(&vis(label));
        output.push_str("\n");
        output.push_str(&format!("{}:\n", label));
    } else {
        output.push_str(asm_text_section());
        output.push_str("\n");
        output.push_str(alignment);
        output.push_str(&alt_entry(label));
        output.push_str("\n");
        output.push_str(&format!(".globl {}\n", label));
        output.push_str(&vis(label));
        output.push_str("\n");
        output.push_str(&format!("{}:\n", label));
    }

    output
}

fn asm_global_label(label: &str) -> String {
    asm_global_label_impl(label, |_| Cow::Borrowed(""), "", |_| Cow::Borrowed(""))
}

fn asm_global_label_aligned(label: &str, align_to: usize) -> String {
    asm_global_label_impl(
        label,
        |_| Cow::Borrowed(""),
        &format!(".align {}", align_to),
        |_| Cow::Borrowed(""),
    )
}

impl Assembler {
    pub fn new() -> Self {
        Self {
            comment: String::new(),
            num_local_labels: 0,
            num_global_labels: 0,
            deferred_next_label_actions: Vec::new(),
            output: String::new(),
            rust_out: TokenStream::new(),
            constants: Vec::new(),
            symbols: Vec::new(),
            doc: TokenStream::new(),
        }
    }

    pub fn compile(mut self) -> TokenStream {
        let mut output = TokenStream::new();
        let str_out = &self.output;

        let mut constants_out = TokenStream::new();
        for (i, expr) in self.constants.iter().enumerate() {
            let name = Ident::new(&format!("_{}", i), Span::call_site());
            constants_out.extend(quote::quote! {
                #name = const { #expr },
            })
        }

        let mut sym_out = TokenStream::new();
        for (i, sym) in self.symbols.iter().enumerate() {
            let name = Ident::new(&format!("{}", &sym.name().to_string()[..]), Span::call_site());
            let sym_id = Ident::new(&format!("_sym_{}", i), Span::call_site());
            sym_out.extend(quote::quote! {
                #sym_id = sym #name,
            })
        }

        let mut lit_str = LitStr::new(&self.output, Span::call_site());

        output.extend(quote::quote! {
            const ASM: &str = #lit_str;
            ::core::arch::global_asm! {
                #lit_str,
                #constants_out
                #sym_out
                options(att_syntax)
            }
        });
        let doc = std::mem::take(&mut self.doc);
        output.extend(quote::quote! {
            #[doc(hidden)]
            pub mod _docs {
                #![allow(non_upper_case_globals)]
                #doc 
            }
        });
        output.extend(self.rust_out);
        output
    }

    pub fn puts(&mut self, line: &str) {
        self.output.push_str(line);
        self.output.push('\n');
    }

    fn add_constant(&mut self, expr: syn::Expr) -> Node {
        let x = self.constants.len();
        self.constants.push(expr);
        Node::AsmOperand(x)
    }

    fn maybe_add_sym(&mut self, label: Arc<Label>) {
        if label.is_extern() {
            let id = self.symbols.len();
            label.set_sym_id(id);
            self.symbols.push(label);
        }
    }

    pub fn puts_label(
        &mut self,
        label_name: &str,
        is_global: bool,
        is_export: bool,
        is_aligned: bool,
        align_to: usize,
    ) -> syn::Result<()> {
        for action in std::mem::take(&mut self.deferred_next_label_actions) {
            action(self)?;
        }

        self.num_global_labels += 1;

        self.puts(&asm_global_label(label_name));

        Ok(())
    }

    pub fn puts_local_label(&mut self, label_name: &str) -> syn::Result<()> {
        self.num_local_labels += 1;

        self.puts(&format!("{}:", label_name));

        Ok(())
    }
}

impl Label {
    pub fn lower(&self, asm: &mut Assembler) -> syn::Result<()> {
        asm.puts_label(
            &self.name().to_string()[..],
            self.is_global(),
            self.is_exported(),
            self.is_aligned(),
            self.aligned_to(),
        )?;
        Ok(())
    }
}

impl LocalLabel {
    pub fn clean_name(&self) -> String {
        let x = self.name.to_string();
        if x.starts_with(".") {
            return x[..].to_string();
        } else {
            x
        }
    }

    pub fn lower(&self, asm: &mut Assembler) -> syn::Result<()> {
        asm.puts_local_label(&self.name.to_string())?;
        Ok(())
    }
}

impl LocalLabelReference {
    pub fn lower(&self, asm: &mut Assembler) -> syn::Result<()> {
        asm.puts(&format!("{}", self.label.name));
        Ok(())
    }
}

impl LabelReference {
    pub fn lower(&self, asm: &mut Assembler) -> syn::Result<()> {
        asm.puts(&format!("{}", self.label.name()));
        Ok(())
    }
}

impl Node {
    pub fn lower(&self, asm: &mut Assembler) -> syn::Result<()> {
        match self {
            Self::Nop => Ok(()),
            Self::Instruction(x) => x.lower(asm),
            Self::Label(x) => x.lower(asm),
            Self::LocalLabel(x) => x.lower(asm),
            Self::LabelReference(x) => x.lower(asm),
            Self::LocalLabelReference(x) => x.lower(asm),
            Self::Seq(seq) => {
                for x in seq {
                    x.lower(asm)?;
                }
                Ok(())
            }
            Self::Export(x) => {
                let name = x.label.name();
                let abi = &x.abi;
                let item = &x.item;
                let link_name = LitStr::new(&name.to_string(), Span::call_site());
                asm.rust_out.extend(quote::quote! {
                    #[allow(non_snake_case)]
                    #[allow(non_camel_case_types)]
                    #[allow(non_upper_case_globals)]
                    #abi {
                        #[link_name=#link_name]
                        #item   
                    }
                });
                Ok(())
            }
            _ => unreachable!("lower {}", self),
        }
    }

    /// Walk all nodes and replace all constants with `{}` and append them
    /// to constant list of `global_asm`.
    pub fn resolve_constants(&self, asm: &mut Assembler) -> Node {
        match self {
            Self::AddImmediates(x) => Self::AddImmediates(AddImmediates {
                left: Box::new(x.left.resolve_constants(asm)),
                plus: x.plus,
                right: Box::new(x.right.resolve_constants(asm)),
            }),
            Self::SubImmediates(x) => Self::SubImmediates(SubImmediates {
                left: Box::new(x.left.resolve_constants(asm)),
                minus: x.minus,
                right: Box::new(x.right.resolve_constants(asm)),
            }),
            Self::MulImmediates(x) => Self::MulImmediates(MulImmediates {
                left: Box::new(x.left.resolve_constants(asm)),
                times: x.times,
                right: Box::new(x.right.resolve_constants(asm)),
            }),
            Self::AndImmediate(x) => Self::AndImmediate(AndImmediate {
                left: Box::new(x.left.resolve_constants(asm)),
                and: x.and,
                right: Box::new(x.right.resolve_constants(asm)),
            }),
            Self::OrImmediate(x) => Self::OrImmediate(OrImmediate {
                left: Box::new(x.left.resolve_constants(asm)),
                or: x.or,
                right: Box::new(x.right.resolve_constants(asm)),
            }),
            Self::BitNotImmediate(x) => Self::BitNotImmediate(BitNotImmediate {
                bitnot: x.bitnot,
                value: Box::new(x.value.resolve_constants(asm)),
            }),
            Self::Instruction(instr) => Self::Instruction(Instruction {
                opcode: instr.opcode.clone(),
                operands: instr
                    .operands
                    .iter()
                    .map(|x| x.resolve_constants(asm))
                    .collect(),
                span: instr.opcode.span(),
                documentation: instr.documentation.clone(),
            }),
            Self::Const(x) => asm.add_constant(x.expr.clone()),
            Self::Seq(seq) => Self::Seq(seq.iter().map(|x| x.resolve_constants(asm)).collect()),
            Self::AsmOperand(x) => Self::AsmOperand(*x),
            Self::Address(addr) => Self::Address(Address {
                base: Box::new(addr.base.resolve_constants(asm)),
                offset: Box::new(addr.offset.resolve_constants(asm)),
            }),

            Self::BaseIndex(x) => Self::BaseIndex(BaseIndex {
                base: Box::new(x.base.resolve_constants(asm)),
                index: Box::new(x.index.resolve_constants(asm)),
                scale: Box::new(x.scale.resolve_constants(asm)),
                offset: Box::new(x.offset.resolve_constants(asm)),
            }),

            Self::AbsoluteAddress(x) => Self::AbsoluteAddress(AbsoluteAddress {
                base: Box::new(x.base.resolve_constants(asm)),
            }),

            Self::Label(x) => {
                asm.maybe_add_sym(x.clone());
                self.clone()
            }

            Self::LabelReference(x) => {
                match &x.label {
                    LabelMapping::Global(x) => {
                        asm.maybe_add_sym(x.clone());
                    }
                    _ => (),
                }
                self.clone()
            }  

           

            _ => self.clone(),
        }
    }
}

impl Instruction {
    pub fn lower_default(&self, asm: &mut Assembler) -> syn::Result<()> {
        Ok(())
    }

    pub fn lower(&self, asm: &mut Assembler) -> syn::Result<()> {
        if is_x86_64() {
            self.lower_x86(asm)
        } else {
            todo!("non x86_64, settings: {:?}", auto_cfg_str());
        }
    }
}
