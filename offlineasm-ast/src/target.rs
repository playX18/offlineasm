use crate::{
    instructions::{Instruction, MapOperands},
    operands::*,
    stmt::{Label, LabelMapping, LocalLabel, Sequence, Stmt},
};
use proc_macro2::Span;
use std::{
    cell::{LazyCell, RefCell},
    collections::HashMap,
    rc::Rc,
};

pub mod x86_proc;
pub mod x86;

pub struct Assembler {
    pub assembler_output: String,
    pub constants: Vec<syn::Expr>,
    pub extern_symbols: Vec<syn::Ident>,
}

impl Assembler {
    pub fn new() -> Self {
        Self {
            assembler_output: String::new(),
            constants: Vec::new(),
            extern_symbols: Vec::new(),
        }
    }

    pub fn add_extern_symbol(&mut self, symbol: syn::Ident) -> Operand {
        let id = self.constants.len() + self.extern_symbols.len();
        self.extern_symbols.push(symbol);
        Operand::Constant(Constant {
            span: Span::call_site(),
            value: ConstantValue::Reference(id),
        })
    }

    pub fn add_constant(&mut self, value: syn::Expr) -> Operand {
        let id = self.constants.len() + self.extern_symbols.len();
        self.constants.push(value);
        Operand::Constant(Constant {
            span: Span::call_site(),
            value: ConstantValue::Reference(id),
        })
    }

    pub fn puts(&mut self, s: &str) {
        self.assembler_output.push_str(s);
        self.assembler_output.push('\n');
    }

    pub fn format(&mut self, arguments: std::fmt::Arguments<'_>) {
        use std::fmt::Write;
        self.assembler_output.write_fmt(arguments).unwrap();
    }

    pub fn local_label(&mut self, label: &LocalLabel) {
        self.format(format_args!(
            "{label}:\n",
            label = local_label_string(&label.name.to_string())
        ));
    }

    fn global_label_impl(
        &mut self,
        label: &Label,
        alt_entry: impl Fn(&Label) -> String,
        alignment: &str,
        visibility: impl Fn(&Label) -> String,
    ) {
        if is_darwin() {
            self.puts(".section __TEXT");
        } else {
            self.puts(".text");
        }
        self.puts(alignment);
        self.puts(&alt_entry(label));
        self.format(format_args!(
            ".globl {label}\n",
            label = global_reference(&label.name.to_string())
        ));
        self.puts(&visibility(label));
        self.format(format_args!(
            "{label}:\n",
            label = global_reference(&label.name.to_string())
        ));
    }

    pub fn global_label(&mut self, label: &Label) {
        self.global_label_impl(label, |_| "".to_string(), "", |_| "".to_string());
    }

    pub fn local_label_reference(label: &LocalLabel) -> String {
        local_label_string(&label.name.to_string())
    }

    pub fn global_label_reference(label: &Label) -> String {
        global_reference(&label.name.to_string())
    }
}

impl Operand {
    pub fn collect_constants(&self, asm: &mut Assembler) -> Self {
        match self {
            Operand::Constant(c) => match &c.value {
                ConstantValue::Expression(expr) => asm.add_constant(expr.clone()),
                _ => self.clone(),
            },

            Operand::LabelReference(lref) => match &lref.label {
                LabelMapping::Global(g) if !g.defined_in_macro.get() => {
                    asm.add_extern_symbol(g.name.clone())
                }
                _ => self.clone(),
            },

            Operand::Address(address) => Operand::Address(Rc::new(match &address.kind {
                AddressKind::Base { base, offset } => Address {
                    span: address.span.clone(),
                    kind: AddressKind::Base {
                        base: base.collect_constants(asm),
                        offset: offset.collect_constants(asm),
                    },
                },
                AddressKind::BaseIndex {
                    base,
                    index,
                    scale,
                    offset,
                } => Address {
                    span: address.span.clone(),
                    kind: AddressKind::BaseIndex {
                        base: base.collect_constants(asm),
                        index: index.collect_constants(asm),
                        scale: scale.collect_constants(asm),
                        offset: offset.collect_constants(asm),
                    },
                },
                AddressKind::Absolute { value } => Address {
                    span: address.span.clone(),
                    kind: AddressKind::Absolute {
                        value: value.collect_constants(asm),
                    },
                },
            })),

            _ => self.clone(),
        }
    }
}

impl Sequence {
    pub fn collect_constants(&self, asm: &mut Assembler) -> Self {
        let mut new_stmts = Vec::new();
        for stmt in self.stmts.iter() {
            new_stmts.push(stmt.collect_constants(asm));
        }
        Self {
            span: self.span.clone(),
            stmts: new_stmts,
        }
    }
}

impl Instruction {
    pub fn collect_constants(&self, asm: &mut Assembler) -> Self {
        self.map_operands(|op| op.collect_constants(asm))
    }
}

impl Stmt {
    pub fn collect_constants(&self, asm: &mut Assembler) -> Self {
        match self {
            Stmt::Instruction(instr) => Stmt::Instruction(Rc::new(instr.collect_constants(asm))),
            Stmt::Sequence(seq) => Stmt::Sequence(Rc::new(seq.collect_constants(asm))),
            _ => self.clone(),
        }
    }
}

thread_local! {
    static SETTINGS: LazyCell<RefCell<HashMap<String, bool>>> = LazyCell::new(|| RefCell::new(HashMap::new()));
}

pub fn is_setting_set(name: &str) -> bool {
    SETTINGS.with(|settings| settings.borrow().get(name).cloned().unwrap_or(false))
}

pub fn set_setting(name: &str, value: bool) {
    SETTINGS.with(|settings| settings.borrow_mut().insert(name.to_string(), value));
}

pub fn is_darwin() -> bool {
    is_setting_set("macos")
        || is_setting_set("ios")
        || is_setting_set("watchos")
        || is_setting_set("tvos")
}

pub fn is_linux() -> bool {
    is_setting_set("linux")
}

pub fn is_unix() -> bool {
    is_setting_set("unix")
}

pub fn is_x64() -> bool {
    is_setting_set("x86_64")
}

pub fn is_arm64() -> bool {
    is_setting_set("arm64")
}

pub fn is_riscv64() -> bool {
    is_setting_set("riscv64")
}

pub fn is_windows() -> bool {
    is_setting_set("windows")
}

pub fn is_freebsd() -> bool {
    is_setting_set("freebsd")
}

pub fn is_haiku() -> bool {
    is_setting_set("haiku")
}

pub fn is_qnx() -> bool {
    is_setting_set("qnx")
}

pub fn symbol_string(symbol: &str) -> String {
    if is_darwin() {
        format!("_{}", symbol)
    } else {
        symbol.to_string()
    }
}

pub fn global_reference(symbol: &str) -> String {
    if (is_linux() || is_freebsd() || is_haiku() || is_qnx()) && is_x64() {
        format!("{symbol}@plt")
    } else {
        symbol_string(symbol)
    }
}

pub fn is_aix() -> bool {
    is_setting_set("aix")
}

pub fn local_reference(symbol: &str) -> String {
    global_reference(symbol)
}

pub fn hide_symbol(symbol: &str) -> String {
    if is_darwin() {
        return format!(".private_extern _{symbol}");
    } else if is_aix() {
        return format!(".lglobl {symbol}");
    } else if is_unix() {
        return format!(".hidden {symbol}");
    } else {
        symbol.to_string()
    }
}

pub fn local_label_string(name: &str) -> String {
    if is_darwin() {
        format!("L{name}")
    } else {
        format!(".L{name}")
    }
}

impl LocalLabel {
    pub fn lower(&self, asm: &mut Assembler) -> syn::Result<()> {
        asm.local_label(&self);
        Ok(())
    }
}

impl Label {
    pub fn lower(&self, asm: &mut Assembler) -> syn::Result<()> {
        asm.global_label(&self);
        Ok(())
    }
}

impl Stmt {
    pub fn lower(&self, asm: &mut Assembler) -> syn::Result<()> {
        todo!()
    }
}