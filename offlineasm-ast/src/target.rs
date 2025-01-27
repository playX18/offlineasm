use crate::{
    instructions::{Instruction, MapOperands},
    operands::*,
    stmt::{LabelMapping, Sequence, Stmt},
};
use proc_macro2::Span;
use std::{
    cell::{LazyCell, RefCell},
    collections::HashMap,
    rc::Rc,
};

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
        self.assembler_output.push('\n');
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
