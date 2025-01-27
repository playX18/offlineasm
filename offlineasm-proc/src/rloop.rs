use std::{
    collections::HashSet,
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::{ast::*, id};
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{parse_quote, spanned::Spanned, FnArg, Ident};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    USIZE,
    ISIZE,
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    F32,
    F64,
    PTR,
    REGPTR,
}

impl RegisterId {
    pub fn rvalue(&self) -> syn::Result<TokenStream> {
        let name = self.name.to_string();

        Ok(match name.as_str() {
            "t0" | "r0" => quote! { t0 },
            "t6" | "a0" => quote! { a0 },
            "t1" | "a1" => quote! { a1 },
            "t2" | "a2" | "r1" => quote! { a2 },
            "t3" | "a3" => quote! { a3 },
            "t4" | "a4" => quote! { a4 },
            "t7" | "a5" => quote! { a5 },
            "t5" => quote! { t5 },
            "csr0" => quote! { csr0 },
            "csr1" => quote! { csr1 },
            "csr2" => quote! { csr2 },
            "csr3" => quote! { csr3 },
            "csr4" => quote! { csr4 },
            "sp" => quote! { sp },
            "cfr" => quote! { cfr },
            "scratch" => quote! { scratch },
            _ => quote! { #name },
        })
    }
}

impl FPRegisterId {
    pub fn rvalue(&self) -> syn::Result<TokenStream> {
        let name = self.name.to_string();

        Ok(match name.as_str() {
            "ft0" | "fa0" | "fr" | "wfa0" => quote! { ft0 },
            "ft1" | "fa1" | "wfa1" => quote! { ft1 },
            "ft2" | "fa2" | "wfa2" => quote! { ft2 },
            "ft3" | "fa3" | "wfa3" => quote! { ft3 },
            "ft4" | "wfa4" => quote! { ft4 },
            "ft5" | "wfa5" => quote! { ft5 },
            "wfa6" => quote! { wfa6 },
            "wfa7" => quote! { wfa7 },
            _ => quote! { #name },
        })
    }
}

impl Label {
    pub fn state_name(&self) -> Ident {
        Ident::new(&format!("Global_{}", self.name()), Span::call_site())
    }
}

impl LocalLabel {
    pub fn state_name(&self) -> Ident {
        Ident::new(&format!("Local_{}", self.name), Span::call_site())
    }
}

impl LabelMapping {
    pub fn state_name(&self) -> Ident {
        match self {
            LabelMapping::Global(global) => global.state_name(),
            LabelMapping::Local(local) => local.state_name(),
        }
    }
}

impl Node {
    pub fn rvalue(&self) -> syn::Result<TokenStream> {
        match self {
            //Self::Const(x) => Ok(x.expr.to_token_stream()),
            Self::RegisterId(register) => register.rvalue(),
            Self::FPRegisterId(register) => register.rvalue(),

            Self::Address(address) => {
                let ptr = self.ptr()?;
                Ok(quote! {
                    Register::from_u(#ptr as usize)
                })
            }

            Self::BaseIndex(base_index) => {
                let ptr = self.ptr()?;
                Ok(quote! {
                    Register::from_u(#ptr as usize)
                })
            }

            Self::AbsoluteAddress(absolute) => {
                let ptr = self.ptr()?;
                Ok(quote! {
                    Register::from_u(#ptr as usize)
                })
            }

            Self::Immediate(imm) => {
                let imm = imm.value;
                Ok(quote! {
                    Register::from_i(#imm)
                })
            }

            Self::LabelReference(label) => {
                match label.label {
                    LabelMapping::Global(ref global) if !global.defined_in_macro => {
                        let name = global.name().clone();
                        return Ok(quote! {
                            Register::from_u(#name as usize)
                        });
                    }

                    _ => (),
                }
                let state_name = label.label.state_name();
                Ok(quote! {
                    Register::from_u(RunState::#state_name as usize)
                })
            }

            Self::LocalLabelReference(local_label) => {
                let state_name = local_label.label.state_name();
                Ok(quote! {
                    Register::from_u(RunState::#state_name as usize)
                })
            }

            Self::Const(constant) => {
                let expr = constant.expr.clone();

                Ok(quote! {
                    Register::from_i(const { #expr } as isize)
                })
            }

            Self::Instruction(instruction) => {
                unreachable!("no rvalue for instruction: {}", instruction.opcode)
            }

            _ => todo!("{}", self),
        }
    }

    pub fn lvalue(&self, typ: Type) -> syn::Result<TokenStream> {
        match self {
            Self::Address(_) | Self::BaseIndex(_) | Self::AbsoluteAddress(_) => {
                let ptr = self.ptr()?;
                Ok(match typ {
                    Type::I8 => {
                        quote! {
                            *#ptr.cast::<i8>().as_mut().unwrap()
                        }
                    }
                    Type::U8 => {
                        quote! {
                            *#ptr.cast::<u8>().as_mut().unwrap()
                        }
                    }

                    Type::I16 => {
                        quote! {
                            *#ptr.cast::<i16>().as_mut().unwrap()
                        }
                    }

                    Type::U16 => {
                        quote! {
                            *#ptr.cast::<u16>().as_mut().unwrap()
                        }
                    }

                    Type::I32 => {
                        quote! {
                            *#ptr.cast::<i32>().as_mut().unwrap()
                        }
                    }

                    Type::U32 => {
                        quote! {
                            *#ptr.cast::<u32>().as_mut().unwrap()
                        }
                    }

                    Type::I64 => {
                        quote! {
                            *#ptr.cast::<i64>().as_mut().unwrap()
                        }
                    }

                    Type::U64 => {
                        quote! {
                            *#ptr.cast::<u64>().as_mut().unwrap()
                        }
                    }

                    Type::F32 => {
                        quote! {
                            *#ptr.cast::<f32>().as_mut().unwrap()
                        }
                    }

                    Type::F64 => {
                        quote! {
                            *#ptr.cast::<f64>().as_mut().unwrap()
                        }
                    }

                    Type::USIZE => {
                        quote! {
                            *#ptr.cast::<usize>().as_mut().unwrap()
                        }
                    }

                    Type::ISIZE => {
                        quote! {
                            *#ptr.cast::<isize>().as_mut().unwrap()
                        }
                    }

                    _ => unreachable!("no lvalue for type: {:?} in {}", typ, self),
                })
            }

            _ => {
                let rval = self.rvalue()?;
                Ok(match typ {
                    Type::I8 => {
                        quote! {
                            *#rval.i8_mut()
                        }
                    }
                    Type::U8 => {
                        quote! {
                            *#rval.u8_mut()
                        }
                    }

                    Type::I16 => {
                        quote! {
                            *#rval.i16_mut()
                        }
                    }

                    Type::U16 => {
                        quote! {
                            *#rval.u16_mut()
                        }
                    }

                    Type::I32 => {
                        quote! {
                            *#rval.i32_mut()
                        }
                    }

                    Type::U32 => {
                        quote! {
                            *#rval.u32_mut()
                        }
                    }

                    Type::I64 => {
                        quote! {
                            *#rval.i64_mut()
                        }
                    }

                    Type::U64 => {
                        quote! {
                            *#rval.u64_mut()
                        }
                    }

                    Type::PTR => {
                        quote! {
                            *#rval.ptr_mut()
                        }
                    }

                    Type::REGPTR => {
                        quote! {
                            *#rval.reg_ptr_mut()
                        }
                    }

                    Type::ISIZE => {
                        quote! {
                            *#rval.i_mut()
                        }
                    }

                    Type::USIZE => {
                        quote! {
                            *#rval.u_mut()
                        }
                    }

                    Type::F64 => {
                        quote! {
                            *#rval.f64_mut()
                        }
                    }

                    Type::F32 => {
                        quote! {
                            *#rval.f32_mut()
                        }
                    }
                })
            }
        }
    }

    pub fn ptr(&self) -> syn::Result<TokenStream> {
        match self {
            Self::Address(address) => {
                let base = address.base.rvalue()?;
                let offset = address.offset.immediate_value()?;
                Ok(quote! {
                    #base.ptr().byte_offset(#offset)
                })
            }

            Self::BaseIndex(base_index) => {
                let base = base_index.base.rvalue()?;
                let index = base_index.index.rvalue()?;
                let scale = base_index.scale.rvalue()?;
                let offset = base_index.offset.immediate_value()?;
                Ok(quote! {
                    base.ptr().byte_offset(#index.i() * #scale as isize + #offset as isize)
                })
            }

            Self::AbsoluteAddress(absolute) => {
                let address = absolute.base.immediate_value()?;
                Ok(quote! {
                    #address as *mut u8
                })
            }

            _ => {
                return Err(syn::Error::new(
                    proc_macro2::Span::call_site(),
                    format!("not an address node: {}", self),
                ))
            }
        }
    }
}

impl Instruction {
    pub fn handle_binop(&self, wrap_op: &str, op: &str, typ: Type) -> syn::Result<TokenStream> {
        let dst = self.operands[0].lvalue(typ)?;
        let (lhs, rhs) = if self.operands.len() == 2 {
            (self.operands[0].rvalue()?, self.operands[1].rvalue()?)
        } else {
            (self.operands[1].rvalue()?, self.operands[2].rvalue()?)
        };
        let op = Ident::new(op, Span::call_site());
        let wrap_op = Ident::new(wrap_op, Span::call_site());
        match typ {
            Type::I8 => Ok(quote! {
                let res = #lhs.i8().#wrap_op(#rhs.i8());
                #dst = res;
            }),
            Type::I16 => Ok(quote! {
                let res = #lhs.i16().#wrap_op(#rhs.i16());
                #dst = res;
            }),
            Type::I32 => Ok(quote! {
                let res = #lhs.i32().#wrap_op(#rhs.i32());
                #dst = res;
            }),
            Type::I64 => Ok(quote! {
                let res = #lhs.i64().#wrap_op(#rhs.i64());
                #dst = res;
            }),

            Type::ISIZE => Ok(quote! {
                let res = #lhs.i().#wrap_op(#rhs.i());
                #dst = res;
            }),
            Type::USIZE => Ok(quote! {
                let res = #lhs.u().#wrap_op(#rhs.u());
                #dst = res;
            }),

            Type::F64 => Ok(quote! {
                let res = #lhs.f64().#op(#rhs.f64());
                #dst = res;
            }),
            Type::F32 => Ok(quote! {
                let res = #lhs.f32().#op(#rhs.f32());
                #dst = res;
            }),

            _ => unreachable!(),
        }
    }

    pub fn handle_unop(&self, wrap_op: &str, op: &str, typ: Type) -> syn::Result<TokenStream> {
        let dst = self.operands[0].lvalue(typ)?;
        let src = self.operands[0].rvalue()?;
        let op = Ident::new(op, Span::call_site());
        let wrap_op = Ident::new(wrap_op, Span::call_site());
        match typ {
            Type::I8 => Ok(quote! {
                #dst = Register::from_i8(#src.i8().#wrap_op());
            }),
            Type::I16 => Ok(quote! {
                #dst = Register::from_i16(#src.i16().#wrap_op());
            }),
            Type::I32 => Ok(quote! {
                #dst = Register::from_i32(#src.i32().#wrap_op());
            }),
            Type::I64 => Ok(quote! {
                #dst = Register::from_i64(#src.i64().#wrap_op());
            }),

            Type::ISIZE => Ok(quote! {
                #dst = Register::from_i(#src.i().#wrap_op());
            }),
            Type::USIZE => Ok(quote! {
                #dst = Register::from_u(#src.u().#wrap_op());
            }),

            Type::F64 => Ok(quote! {
                #dst = Register::from_f64(#src.f64().#op());
            }),
            Type::F32 => Ok(quote! {
                #dst = Register::from_f32(#src.f32().#op());
            }),

            _ => unreachable!(),
        }
    }

    fn handle_jump(&self) -> syn::Result<TokenStream> {
        let target = self.operands.last().unwrap(); // labels are always the last operand.

        match target {
            Node::LabelReference(lref) => {
                let state_name = lref.label.state_name();
                Ok(quote! {
                    state = RunState::#state_name;
                    continue 'run_loop;
                })
            }

            Node::LocalLabelReference(lref) => {
                let state_name = lref.label.state_name();
                Ok(quote! {
                    state = RunState::#state_name;
                    continue 'run_loop;
                })
            }

            Node::Const(constant) => {
                let expr = constant.expr.clone();
                Ok(quote! {
                    state = RunState::from_u(#expr as usize);
                    continue 'run_loop;
                })
            }

            _ => {
                let target = target.rvalue()?;
                Ok(quote! {
                    state = RunState::from_u(#target.u() as usize);
                    continue 'run_loop;
                })
            }
        }
    }

    pub fn lower_rloop(&self) -> syn::Result<TokenStream> {
        println!("lower {}", self);
        let name = self.opcode.to_string();
        let operands = &self.operands;
        match name.as_str() {
            "mov" => {
                let dst = self.operands[0].rvalue()?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src;
                })
            }

            "addi" => self.handle_binop("wrapping_add", "add", Type::I32),
            "addp" => self.handle_binop("wrapping_add", "add", Type::ISIZE),
            "addq" => self.handle_binop("wrapping_add", "add", Type::I64),
            "andi" => self.handle_binop("bitand", "bitand", Type::I32),
            "andp" => self.handle_binop("bitand", "bitand", Type::ISIZE),
            "andq" => self.handle_binop("bitand", "bitand", Type::I64),

            "lshifti" => self.handle_binop("wrapping_shl", "shl", Type::I32),
            "lshiftp" => self.handle_binop("wrapping_shl", "shl", Type::ISIZE),
            "lshiftq" => self.handle_binop("wrapping_shl", "shl", Type::I64),

            "rshifti" => self.handle_binop("wrapping_shr", "shr", Type::I32),
            "rshiftp" => self.handle_binop("wrapping_shr", "shr", Type::ISIZE),
            "rshiftq" => self.handle_binop("wrapping_shr", "shr", Type::I64),

            "urshifti" => self.handle_binop("wrapping_shr", "shr", Type::I32),
            "urshiftp" => self.handle_binop("wrapping_shr", "shr", Type::ISIZE),
            "urshiftq" => self.handle_binop("wrapping_shr", "shr", Type::I64),

            "rrotatei" => self.handle_binop("rotate_right", "rotate_right", Type::I32),
            "rrotateq" => self.handle_binop("rotate_right", "rotate_right", Type::I64),
            "muli" => self.handle_binop("wrapping_mul", "mul", Type::I32),
            "mulp" => self.handle_binop("wrapping_mul", "mul", Type::ISIZE),
            "mulq" => self.handle_binop("wrapping_mul", "mul", Type::I64),

            "negi" => self.handle_unop("wrapping_neg", "neg", Type::I32),
            "negp" => self.handle_unop("wrapping_neg", "neg", Type::ISIZE),
            "negq" => self.handle_unop("wrapping_neg", "neg", Type::I64),
            "noti" => self.handle_unop("not", "not", Type::I32),
            "notq" => self.handle_unop("not", "not", Type::I64),

            "ori" => self.handle_binop("bitor", "bitor", Type::I32),
            "orp" => self.handle_binop("bitor", "bitor", Type::ISIZE),
            "orq" => self.handle_binop("bitor", "bitor", Type::I64),

            "lrotatei" => self.handle_binop("rotate_left", "rotate_left", Type::I32),
            "lrotateq" => self.handle_binop("rotate_left", "rotate_left", Type::I64),

            "subi" => self.handle_binop("wrapping_sub", "sub", Type::I32),
            "subp" => self.handle_binop("wrapping_sub", "sub", Type::ISIZE),
            "subq" => self.handle_binop("wrapping_sub", "sub", Type::I64),

            "xori" => self.handle_binop("bitxor", "bitxor", Type::I32),
            "xorp" => self.handle_binop("bitxor", "bitxor", Type::ISIZE),
            "xorq" => self.handle_binop("bitxor", "bitxor", Type::I64),

            "leap" => {
                let dst = self.operands[0].lvalue(Type::ISIZE)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src as isize;
                })
            }

            "loadi" => {
                let dst = self.operands[0].lvalue(Type::I32)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<i32>().read();
                })
            }

            "atomicloadi" => {
                let dst = self.operands[0].lvalue(Type::I32)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<AtomicI32>().as_ref().unwrap().load(Ordering::Relaxed);
                })
            }

            "storei" => {
                let dst = self.operands[0].ptr()?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst.cast::<i32>().write(#src.i32());
                })
            }

            "loadis" => {
                let dst = self.operands[0].lvalue(Type::I64)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = Register::from_i64(#src.cast::<i32>().read() as i64);
                })
            }

            "loadp" => {
                let dst = self.operands[0].lvalue(Type::ISIZE)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<isize>().read();
                })
            }

            "storep" => {
                let dst = self.operands[0].ptr()?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst.cast::<isize>().write(#src.i());
                })
            }

            "loadq" => {
                let dst = self.operands[0].lvalue(Type::I64)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<i64>().read();
                })
            }

            "atomicloadq" => {
                let dst = self.operands[0].lvalue(Type::I64)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<AtomicI64>().as_ref().unwrap().load(Ordering::Relaxed);
                })
            }

            "loadb" => {
                let dst = self.operands[0].lvalue(Type::I8)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<i8>().read();
                })
            }

            "loadbsi" => {
                let dst = self.operands[0].lvalue(Type::I32)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<i8>().read() as i32;
                })
            }

            "loadbsq" => {
                let dst = self.operands[0].lvalue(Type::I64)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<i8>().read() as i64;
                })
            }

            "loadh" => {
                let dst = self.operands[0].lvalue(Type::I16)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<i16>().read();
                })
            }

            "loadhsi" => {
                let dst = self.operands[0].lvalue(Type::I32)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<i16>().read() as i32;
                })
            }

            "atomicloadh" => {
                let dst = self.operands[0].lvalue(Type::I16)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<AtomicI16>().as_ref().unwrap().load(Ordering::Relaxed);
                })
            }

            "loadhsq" => {
                let dst = self.operands[0].lvalue(Type::I64)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<i16>().read() as i64;
                })
            }

            "storeb" => {
                let dst = self.operands[0].ptr()?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst.cast::<i8>().write(#src.i8());
                })
            }

            "storeh" => {
                let dst = self.operands[0].ptr()?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst.cast::<i16>().write(#src.i16());
                })
            }

            "loadf" => {
                let dst = self.operands[0].lvalue(Type::F64)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<f32>().read() as f64;
                })
            }

            "loadd" => {
                let dst = self.operands[0].lvalue(Type::F64)?;
                let src = self.operands[1].ptr()?;
                Ok(quote! {
                    #dst = #src.cast::<f64>().read();
                })
            }

            "moved" => {
                let dst = self.operands[0].rvalue()?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src;
                })
            }

            "storef" => {
                let dst = self.operands[0].ptr()?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst.cast::<f32>().write(#src.f64() as f32);
                })
            }

            "stored" => {
                let dst = self.operands[0].ptr()?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst.cast::<f64>().write(#src.f64());
                })
            }

            "addf" => self.handle_binop("wrapping_add", "add", Type::F32),
            "addd" => self.handle_binop("wrapping_add", "add", Type::F64),
            "divd" => self.handle_binop("wrapping_div", "div", Type::F64),
            "divf" => self.handle_binop("wrapping_div", "div", Type::F32),
            "muld" => self.handle_binop("wrapping_mul", "mul", Type::F64),
            "mulf" => self.handle_binop("wrapping_mul", "mul", Type::F32),
            "negf" => self.handle_unop("wrapping_neg", "neg", Type::F32),
            "negd" => self.handle_unop("wrapping_neg", "neg", Type::F64),
            "subf" => self.handle_binop("wrapping_sub", "sub", Type::F32),
            "subd" => self.handle_binop("wrapping_sub", "sub", Type::F64),
            "sqrd" => self.handle_unop("sqrt", "sqrt", Type::F64),
            "sqrtf" => self.handle_unop("sqrt", "sqrt", Type::F32),
            "roundf" => self.handle_unop("round", "round", Type::F32),
            "roundd" => self.handle_unop("round", "round", Type::F64),
            "ceilf" => self.handle_unop("ceil", "ceil", Type::F32),
            "ceild" => self.handle_unop("ceil", "ceil", Type::F64),
            "floorf" => self.handle_unop("floor", "floor", Type::F32),
            "floord" => self.handle_unop("floor", "floor", Type::F64),
            "truncatef" => self.handle_unop("trunc", "trunc", Type::F32),
            "truncated" => self.handle_unop("trunc", "trunc", Type::F64),

            "truncatef2i" | "truncatef2is" => {
                let dst = self.operands[0].lvalue(Type::I32)?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src.f32().trunc() as i32;
                })
            }

            "truncated2i" | "truncated2is" => {
                let dst = self.operands[0].lvalue(Type::I32)?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src.f64().trunc() as i32;
                })
            }

            "truncatef2q" | "truncatef2qs" => {
                let dst = self.operands[0].lvalue(Type::I64)?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src.f64().trunc() as i64;
                })
            }

            "truncated2q" | "truncated2qs" => {
                let dst = self.operands[0].lvalue(Type::I64)?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src.f64().trunc() as i64;
                })
            }

            "ci2d" | "ci2ds" => {
                let dst = self.operands[0].lvalue(Type::F64)?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src.i32() as f64;
                })
            }

            "ci2f" | "ci2fs" => {
                let dst = self.operands[0].lvalue(Type::F32)?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src.i32() as f32;
                })
            }

            "cq2f" | "cq2fs" => {
                let dst = self.operands[0].lvalue(Type::F32)?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src.i64() as f32;
                })
            }

            "cq2d" | "cq2ds" => {
                let dst = self.operands[0].lvalue(Type::F64)?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src.i64() as f64;
                })
            }

            "cd2f" => {
                let dst = self.operands[0].lvalue(Type::F32)?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src.f64() as f32;
                })
            }

            "cf2d" => {
                let dst = self.operands[0].lvalue(Type::F64)?;
                let src = self.operands[1].rvalue()?;
                Ok(quote! {
                    #dst = #src.f32() as f64;
                })
            }

            "bdeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                if self.operands[0] == self.operands[1] {
                    Ok(quote! {
                        if #lhs.f64().partial_cmp(&#rhs.f64()).is_some() {
                            #jmp
                        }
                    })
                } else {
                    Ok(quote! {
                        if #lhs.f64().partial_cmp(&#rhs.f64()) == Some(Ordering::Equal) {
                            #jmp
                        }
                    })
                }
            }

            "bdneq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f64().total_cmp(&#rhs.f64()) != Ordering::Equal {
                        #jmp
                    }
                })
            }

            "bdgt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f64().total_cmp(&#rhs.f64()) == Ordering::Greater {
                        #jmp
                    }
                })
            }

            "bdgteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f64().total_cmp(&#rhs.f64()) != Ordering::Less {
                        #jmp
                    }
                })
            }

            "bdlt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f64().total_cmp(&#rhs.f64()) == Ordering::Less {
                        #jmp
                    }
                })
            }

            "bdlteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f64().total_cmp(&#rhs.f64()) != Ordering::Greater {
                        #jmp
                    }
                })
            }

            "bdequn" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;

                Ok(quote! {
                    if #lhs.f64().partial_cmp(&#rhs.f64()) == Some(Ordering::Equal) {
                        #jmp
                    }
                })
            }

            "bdnequn" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                if self.operands[0] == self.operands[1] {
                    Ok(quote! {
                        if #lhs.f64().partial_cmp(&#rhs.f64()).is_none() {
                            #jmp
                        }
                    })
                } else {
                    Ok(quote! {
                        if #lhs.f64().partial_cmp(&#rhs.f64()) != Some(Ordering::Equal) {
                            #jmp
                        }
                    })
                }
            }

            "bdgtun" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f64().partial_cmp(&#rhs.f64()) == Some(Ordering::Greater) {
                        #jmp
                    }
                })
            }

            "bdgtequn" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f64().partial_cmp(&#rhs.f64()) != Some(Ordering::Less) {
                        #jmp
                    }
                })
            }

            "bdltun" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f64().partial_cmp(&#rhs.f64()) == Some(Ordering::Less) {
                        #jmp
                    }
                })
            }

            "bdltequn" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f64().partial_cmp(&#rhs.f64()) != Some(Ordering::Greater) {
                        #jmp
                    }
                })
            }

            "bfeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                if self.operands[0] == self.operands[1] {
                    Ok(quote! {
                        if #lhs.f32().partial_cmp(&#rhs.f32()).is_some() {
                            #jmp
                        }
                    })
                } else {
                    Ok(quote! {
                        if #lhs.f32().partial_cmp(&#rhs.f32()) == Some(Ordering::Equal) {
                            #jmp
                        }
                    })
                }
            }

            "bfneq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f32().total_cmp(&#rhs.f32()) != Ordering::Equal {
                        #jmp
                    }
                })
            }

            "bfgt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f32().total_cmp(&#rhs.f32()) == Ordering::Greater {
                        #jmp
                    }
                })
            }

            "bfgteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f32().total_cmp(&#rhs.f32()) != Ordering::Less {
                        #jmp
                    }
                })
            }

            "bflt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f32().total_cmp(&#rhs.f32()) == Ordering::Less {
                        #jmp
                    }
                })
            }

            "bflteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f32().total_cmp(&#rhs.f32()) != Ordering::Greater {
                        #jmp
                    }
                })
            }

            "bfequn" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f32().partial_cmp(&#rhs.f32()) == Some(Ordering::Equal) {
                        #jmp
                    }
                })
            }

            "bfnequn" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                if self.operands[0] == self.operands[1] {
                    Ok(quote! {
                        if #lhs.f32().partial_cmp(&#rhs.f32()).is_none() {
                            #jmp
                        }
                    })
                } else {
                    Ok(quote! {
                        if #lhs.f32().partial_cmp(&#rhs.f32()) != Some(Ordering::Equal) {
                            #jmp
                        }
                    })
                }
            }

            "bfgtun" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f32().partial_cmp(&#rhs.f32()) == Some(Ordering::Greater) {
                        #jmp
                    }
                })
            }

            "bfgtequn" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f32().partial_cmp(&#rhs.f32()) != Some(Ordering::Less) {
                        #jmp
                    }
                })
            }

            "bfltun" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f32().partial_cmp(&#rhs.f32()) == Some(Ordering::Less) {
                        #jmp
                    }
                })
            }

            "bfltequn" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.f32().partial_cmp(&#rhs.f32()) != Some(Ordering::Greater) {
                        #jmp
                    }
                })
            }

            "bieq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i32() == #rhs.i32() {
                        #jmp
                    }
                })
            }

            "bpeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i() == #rhs.i() {
                        #jmp
                    }
                })
            }

            "bqeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i64() == #rhs.i64() {
                        #jmp
                    }
                })
            }

            "bineq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i32() != #rhs.i32() {
                        #jmp
                    }
                })
            }

            "bpneq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i() != #rhs.i() {
                        #jmp
                    }
                })
            }

            "bqneq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i64() != #rhs.i64() {
                        #jmp
                    }
                })
            }

            "bia" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u32() > #rhs.u32() {
                        #jmp
                    }
                })
            }

            "bpa" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u() > #rhs.u() {
                        #jmp
                    }
                })
            }

            "bqa" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u64() > #rhs.u64() {
                        #jmp
                    }
                })
            }

            "biaeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u32() >= #rhs.u32() {
                        #jmp
                    }
                })
            }

            "bpaeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u() >= #rhs.u() {
                        #jmp
                    }
                })
            }

            "bqaeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u64() >= #rhs.u64() {
                        #jmp
                    }
                })
            }

            "bib" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u32() < #rhs.u32() {
                        #jmp
                    }
                })
            }

            "bpb" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u() < #rhs.u() {
                        #jmp
                    }
                })
            }

            "bqb" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u64() < #rhs.u64() {
                        #jmp
                    }
                })
            }

            "bibeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u32() <= #rhs.u32() {
                        #jmp
                    }
                })
            }

            "bpbeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u() <= #rhs.u() {
                        #jmp
                    }
                })
            }

            "bqbeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u64() <= #rhs.u64() {
                        #jmp
                    }
                })
            }

            "bigt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i32() > #rhs.i32() {
                        #jmp
                    }
                })
            }

            "bpgt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i() > #rhs.i() {
                        #jmp
                    }
                })
            }

            "bqgt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i64() > #rhs.i64() {
                        #jmp
                    }
                })
            }

            "bigteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i32() >= #rhs.i32() {
                        #jmp
                    }
                })
            }

            "bpgteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i() >= #rhs.i() {
                        #jmp
                    }
                })
            }

            "bqgteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i64() >= #rhs.i64() {
                        #jmp
                    }
                })
            }

            "bilt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i32() < #rhs.i32() {
                        #jmp
                    }
                })
            }

            "bplt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i() < #rhs.i() {
                        #jmp
                    }
                })
            }

            "bqlt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i64() < #rhs.i64() {
                        #jmp
                    }
                })
            }

            "bilteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i32() <= #rhs.i32() {
                        #jmp
                    }
                })
            }

            "bplteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i() <= #rhs.i() {
                        #jmp
                    }
                })
            }

            "bqlteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i64() <= #rhs.i64() {
                        #jmp
                    }
                })
            }

            "bbeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i8() == #rhs.i8() {
                        #jmp
                    }
                })
            }

            "bbneq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i8() != #rhs.i8() {
                        #jmp
                    }
                })
            }

            "bba" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u8() > #rhs.u8() {
                        #jmp
                    }
                })
            }

            "bbaeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u8() >= #rhs.u8() {
                        #jmp
                    }
                })
            }

            "bbb" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u8() < #rhs.u8() {
                        #jmp
                    }
                })
            }

            "bbbeq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.u8() <= #rhs.u8() {
                        #jmp
                    }
                })
            }

            "bbgt   " => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i8() > #rhs.i8() {
                        #jmp
                    }
                })
            }

            "bbgteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i8() >= #rhs.i8() {
                        #jmp
                    }
                })
            }

            "bblt" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i8() < #rhs.i8() {
                        #jmp
                    }
                })
            }

            "bblteq" => {
                let lhs = self.operands[0].rvalue()?;
                let rhs = self.operands[1].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #lhs.i8() <= #rhs.i8() {
                        #jmp
                    }
                })
            }
            // jump if signed
            "btis" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i32() < 0 {
                        #jmp
                    }
                })
            }

            "btps" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i() < 0 {
                        #jmp
                    }
                })
            }

            "btqs" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i64() < 0 {
                        #jmp
                    }
                })
            }

            "btiz" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i32() == 0 {
                        #jmp
                    }
                })
            }

            "btqz" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i64() == 0 {
                        #jmp
                    }
                })
            }

            "btpz" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i() == 0 {
                        #jmp
                    }
                })
            }

            "btinz" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i32() != 0 {
                        #jmp
                    }
                })
            }

            "btqnz" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i64() != 0 {
                        #jmp
                    }
                })
            }

            "btpnz" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i() != 0 {
                        #jmp
                    }
                })
            }

            "btbs" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i8() < 0 {
                        #jmp
                    }
                })
            }

            "btbz" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i8() == 0 {
                        #jmp
                    }
                })
            }

            "btbnz" => {
                let op = self.operands[0].rvalue()?;
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    if #op.i8() != 0 {
                        #jmp
                    }
                })
            }

            "jmp" => {
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    #jmp
                })
            }

            "call" => {
                /* no SP or CFR modifications, special-cased in RLoopEmitter */
                let jmp = self.handle_jump()?;
                Ok(quote! {
                    #jmp
                })
            }

            "push" => {
                let mut output = TokenStream::new();
                for op in self.operands.iter() {
                    let op = op.rvalue()?;
                    output.extend(quote! {
                        push!(#op);
                    })
                }
                Ok(output)
            }

            "pop" => {
                let mut output = TokenStream::new();
                for op in self.operands.iter() {
                    let op = op.lvalue(Type::ISIZE)?;
                    output.extend(quote! {
                        #op = pop!();
                    })
                }
                Ok(output)
            }

            "breakpoint" => Ok(quote! {
                panic!("breakpoint");
            }),

            "ret" => Ok(quote! {
                let op = pop!();
                state = RunState::from_u(op as usize);
                continue 'run_loop;
            }),

            // rloop-specific: call operand with arguments passed to it. Pass `sp` as the first argument.
            "callNative" => {
                let mut output = TokenStream::new();
                let target = self.operands[0].rvalue()?;

                output.extend(quote! {
                    let target: unsafe extern "C-unwind" fn(&mut OfflineAsmLoopState) = unsafe { ::std::mem::transmute(#target.u()) };
                    self.state = state;
                    self.t0 = t0;
                    self.a0 = a0;
                    self.a1 = a1;
                    self.a2 = a2;
                    self.a3 = a3;
                    self.a4 = a4;
                    self.a5 = a5;
                    self.t5 = t5;
                    self.csr0 = csr0;
                    self.csr1 = csr1;
                    self.csr2 = csr2;
                    self.csr3 = csr3;
                    self.csr4 = csr4;
                    self.sp = sp;
                    self.cfr = cfr;
                    self.scratch = scratch;
                    self.ft0 = ft0;
                    self.ft1 = ft1;
                    self.ft2 = ft2;
                    self.ft3 = ft3;
                    self.ft4 = ft4;
                    self.ft5 = ft5;
                    self.wfa6 = wfa6;
                    self.wfa7 = wfa7;
                    target(&mut state);
                    state = self.state;
                    t0 = self.t0;
                    a0 = self.a0;
                    a1 = self.a1;
                    a2 = self.a2;
                    a3 = self.a3;
                    a4 = self.a4;
                    a5 = self.a5;
                    t5 = self.t5;
                    csr0 = self.csr0;
                    csr1 = self.csr1;
                    csr2 = self.csr2;
                    csr3 = self.csr3;
                    csr4 = self.csr4;
                    sp = self.sp;
                    cfr = self.cfr;
                    scratch = self.scratch;
                    ft0 = self.ft0;
                    ft1 = self.ft1;
                    ft2 = self.ft2;
                    ft3 = self.ft3;
                    ft4 = self.ft4;
                    ft5 = self.ft5;
                    wfa6 = self.wfa6;
                    wfa7 = self.wfa7;
                });
                Ok(output)
            }
            _ => unreachable!("{}", self.opcode),
        }
    }
}

pub struct RLoopEmitter {
    pub states: HashSet<Ident>,
    pub output: TokenStream,
}
static RETURN_COUNT: AtomicUsize = AtomicUsize::new(0);

impl RLoopEmitter {
    pub fn new() -> Self {
        Self {
            states: HashSet::new(),
            output: TokenStream::new(),
        }
    }

    pub fn add_state(&mut self, state: Ident) {
        assert!(!self.states.contains(&state));
        self.states.insert(state);
    }

    pub fn new_return_point(&mut self) -> Ident {
        let id = format!("return_{}", RETURN_COUNT.fetch_add(1, Ordering::Relaxed));
        let id = Ident::new(&id, Span::call_site());
        self.add_state(id.clone());
        id
    }

    pub fn compile_sequence(&mut self, seq: &[Node]) -> syn::Result<TokenStream> {
        let exit_loop = Ident::new("exit_loop", Span::call_site());
        self.add_state(exit_loop.clone());

        let mut current_output = TokenStream::new();
        let mut current_state = None;
        let mut exports = TokenStream::new();
        for node in seq {
            match node {
                Node::Export(export) => {
                    let label = export.label.state_name();
                    let syn::ForeignItemFn { sig, .. } = &export.item;
                    let abi = &export.abi;

                    let mut args = sig.inputs.iter();
                    let gp_args = [id("a0"), id("a1"), id("a2"), id("a3"), id("a4"), id("a5")];
                    let fp_args = [id("ft0"), id("ft1"), id("ft2"), id("ft3")];

                    let mut gp_args = gp_args.iter();
                    let mut fp_args = fp_args.iter();

                    let mut init = TokenStream::new();
                    let mut post = TokenStream::new();

                    let mut arg_count = 0;

                    for arg in args {
                        match arg {
                            FnArg::Typed(pat) => {
                                let (is_gpr, is_fpr) = match &*pat.ty {
                                    syn::Type::Ptr(_)
                                    | syn::Type::BareFn(_)
                                    | syn::Type::Reference(_) => (true, false),
                                    syn::Type::Path(path) => {
                                        if path.path.segments.len() != 1 {
                                            return Err(syn::Error::new(
                                                pat.span(),
                                                "rloop does not yet support complex types in `export`",
                                            ));
                                        }
                                        let segment = &path.path.segments[0];
                                        let name = segment.ident.to_string();
                                        match name.as_str() {
                                            "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "u64"
                                            | "usize" | "isize" | "i64" | "u128" | "i128" => {
                                                (true, false)
                                            }
                                            "f32" | "f64" => (false, true),
                                            _ => (false, false),
                                        }
                                    }

                                    _ => {
                                        return Err(syn::Error::new(
                                            pat.span(),
                                            "rloop does not yet support complex types in `export`",
                                        ))
                                    }
                                };

                                if is_gpr {
                                    match gp_args.next() {
                                        Some(reg) => {
                                            let arg_name = match &*pat.pat {
                                                syn::Pat::Ident(ident) => &ident.ident,
                                                _ => return Err(syn::Error::new(
                                                    pat.span(),
                                                    "rloop does not yet support complex types in `export`",
                                                )),
                                            };
                                            init.extend(quote! {
                                                state.#reg = Register::from(#arg_name);
                                            });
                                        }

                                        None => {
                                            let arg_name = match &*pat.pat {
                                                syn::Pat::Ident(ident) => &ident.ident,
                                                _ => return Err(syn::Error::new(
                                                    pat.span(),
                                                    "rloop does not yet support complex types in `export`",
                                                )),
                                            };
                                            post.extend(quote! {
                                                (state.sp.u() as *mut Register).write(Register::from(#arg_name));
                                            });
                                        }
                                    }
                                } else {
                                    match fp_args.next() {
                                        Some(reg) => {
                                            let arg_name = match &*pat.pat {
                                                syn::Pat::Ident(ident) => &ident.ident,
                                                _ => return Err(syn::Error::new(
                                                    pat.span(),
                                                    "rloop does not yet support complex types in `export`",
                                                )),
                                            };
                                            init.extend(quote! {
                                                state.#reg = Register::from(#arg_name);
                                                state.sp = Register::from_u(state.sp.u() - size_of::<Register>());
                                            });
                                        }

                                        None => {
                                            let arg_name = match &*pat.pat {
                                                syn::Pat::Ident(ident) => &ident.ident,
                                                _ => return Err(syn::Error::new(
                                                    pat.span(),
                                                    "rloop does not yet support complex types in `export`",
                                                )),
                                            };
                                            post.extend(quote! {
                                                (state.sp.u() as *mut Register).write(Register::from(#arg_name));
                                                state.sp = Register::from_u(state.sp.u() - size_of::<Register>());
                                            });
                                        }
                                    }
                                }
                            }
                            x => todo!("{}", x.to_token_stream()),
                        }
                    }

                    exports.extend(quote! {
                        unsafe #abi #sig {
                            let state = get_state();
                            #init
                            unsafe { state.run(rloop_impl::RunState::#label); }
                            state.t0.into()
                        }
                    })
                }
                Node::Label(label) => {
                    let next_state = label.state_name();
                    self.add_state(next_state.clone());
                    if let Some(state) = current_state.take() {
                        self.output.extend(quote! {
                            RunState::#state => {{
                                #current_output
                                state = RunState::#next_state;
                                continue 'run_loop;
                            }}
                        });
                    }

                    current_state = Some(label.state_name());
                    current_output = TokenStream::new();
                }

                Node::LocalLabel(label) => {
                    self.add_state(label.state_name());

                    if let Some(state) = current_state.take() {
                        let next_state = label.state_name();
                        self.output.extend(quote! {
                            RunState::#state => {{
                                #current_output
                                state = RunState::#next_state;
                                continue 'run_loop;
                            }}
                        });
                    }

                    current_state = Some(label.state_name());
                    current_output = TokenStream::new();
                }

                Node::Instruction(ins) => {
                    let is_call = ins.opcode == "call";

                    let return_point = if is_call {
                        let return_point = self.new_return_point();
                        current_output.extend(quote! {
                            push!(Register::from_u(RunState::#return_point as usize));
                        });
                        Some(return_point)
                    } else {
                        None
                    };

                    let source = node.to_string();
                    current_output.extend(quote! {
                        let _ = #source;
                    });
                    current_output.extend(ins.lower_rloop()?);

                    if is_call {
                        let current = current_state.take().unwrap();
                        self.output.extend(quote! {
                            RunState::#current => {{
                                #current_output
                            }}
                        });
                        current_state = return_point;
                        current_output = TokenStream::new();
                    }
                }

                _ => todo!(),
            }
        }

        if let Some(state) = current_state.take() {
            self.output.extend(quote! {
                RunState::#state => {{
                    #current_output
                }}
            });
        }

        let mut output = TokenStream::new();
        self.output.extend(quote! {
            RunState::#exit_loop => {{
                self.state = state;
                self.t0 = t0;
                self.a0 = a0;
                self.a1 = a1;
                self.a2 = a2;
                self.a3 = a3;
                self.a4 = a4;
                self.a5 = a5;
                self.t5 = t5;
                self.csr0 = csr0;
                self.csr1 = csr1;
                self.csr2 = csr2;
                self.csr3 = csr3;
                self.csr4 = csr4;
                self.sp = sp;
                self.cfr = cfr;
                self.scratch = scratch;
                self.ft0 = ft0;
                self.ft1 = ft1;
                self.ft2 = ft2;
                self.ft3 = ft3;
                self.ft4 = ft4;
                self.ft5 = ft5;
                self.wfa6 = wfa6;
                self.wfa7 = wfa7;
                break 'run_loop;
            }}
        });
        let handlers = self.output.clone();

        let mut states = self.states.iter().collect::<Vec<_>>();
        states.sort_by(|a, b| a.to_string().cmp(&b.to_string()));

        let mut runstate_from_u = TokenStream::new();
        for (i, state) in states.iter().enumerate() {
            runstate_from_u.extend(quote! {
                #i => RunState::#state,
            });
        }

        runstate_from_u.extend(quote! {
            _ => std::process::exit(1),
        });

        output.extend(quote! {

            #[derive(Debug)]
            #[repr(usize)]
            pub enum RunState {
                #(#states),*
            }

            impl Copy for RunState {}
            impl Clone for RunState {
                fn clone(&self) -> Self {
                    *self
                }
            }
        });

        output.extend(quote! {
            impl RunState {
                pub fn from_u(u: usize) -> Self {
                    match u {
                        #runstate_from_u
                    }
                }
            }
        });

        output.extend(quote! {
            pub struct OfflineAsmLoopState {
                pub state: RunState,
                pub t0: Register,
                pub a0: Register,
                pub a1: Register,
                pub a2: Register,
                pub a3: Register,
                pub a4: Register,
                pub a5: Register,
                pub t5: Register,
                pub csr0: Register,
                pub csr1: Register,
                pub csr2: Register,
                pub csr3: Register,
                pub csr4: Register,
                pub sp: Register,
                pub cfr: Register,
                pub scratch: Register,
                pub ft0: Register,
                pub ft1: Register,
                pub ft2: Register,
                pub ft3: Register,
                pub ft4: Register,
                pub ft5: Register,
                pub wfa6: Register,
                pub wfa7: Register,
                pub stack: Stack,
            }


            impl OfflineAsmLoopState {
                pub fn new(stack_size: usize) -> Self {
                    let stack = Stack::new(stack_size);
                    Self {
                        state: RunState::exit_loop,
                        ft0: Register::from_u64(0xbadbeefdeadbeefu64),
                        ft1: Register::from_u64(0xbadbeefdeadbeefu64),
                        ft2: Register::from_u64(0xbadbeefdeadbeefu64),
                        ft3: Register::from_u64(0xbadbeefdeadbeefu64),
                        ft4: Register::from_u64(0xbadbeefdeadbeefu64),
                        ft5: Register::from_u64(0xbadbeefdeadbeefu64),
                        wfa6: Register::from_u64(0xbadbeefdeadbeefu64),
                        wfa7: Register::from_u64(0xbadbeefdeadbeefu64),
                        t0: Register::from_u64(0xbadbeefdeadbeefu64),
                        a0: Register::from_u64(0xbadbeefdeadbeefu64),
                        a1: Register::from_u64(0xbadbeefdeadbeefu64),
                        a2: Register::from_u64(0xbadbeefdeadbeefu64),
                        a3: Register::from_u64(0xbadbeefdeadbeefu64),
                        a4: Register::from_u64(0xbadbeefdeadbeefu64),
                        a5: Register::from_u64(0xbadbeefdeadbeefu64),
                        t5: Register::from_u64(0xbadbeefdeadbeefu64),
                        csr0: Register::from_u64(0xbadbeefdeadbeefu64),
                        csr1: Register::from_u64(0xbadbeefdeadbeefu64),
                        csr2: Register::from_u64(0xbadbeefdeadbeefu64),
                        csr3: Register::from_u64(0xbadbeefdeadbeefu64),
                        csr4: Register::from_u64(0xbadbeefdeadbeefu64),
                        sp: Register::from_u64(stack.end() as *const u8 as u64),
                        cfr: Register::from_u64(0xbadbeefdeadbeefu64),
                        scratch: Register::from_u64(0xbadbeefdeadbeefu64),
                        stack,
                    }
                }

                pub unsafe fn run(&mut self, mut state: RunState) {
                    self.state = state;

                    let mut t0 = self.t0;
                    let mut a0 = self.a0;
                    let mut a1 = self.a1;
                    let mut a2 = self.a2;
                    let mut a3 = self.a3;
                    let mut a4 = self.a4;
                    let mut a5 = self.a5;
                    let mut t5 = self.t5;
                    let mut csr0 = self.csr0;
                    let mut csr1 = self.csr1;
                    let mut csr2 = self.csr2;
                    let mut csr3 = self.csr3;
                    let mut csr4 = self.csr4;
                    let mut sp = self.sp;
                    let mut cfr = self.cfr;
                    let mut scratch = self.scratch;
                    let mut ft0 = self.ft0;
                    let mut ft1 = self.ft1;
                    let mut ft2 = self.ft2;
                    let mut ft3 = self.ft3;
                    let mut ft4 = self.ft4;
                    let mut ft5 = self.ft5;
                    let mut wfa6 = self.wfa6;
                    let mut wfa7 = self.wfa7;

                    macro_rules! push {
                        ($value: expr) => {{
                            (sp.u() as *mut usize).write($value.u());
                            sp = Register::from_u(sp.u() - size_of::<usize>());
                        }}
                    }

                    macro_rules! pop {
                        () => {{
                            sp = Register::from_u(sp.u() + size_of::<usize>());
                            let value = (sp.u() as *mut isize).read();
                            value
                        }}
                    }

                    push!(Register::from_u(RunState::exit_loop as usize));

                    'run_loop: loop {
                        println!("state: {:?}", state);
                        match state {
                            #handlers
                        }
                    }
                }
            }
        });

        Ok(quote! {
            #[doc(hidden)]
            pub mod rloop_impl {
                use ::core::ops::*;
                use ::offlineasm::rloop::*;
                #output
            }

            pub fn new_rloop_state(stack_size: usize) -> rloop_impl::OfflineAsmLoopState {
                rloop_impl::OfflineAsmLoopState::new(stack_size)
            }

            thread_local! {
                static STATE: ::std::cell::LazyCell<
                    ::std::cell::UnsafeCell<rloop_impl::OfflineAsmLoopState>> =
                    ::std::cell::LazyCell::new(
                        || ::std::cell::UnsafeCell::new(rloop_impl::OfflineAsmLoopState::new(16*1024))
                    );
            }

            fn get_state() -> &'static mut rloop_impl::OfflineAsmLoopState {
                STATE.with(|state| unsafe {
                    &mut *state.get()
                })
            }

            #exports
        })
    }
}
