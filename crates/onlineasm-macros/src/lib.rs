//! `onlineasm!` emits runtime assembly using offlineasm mnemonics.
//!
//! ```ignore
//! onlineasm!(asm;
//!     move t0, 0;
//!     move t1, {n};
//! .loop:
//!     addi t0, t1;
//!     btinz t0, .loop;
//!     #[patch = done] jmp end;
//! =>end;
//! );
//! ```
//!
//! Rules:
//!
//! * The first argument is the assembler expression (evaluated once). The
//!   rest are `;`-separated statements.
//! * `.name:` defines a local label, referenced as `.name`. `=>name` binds a
//!   fresh label at the current position to the Rust variable `name`.
//!   `#[patch = name]` / `#[patch_abs = name]` bind the emitted
//!   `PatchHandle` to `name`. Bindings introduced by `=>` and `#[patch]`
//!   are returned from the macro (statement position) so they stay usable
//!   afterwards. There are no string label maps.
//! * Operands: integer literals (decimal/`0x`/`0o`/`0b`, signed), offlineasm
//!   vregs such as `t0`, `ft0`, and `sp` (there is no built-in `arg0`-`arg7`.
//!   Declare your own `VReg` constant and splice it. A bare `argN` is a
//!   compile error pointing at that), physical registers such as `rax`,
//!   `xmm0`, `x9`, and `d0`, spelled bare or with a `%` prefix (`%rax`;
//!   unchecked, including reserved and scratch ones - `%` additionally
//!   reaches ABI names with no bare/vreg meaning, such as `%sp`/`%fp`/`%lr`
//!   on AArch64 and the full psABI name set on RISC-V), `.name` label
//!   references, `[base + index*scale + disp]` memory, and `{expr}` splices
//!   of Rust values (`VReg`, `Gpr`, `Fpr`, `Mem`, `Label`, integers).
//! * `#[patch = name]` emits an instruction through a patchable site/block.
//!   `#[patch_abs = name]` on `jmp`/`call` materializes a 64-bit absolute
//!   target through the expansion scratch GPR and branches indirectly. Use
//!   `onlineasm::repatch_u64` (or the asmkit `repatch_*` functions) to fill it in after
//!   allocation.
//!
//! * `extern name = {expr};` declares the external symbol `{expr}` (anything
//!   `Into<onlineasm::ExternalName>`) and binds the `onlineasm::Extern` to
//!   `name`, which later operands name bare (`call name`) and the macro
//!   returns like a `=>` binding. `extern near name = {expr};` declares a
//!   direct (near) reference. An operand can also declare one in place:
//!   `call extern {expr}` or `call extern near {expr}`. An extern is a
//!   `jmp`/`call` target or the source of `move`/`leap`/`globaladdr`/`la`;
//!   the image is then loaded with `Finished::load`.
//!
//! External symbols can also be brought in by splicing an address
//! (`move reg, {sym as u64}`) or by reserving a `#[patch]` slot and
//! repatching it at runtime.

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::ext::IdentExt;
use syn::parse::{Parse, ParseStream};
use syn::{braced, bracketed, Attribute, Error, Expr, Ident, Lit, LitInt, Token};

/// Names the register class of a classified physical register.
#[derive(Clone, Copy, PartialEq, Eq)]
enum RegClass {
    Gpr,
    Fpr,
}

/// Names a portable vreg spelling or a physical machine-register number.
///
/// The target resolves the vreg spelling at runtime.
enum RegId {
    VReg(String),
    Phys { id: u8, class: RegClass },
}

/// Returns the numeric x86-64 GPR id for `name`.
///
/// Aliases share their physical register's id.
fn x86_gpr(name: &str) -> Option<u8> {
    Some(match name {
        "rax" | "eax" | "ax" | "al" | "ah" => 0,
        "rcx" | "ecx" | "cx" | "cl" | "ch" => 1,
        "rdx" | "edx" | "dx" | "dl" | "dh" => 2,
        "rbx" | "ebx" | "bx" | "bl" | "bh" => 3,
        "rsp" | "esp" | "spl" => 4,
        "rbp" | "ebp" | "bpl" => 5,
        "rsi" | "esi" | "sil" => 6,
        "rdi" | "edi" | "dil" => 7,
        "r8" | "r8d" | "r8w" | "r8b" => 8,
        "r9" | "r9d" | "r9w" | "r9b" => 9,
        "r10" | "r10d" | "r10w" | "r10b" => 10,
        "r11" | "r11d" | "r11w" | "r11b" => 11,
        "r12" | "r12d" | "r12w" | "r12b" => 12,
        "r13" | "r13d" | "r13w" | "r13b" => 13,
        "r14" | "r14d" | "r14w" | "r14b" => 14,
        "r15" | "r15d" | "r15w" | "r15b" => 15,
        _ => return None,
    })
}

/// Returns the numeric x86 XMM id for `name`.
///
/// Accepts `xmm0` through `xmm15`.
fn x86_fpr(name: &str) -> Option<u8> {
    let id: u32 = name.strip_prefix("xmm")?.parse().ok()?;
    (id <= 15).then_some(id as u8)
}

/// Returns the numeric AArch64 GPR id for `name`.
///
/// Accepts `x0`-`x30`, `w0`-`w30`, `xzr`/`wzr`, and `wsp`. Runs after the
/// vreg spelling table so `sp`/`zr` keep their vreg meaning.
fn aarch64_gpr(name: &str) -> Option<u8> {
    match name {
        "xzr" | "wzr" => return Some(63),
        "wsp" => return Some(31),
        _ => {}
    }
    let body = name.strip_prefix('x').or_else(|| name.strip_prefix('w'))?;
    let id: u32 = body.parse().ok()?;
    (id <= 30).then_some(id as u8)
}

/// Returns the numeric AArch64 FPR id for `name`.
///
/// Accepts `d`, `q`, or `s` plus `0`-`31`.
fn aarch64_fpr(name: &str) -> Option<u8> {
    let body = name
        .strip_prefix('d')
        .or_else(|| name.strip_prefix('q'))
        .or_else(|| name.strip_prefix('s'))?;
    let id: u32 = body.parse().ok()?;
    (id <= 31).then_some(id as u8)
}

/// Returns the numeric RISC-V GPR id for `name`.
///
/// Accepts `x0` through `x31`.
fn riscv_gpr(name: &str) -> Option<u8> {
    let id: u32 = name.strip_prefix('x')?.parse().ok()?;
    (id <= 31).then_some(id as u8)
}

/// Returns the numeric RISC-V FPR id for `name`.
///
/// Accepts `f0` through `f31`.
fn riscv_fpr(name: &str) -> Option<u8> {
    let id: u32 = name.strip_prefix('f')?.parse().ok()?;
    (id <= 31).then_some(id as u8)
}

/// Reports whether `name` is exactly `arg0`-`arg7`.
///
/// Those non-upstream ABI aliases have no `onlineasm::regs` constants.
/// Callers report a targeted hint instead of the generic downstream
/// "cannot find value" error.
fn is_bare_arg_name(name: &str) -> bool {
    matches!(
        name,
        "arg0" | "arg1" | "arg2" | "arg3" | "arg4" | "arg5" | "arg6" | "arg7"
    )
}

/// Returns the numeric AArch64 GPR id for an ABI alias not covered by
/// [`aarch64_gpr`]'s indexed spellings: `sp`, `fp` (frame pointer, `x29`),
/// `lr` (link register, `x30`).
///
/// Kept separate from `aarch64_gpr` because bare `sp` already resolves to
/// the portable `::onlineasm::regs::sp` vreg; only the `%`-escaped physical
/// path consults this table.
fn aarch64_abi_gpr(name: &str) -> Option<u8> {
    Some(match name {
        "sp" => 31,
        "fp" => 29,
        "lr" => 30,
        _ => return None,
    })
}

/// Returns the numeric RISC-V GPR id for a psABI register name (`ra`, `sp`,
/// `gp`, `tp`, `t0`-`t6`, `s0`-`s11`, `a0`-`a7`, `fp`, `zero`).
///
/// Kept separate from `riscv_gpr`'s `xN` spellings for the same reason as
/// [`aarch64_abi_gpr`]: bare ABI names already resolve to portable vregs.
fn riscv_abi_gpr(name: &str) -> Option<u8> {
    Some(match name {
        "zero" => 0,
        "ra" => 1,
        "sp" => 2,
        "gp" => 3,
        "tp" => 4,
        "t0" => 5,
        "t1" => 6,
        "t2" => 7,
        "s0" | "fp" => 8,
        "s1" => 9,
        "a0" => 10,
        "a1" => 11,
        "a2" => 12,
        "a3" => 13,
        "a4" => 14,
        "a5" => 15,
        "a6" => 16,
        "a7" => 17,
        "s2" => 18,
        "s3" => 19,
        "s4" => 20,
        "s5" => 21,
        "s6" => 22,
        "s7" => 23,
        "s8" => 24,
        "s9" => 25,
        "s10" => 26,
        "s11" => 27,
        "t3" => 28,
        "t4" => 29,
        "t5" => 30,
        "t6" => 31,
        _ => return None,
    })
}

/// Returns the numeric RISC-V FPR id for a psABI register name (`ft0`-`ft11`,
/// `fs0`-`fs11`, `fa0`-`fa7`).
fn riscv_abi_fpr(name: &str) -> Option<u8> {
    Some(match name {
        "ft0" => 0,
        "ft1" => 1,
        "ft2" => 2,
        "ft3" => 3,
        "ft4" => 4,
        "ft5" => 5,
        "ft6" => 6,
        "ft7" => 7,
        "fs0" => 8,
        "fs1" => 9,
        "fa0" => 10,
        "fa1" => 11,
        "fa2" => 12,
        "fa3" => 13,
        "fa4" => 14,
        "fa5" => 15,
        "fa6" => 16,
        "fa7" => 17,
        "fs2" => 18,
        "fs3" => 19,
        "fs4" => 20,
        "fs5" => 21,
        "fs6" => 22,
        "fs7" => 23,
        "fs8" => 24,
        "fs9" => 25,
        "fs10" => 26,
        "fs11" => 27,
        "ft8" => 28,
        "ft9" => 29,
        "ft10" => 30,
        "ft11" => 31,
        _ => return None,
    })
}

/// Tries every indexed physical-register table, shared by the bare-name and
/// `%`-escaped classifiers.
fn try_physical(s: &str) -> Option<RegId> {
    if let Some(id) = x86_gpr(s) {
        return Some(RegId::Phys {
            id,
            class: RegClass::Gpr,
        });
    }
    if let Some(id) = x86_fpr(s) {
        return Some(RegId::Phys {
            id,
            class: RegClass::Fpr,
        });
    }
    if let Some(id) = aarch64_gpr(s) {
        return Some(RegId::Phys {
            id,
            class: RegClass::Gpr,
        });
    }
    if let Some(id) = aarch64_fpr(s) {
        return Some(RegId::Phys {
            id,
            class: RegClass::Fpr,
        });
    }
    if let Some(id) = riscv_gpr(s) {
        return Some(RegId::Phys {
            id,
            class: RegClass::Gpr,
        });
    }
    if let Some(id) = riscv_fpr(s) {
        return Some(RegId::Phys {
            id,
            class: RegClass::Fpr,
        });
    }
    None
}

/// Classifies a `%`-escaped physical-register spelling (`%rax`, `%sp`,
/// `%a0`, `%ft3`).
///
/// Accepts every spelling `classify_reg` accepts as a bare physical name,
/// plus the ABI aliases (`%sp`, `%fp`, `%lr` on AArch64; the full psABI
/// names on RISC-V) that would otherwise resolve as portable vregs when
/// written bare. Unlike `classify_reg`, an unrecognized name is a hard
/// error rather than falling back to a portable vreg.
fn classify_phys(name: &Ident) -> syn::Result<RegId> {
    let s = name.to_string();
    if let Some(reg) = try_physical(&s) {
        return Ok(reg);
    }
    if let Some(id) = aarch64_abi_gpr(&s) {
        return Ok(RegId::Phys {
            id,
            class: RegClass::Gpr,
        });
    }
    if let Some(id) = riscv_abi_gpr(&s) {
        return Ok(RegId::Phys {
            id,
            class: RegClass::Gpr,
        });
    }
    if let Some(id) = riscv_abi_fpr(&s) {
        return Ok(RegId::Phys {
            id,
            class: RegClass::Fpr,
        });
    }
    Err(Error::new_spanned(
        name,
        format!("`%{s}` is not a known physical register"),
    ))
}

/// Classifies a bare register spelling.
///
/// Physical names become numeric machine-register ids. Anything else becomes
/// a portable `::onlineasm::regs::<name>` constant, validated at compile
/// time there.
fn classify_reg(name: &Ident) -> syn::Result<RegId> {
    let s = name.to_string();
    if is_bare_arg_name(&s) {
        return Err(Error::new_spanned(
            name,
            format!(
                "`{s}` is not a register; onlineasm has no built-in argument-register \
                 aliases, declare it yourself, e.g. \
                 `const {upper}: ::onlineasm::VReg = ::onlineasm::regs::t6;` and use \
                 `{{{upper}}}`",
                s = s,
                upper = s.to_uppercase(),
            ),
        ));
    }
    if let Some(reg) = try_physical(&s) {
        return Ok(reg);
    }
    Ok(RegId::VReg(s))
}

struct AsmInput {
    asm: Expr,
    stmts: Vec<Stmt>,
}

enum Stmt {
    /// `.name:`: a local label, referenced as `.name`.
    LocalDef { name: String },
    /// `=>name`: a fresh label bound to the Rust variable `name`.
    DynDef { name: Ident },
    /// `extern [near] name = {expr}`: an external symbol bound to the Rust
    /// variable `name`.
    ExternDef { name: Ident, near: bool, expr: Expr },
    Instr {
        patch: Option<PatchAttr>,
        mnemonic: String,
        mnemonic_span: Span,
        operands: Vec<Operand>,
    },
}

/// `#[patch = name]` (relative site/block) or `#[patch_abs = name]`
/// (movable 64-bit absolute target, for cross-image inline caches).
#[derive(Clone, Copy, PartialEq, Eq)]
enum PatchMode {
    Site,
    Abs,
}

struct PatchAttr {
    name: Ident,
    mode: PatchMode,
}

enum Operand {
    Imm {
        lit: LitInt,
        neg: bool,
    },
    Reg(RegId),
    /// A bare identifier that is not a register: an `extern` binding, or
    /// `err` if no `extern` declares it.
    Name {
        name: Ident,
        err: Error,
    },
    /// `extern [near] {expr}`: an external symbol declared in place.
    Extern {
        near: bool,
        expr: Expr,
    },
    LocalLabel(String),
    Splice(Expr),
    Mem(MemOp),
}

struct MemOp {
    base: MemAtom,
    index: Option<(MemAtom, u8)>,
    disp: MemDisp,
}

enum MemAtom {
    Reg(RegId),
    Splice(Box<Expr>),
}

enum MemDisp {
    None,
    Imm(i32),
    Splice(Box<Expr>),
    NegSplice(Box<Expr>),
}

impl Parse for AsmInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let asm: Expr = input.parse()?;
        input.parse::<Token![;]>()?;
        let mut stmts = Vec::new();
        while !input.is_empty() {
            stmts.push(parse_stmt(input)?);
            // Labels are not `;`-terminated. Instructions may or may not be.
            if input.peek(Token![;]) {
                input.parse::<Token![;]>()?;
            }
        }
        Ok(AsmInput { asm, stmts })
    }
}

fn parse_patch_attr(attrs: &[Attribute]) -> syn::Result<Option<PatchAttr>> {
    let mut patch = None;
    for attr in attrs {
        let syn::Meta::NameValue(nv) = &attr.meta else {
            return Err(Error::new_spanned(attr, "expected #[patch = name]"));
        };
        let mode = if nv.path.is_ident("patch") {
            PatchMode::Site
        } else if nv.path.is_ident("patch_abs") {
            PatchMode::Abs
        } else {
            return Err(Error::new_spanned(
                attr,
                "unsupported attribute (only #[patch = name] and #[patch_abs = name])",
            ));
        };
        let syn::Expr::Path(p) = &nv.value else {
            return Err(Error::new_spanned(&nv.value, "expected #[patch = name]"));
        };
        let name = p
            .path
            .get_ident()
            .cloned()
            .ok_or_else(|| Error::new_spanned(&p.path, "expected #[patch = name]"))?;
        if patch.is_some() {
            return Err(Error::new_spanned(attr, "duplicate #[patch]"));
        }
        patch = Some(PatchAttr { name, mode });
    }
    Ok(patch)
}

fn parse_stmt(input: ParseStream) -> syn::Result<Stmt> {
    let attrs = Attribute::parse_outer(input)?;
    let patch = parse_patch_attr(&attrs)?;

    // =>name: fresh label definition bound to a Rust variable.
    if input.peek(Token![=>]) {
        input.parse::<Token![=>]>()?;
        let name: Ident = input.parse()?;
        if patch.is_some() {
            return Err(Error::new_spanned(name, "#[patch] needs an instruction"));
        }
        if input.peek(Token![:]) {
            input.parse::<Token![:]>()?;
        }
        return Ok(Stmt::DynDef { name });
    }

    // extern [near] name = {expr}: an external symbol bound to `name`.
    if input.peek(Token![extern]) {
        input.parse::<Token![extern]>()?;
        let near = parse_near(input)?;
        let name: Ident = input.call(Ident::parse_any)?;
        if patch.is_some() {
            return Err(Error::new_spanned(name, "#[patch] needs an instruction"));
        }
        if is_register_name(&name) {
            return Err(Error::new_spanned(
                &name,
                format!("extern `{name}` shadows a register name"),
            ));
        }
        input.parse::<Token![=]>()?;
        let content;
        let _ = braced!(content in input);
        let expr: Expr = content.parse()?;
        return Ok(Stmt::ExternDef { name, near, expr });
    }

    // .name: local label definition.
    if input.peek(Token![.]) {
        let fork = input.fork();
        if fork.parse::<Token![.]>().is_ok()
            && fork.call(Ident::parse_any).is_ok()
            && fork.peek(Token![:])
        {
            input.parse::<Token![.]>()?;
            let name: Ident = input.call(Ident::parse_any)?;
            input.parse::<Token![:]>()?;
            if patch.is_some() {
                return Err(Error::new_spanned(name, "#[patch] needs an instruction"));
            }
            return Ok(Stmt::LocalDef {
                name: format!(".{}", name),
            });
        }
    }

    // Rejects bare `name:` labels with a useful error instead of parsing
    // `name` as a register.
    {
        let fork = input.fork();
        if fork.call(Ident::parse_any).is_ok() && fork.peek(Token![:]) {
            let span = input.span();
            let _ = input.call(Ident::parse_any)?;
            let _ = input.parse::<Token![:]>()?;
            return Err(Error::new(
                span,
                "bare labels are not supported: use `.name:` for a local label, \
                 `=>name` for a Rust binding, or create a label with `asm.label()` \
                 and splice it as `{name}`",
            ));
        }
    }

    // Instruction: mnemonic + comma-separated operands.
    let mnemonic_span = input.span();
    let mnemonic = if input.peek(Token![move]) {
        input.parse::<Token![move]>()?;
        "move".to_string()
    } else if input.peek(Token![break]) {
        input.parse::<Token![break]>()?;
        "break".to_string()
    } else {
        input.call(Ident::parse_any)?.to_string()
    };
    let mut operands = Vec::new();
    loop {
        if input.peek(Token![;]) || input.is_empty() {
            break;
        }
        operands.push(parse_operand(input)?);
        if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;
            // Trailing comma before `;` is allowed.
            if input.peek(Token![;]) || input.is_empty() {
                break;
            }
        } else {
            break;
        }
    }
    Ok(Stmt::Instr {
        patch,
        mnemonic,
        mnemonic_span,
        operands,
    })
}

fn parse_lit_int(lit: &LitInt) -> syn::Result<i64> {
    let s = lit.to_string();
    let digits = strip_int_suffix(&s).replace('_', "");
    let v: i128 = if let Some(h) = digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        i128::from_str_radix(h, 16)
    } else if let Some(h) = digits
        .strip_prefix("0o")
        .or_else(|| digits.strip_prefix("0O"))
    {
        i128::from_str_radix(h, 8)
    } else if let Some(h) = digits
        .strip_prefix("0b")
        .or_else(|| digits.strip_prefix("0B"))
    {
        i128::from_str_radix(h, 2)
    } else {
        digits.parse::<i128>()
    }
    .map_err(|_| Error::new_spanned(lit, "integer literal out of range"))?;
    i64::try_from(v).map_err(|_| Error::new_spanned(lit, "integer literal out of range"))
}

fn strip_int_suffix(s: &str) -> &str {
    for suffix in [
        "usize", "isize", "u64", "i64", "u32", "i32", "u16", "i16", "u8", "i8",
    ] {
        if let Some(d) = s.strip_suffix(suffix) {
            if d.ends_with(|c: char| c.is_ascii_digit() || c == '_') {
                return d;
            }
        }
    }
    s
}

/// Reports whether `name` spells a register: a portable vreg or a bare
/// physical register.
fn is_register_name(name: &Ident) -> bool {
    use offlineasm_ir::regs::{FPRS, GPRS, VECS};
    let s = name.to_string();
    GPRS.iter().chain(FPRS).chain(VECS).any(|r| *r == s) || try_physical(&s).is_some()
}

/// Parses the optional `near` after `extern`.
fn parse_near(input: ParseStream) -> syn::Result<bool> {
    let fork = input.fork();
    if fork.call(Ident::parse_any).is_ok_and(|i| i == "near") {
        let _ = input.call(Ident::parse_any)?;
        return Ok(true);
    }
    Ok(false)
}

fn parse_operand(input: ParseStream) -> syn::Result<Operand> {
    if input.peek(Token![extern]) {
        input.parse::<Token![extern]>()?;
        let near = parse_near(input)?;
        let content;
        let _ = braced!(content in input);
        let expr: Expr = content.parse()?;
        return Ok(Operand::Extern { near, expr });
    }
    // -N: negative immediate.
    if input.peek(Token![-]) && input.peek2(Lit) {
        input.parse::<Token![-]>()?;
        let lit: LitInt = input.parse()?;
        let _ = parse_lit_int(&lit)?;
        return Ok(Operand::Imm { lit, neg: true });
    }
    if input.peek(Lit) {
        let lit: Lit = input.parse()?;
        match lit {
            Lit::Int(i) => {
                let _ = parse_lit_int(&i)?;
                return Ok(Operand::Imm { lit: i, neg: false });
            }
            other => {
                return Err(Error::new_spanned(
                    other,
                    "only integer literals are operands",
                ))
            }
        }
    }
    if input.peek(syn::token::Brace) {
        let content;
        let _ = braced!(content in input);
        let expr: Expr = content.parse()?;
        return Ok(Operand::Splice(expr));
    }
    if input.peek(syn::token::Bracket) {
        let content;
        let _ = bracketed!(content in input);
        return Ok(Operand::Mem(parse_mem(&content)?));
    }
    // Possibly dotted local label reference (`.loop`).
    if input.peek(Token![.]) {
        let fork = input.fork();
        if fork.parse::<Token![.]>().is_ok() && fork.call(Ident::parse_any).is_ok() {
            input.parse::<Token![.]>()?;
            let name: Ident = input.call(Ident::parse_any)?;
            return Ok(Operand::LocalLabel(format!(".{}", name)));
        }
    }
    // %rax: an explicit physical-register escape, matching offlineasm's
    // `%`-prefixed spelling.
    if input.peek(Token![%]) {
        input.parse::<Token![%]>()?;
        let name: Ident = input.call(Ident::parse_any)?;
        return Ok(Operand::Reg(classify_phys(&name)?));
    }
    if input.peek(Ident) {
        let name: Ident = input.call(Ident::parse_any)?;
        return Ok(match classify_reg(&name) {
            Ok(reg) => Operand::Reg(reg),
            Err(err) => Operand::Name { name, err },
        });
    }
    Err(input.error("expected an operand"))
}

fn parse_mem_atom(input: ParseStream) -> syn::Result<MemAtom> {
    if input.peek(syn::token::Brace) {
        let content;
        let _ = braced!(content in input);
        return Ok(MemAtom::Splice(Box::new(content.parse()?)));
    }
    if input.peek(Token![%]) {
        input.parse::<Token![%]>()?;
        let name: Ident = input.call(Ident::parse_any)?;
        return Ok(MemAtom::Reg(classify_phys(&name)?));
    }
    if input.peek(Ident) {
        let name: Ident = input.call(Ident::parse_any)?;
        return Ok(MemAtom::Reg(classify_reg(&name)?));
    }
    Err(input.error("expected a register or {expr}"))
}

fn parse_mem(input: ParseStream) -> syn::Result<MemOp> {
    let base = parse_mem_atom(input)?;
    let mut index = None;
    let mut disp = MemDisp::None;
    // [base + index*scale] and/or [+/- disp]
    if input.peek(Token![+]) {
        input.parse::<Token![+]>()?;
        let fork = input.fork();
        let is_index = fork.peek(syn::token::Brace) || fork.peek(Ident);
        if is_index {
            let atom = parse_mem_atom(input)?;
            let mut scale: u8 = 1;
            if input.peek(Token![*]) {
                input.parse::<Token![*]>()?;
                if input.peek(Lit) {
                    let lit: LitInt = input.parse()?;
                    let v = parse_lit_int(&lit)?;
                    if ![1, 2, 4, 8].contains(&v) {
                        return Err(Error::new_spanned(lit, "scale must be 1, 2, 4, or 8"));
                    }
                    scale = v as u8;
                } else {
                    return Err(input.error("scale must be an integer literal"));
                }
            }
            index = Some((atom, scale));
            if input.peek(Token![+]) || input.peek(Token![-]) {
                disp = parse_mem_disp(input)?;
            }
        } else {
            disp = parse_mem_disp_after_plus(input)?;
        }
    } else if input.peek(Token![-]) {
        disp = parse_mem_disp(input)?;
    }
    if !input.is_empty() {
        return Err(input.error("unexpected tokens in memory operand"));
    }
    Ok(MemOp { base, index, disp })
}

fn parse_mem_disp(input: ParseStream) -> syn::Result<MemDisp> {
    let neg = input.peek(Token![-]);
    if neg {
        input.parse::<Token![-]>()?;
    } else {
        input.parse::<Token![+]>()?;
    }
    parse_mem_disp_after_sign(input, neg)
}

fn parse_mem_disp_after_plus(input: ParseStream) -> syn::Result<MemDisp> {
    parse_mem_disp_after_sign(input, false)
}

fn parse_mem_disp_after_sign(input: ParseStream, neg: bool) -> syn::Result<MemDisp> {
    if input.peek(syn::token::Brace) {
        let content;
        let _ = braced!(content in input);
        let expr: Expr = content.parse()?;
        return Ok(if neg {
            MemDisp::NegSplice(Box::new(expr))
        } else {
            MemDisp::Splice(Box::new(expr))
        });
    }
    if input.peek(Lit) {
        let lit: LitInt = input.parse()?;
        let v = parse_lit_int(&lit)?;
        let v = if neg { -v } else { v };
        let d =
            i32::try_from(v).map_err(|_| Error::new_spanned(lit, "displacement out of range"))?;
        return Ok(MemDisp::Imm(d));
    }
    Err(input.error("displacement must be an integer literal or {expr}"))
}

#[proc_macro]
pub fn onlineasm(input: TokenStream) -> TokenStream {
    match onlineasm_inner(input.into()) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Holds one call-site binding from `=>name` or `#[patch = name]`.
struct Binding {
    /// The identifier visible at the call site (and inside the block).
    public: Ident,
    /// `true` for `=>name` (the block must declare the label), `false` for
    /// `#[patch]` (the statement declares the handle).
    is_label: bool,
}

fn onlineasm_inner(input: TokenStream2) -> syn::Result<TokenStream2> {
    let parsed = syn::parse2::<AsmInput>(input)?;
    let asm_expr = &parsed.asm;

    let mut locals: Vec<(String, Ident)> = Vec::new();
    let mut bindings: Vec<Binding> = Vec::new();
    for stmt in &parsed.stmts {
        match stmt {
            Stmt::LocalDef { name } => {
                local_ident(&mut locals, name, Span::mixed_site());
            }
            Stmt::DynDef { name } => bindings.push(Binding {
                public: name.clone(),
                is_label: true,
            }),
            Stmt::ExternDef { name, .. } => bindings.push(Binding {
                public: name.clone(),
                is_label: false,
            }),
            Stmt::Instr {
                patch, operands, ..
            } => {
                for op in operands {
                    if let Operand::LocalLabel(name) = op {
                        local_ident(&mut locals, name, Span::mixed_site());
                    }
                }
                if let Some(p) = patch {
                    bindings.push(Binding {
                        public: p.name.clone(),
                        is_label: false,
                    });
                }
            }
        }
    }

    let mut prelude = TokenStream2::new();
    for (_, id) in &locals {
        prelude.extend(quote! {
            let #id = __onlineasm_asm.label();
        });
    }
    for binding in bindings.iter().filter(|b| b.is_label) {
        let id = &binding.public;
        prelude.extend(quote! {
            let #id = __onlineasm_asm.label();
        });
    }

    let mut stmts = TokenStream2::new();
    let mut externs: Vec<Ident> = Vec::new();
    for stmt in &parsed.stmts {
        stmts.extend(emit_stmt(&locals, &externs, &bindings, stmt)?);
        if let Stmt::ExternDef { name, .. } = stmt {
            externs.push(name.clone());
        }
    }

    let temps: Vec<&Ident> = bindings.iter().map(|b| &b.public).collect();
    let publics = temps.clone();

    let tail = if temps.is_empty() {
        TokenStream2::new()
    } else {
        quote! { ( #(#temps,)* ) }
    };

    let body = quote! {{
        let __onlineasm_asm = &mut #asm_expr;
        #prelude
        #stmts
        #tail
    }};

    if bindings.is_empty() {
        // No call-site bindings: a plain block keeps the borrow scoped.
        Ok(quote! { { #body } })
    } else {
        Ok(quote! {
            let ( #(#publics,)* ) = #body;
        })
    }
}

fn local_ident(locals: &mut Vec<(String, Ident)>, name: &str, span: Span) -> Ident {
    if let Some((_, id)) = locals.iter().find(|(n, _)| n == name) {
        return id.clone();
    }
    let id = Ident::new(&format!("__onlineasm_local_{}", locals.len()), span);
    locals.push((name.to_string(), id.clone()));
    id
}

fn emit_stmt(
    locals: &[(String, Ident)],
    externs: &[Ident],
    bindings: &[Binding],
    stmt: &Stmt,
) -> syn::Result<TokenStream2> {
    match stmt {
        Stmt::LocalDef { name } => {
            let id = local_ident_ref(locals, name);
            Ok(quote! {
                __onlineasm_asm.bind(#id);
            })
        }
        Stmt::DynDef { name } => Ok(quote! {
            __onlineasm_asm.bind(#name);
        }),
        Stmt::ExternDef { name, near, expr } => {
            let reach = reach_tokens(*near);
            Ok(quote! {
                let #name = __onlineasm_asm.extern_name(#expr, #reach);
            })
        }
        Stmt::Instr {
            patch,
            mnemonic,
            mnemonic_span,
            operands,
        } => {
            let mnem = mnemonic_ident(mnemonic, *mnemonic_span);
            let mut prologue = TokenStream2::new();
            let mut ops = Vec::new();
            for (i, op) in operands.iter().enumerate() {
                let expr = emit_value(locals, externs, op)?;
                let id = Ident::new(&format!("__onlineasm_op{i}"), Span::mixed_site());
                prologue.extend(quote! {
                    let #id = #expr;
                });
                ops.push(id);
            }
            if let Some(attr) = patch {
                let binding = bindings
                    .iter()
                    .find(|b| b.public == attr.name)
                    .expect("patch binding");
                let handle = &binding.public;
                match attr.mode {
                    PatchMode::Site => Ok(quote! {
                        #prologue
                        let #handle = match __onlineasm_asm.emit_patched(#mnem, &[#(#ops),*]) {
                            ::std::result::Result::Ok(__h) => __h,
                            ::std::result::Result::Err(__e) => {
                                ::std::panic!("onlineasm: lowering `{}` failed: {}", #mnemonic, __e)
                            }
                        };
                    }),
                    PatchMode::Abs => {
                        if mnemonic != "jmp" && mnemonic != "call" {
                            return Err(Error::new(
                                *mnemonic_span,
                                "onlineasm: #[patch_abs] applies to `jmp`/`call` only",
                            ));
                        }
                        let target =
                            match (operands.first(), operands.len()) {
                                (Some(Operand::Imm { .. }) | Some(Operand::Splice(_)), 1) => {
                                    ops[0].clone()
                                }
                                (Some(_), _) => return Err(Error::new(
                                    *mnemonic_span,
                                    "onlineasm: #[patch_abs] target must be an integer or {expr}",
                                )),
                                (None, _) => {
                                    return Err(Error::new(
                                        *mnemonic_span,
                                        "onlineasm: #[patch_abs] needs a target operand",
                                    ))
                                }
                            };
                        let move_ident = mnemonic_ident("move", *mnemonic_span);
                        Ok(quote! {
                            #prologue
                            let __onlineasm_scratch = __onlineasm_asm.scratch().gpr;
                            let #handle = match __onlineasm_asm.emit_patched(
                                #move_ident,
                                &[#target, ::onlineasm::Op::Gpr(__onlineasm_scratch)],
                            ) {
                                ::std::result::Result::Ok(__h) => __h,
                                ::std::result::Result::Err(__e) => {
                                    ::std::panic!("onlineasm: lowering `move` failed: {}", __e)
                                }
                            };
                            let __onlineasm_scratch_op = ::onlineasm::Op::Gpr(__onlineasm_scratch);
                            if let ::std::result::Result::Err(__e) =
                                __onlineasm_asm.emit(#mnem, &[__onlineasm_scratch_op])
                            {
                                ::std::panic!("onlineasm: lowering `{}` failed: {}", #mnemonic, __e)
                            }
                        })
                    }
                }
            } else {
                Ok(quote! {
                    #prologue
                    if let ::std::result::Result::Err(__e) =
                        __onlineasm_asm.emit(#mnem, &[#(#ops),*])
                    {
                        ::std::panic!("onlineasm: lowering `{}` failed: {}", #mnemonic, __e)
                    }
                })
            }
        }
    }
}

fn local_ident_ref(locals: &[(String, Ident)], name: &str) -> Ident {
    locals
        .iter()
        .find(|(n, _)| n == name)
        .map(|(_, id)| id.clone())
        .expect("local label")
}

/// Maps a mnemonic to its `::onlineasm::mnem::<name>` constant.
///
/// Encodes Rust keywords as raw idents.
fn mnemonic_ident(mnemonic: &str, span: Span) -> TokenStream2 {
    let ident = match mnemonic {
        "move" => Ident::new_raw("move", span),
        "break" => Ident::new_raw("break", span),
        other => Ident::new(other, span),
    };
    quote! { ::onlineasm::mnem::#ident }
}

fn reach_tokens(near: bool) -> TokenStream2 {
    if near {
        quote! { ::onlineasm::Reach::Near }
    } else {
        quote! { ::onlineasm::Reach::Far }
    }
}

/// Emits an operand expression evaluating to an `Op`.
fn emit_value(
    locals: &[(String, Ident)],
    externs: &[Ident],
    op: &Operand,
) -> syn::Result<TokenStream2> {
    Ok(match op {
        Operand::Name { name, err } => {
            if !externs.contains(name) {
                return Err(err.clone());
            }
            quote! { __onlineasm_asm.op(#name) }
        }
        Operand::Extern { near, expr } => {
            let reach = reach_tokens(*near);
            quote! {{
                let __onlineasm_ext = __onlineasm_asm.extern_name(#expr, #reach);
                __onlineasm_asm.op(__onlineasm_ext)
            }}
        }
        Operand::Imm { lit, neg } => {
            if *neg {
                quote! { __onlineasm_asm.op(-(#lit as i64)) }
            } else {
                quote! { __onlineasm_asm.op(#lit as i64) }
            }
        }
        Operand::Reg(RegId::VReg(name)) => {
            if let Some(ext) = externs.iter().find(|e| *e == name) {
                quote! { __onlineasm_asm.op(#ext) }
            } else {
                let ident = Ident::new(name, Span::call_site());
                quote! { __onlineasm_asm.op(::onlineasm::regs::#ident) }
            }
        }
        Operand::Reg(RegId::Phys {
            id,
            class: RegClass::Gpr,
        }) => quote! { __onlineasm_asm.op(::onlineasm::Gpr(#id)) },
        Operand::Reg(RegId::Phys {
            id,
            class: RegClass::Fpr,
        }) => quote! { __onlineasm_asm.op(::onlineasm::Fpr(#id)) },
        Operand::LocalLabel(name) => {
            let id = local_ident_ref(locals, name);
            quote! { __onlineasm_asm.op(#id) }
        }
        Operand::Splice(e) => quote! { __onlineasm_asm.op(#e) },
        Operand::Mem(m) => {
            let base = emit_mem_atom(m.base_ref());
            let op = match &m.index {
                None => {
                    let disp = emit_disp(&m.disp);
                    quote! { __onlineasm_asm.mem(#base, #disp) }
                }
                Some((atom, scale)) => {
                    let idx = emit_mem_atom(atom);
                    let disp = emit_disp(&m.disp);
                    quote! { __onlineasm_asm.mem_indexed(#base, #idx, #scale, #disp) }
                }
            };
            quote! { ::onlineasm::Op::Mem(#op) }
        }
    })
}

impl MemOp {
    fn base_ref(&self) -> &MemAtom {
        &self.base
    }
}

fn emit_mem_atom(atom: &MemAtom) -> TokenStream2 {
    match atom {
        MemAtom::Reg(RegId::VReg(name)) => {
            let ident = Ident::new(name, Span::call_site());
            quote! { ::onlineasm::regs::#ident }
        }
        MemAtom::Reg(RegId::Phys {
            id,
            class: RegClass::Gpr,
        }) => quote! { ::onlineasm::Gpr(#id) },
        MemAtom::Reg(RegId::Phys {
            id,
            class: RegClass::Fpr,
        }) => quote! { ::onlineasm::Fpr(#id) },
        MemAtom::Splice(e) => quote! { #e },
    }
}

fn emit_disp(disp: &MemDisp) -> TokenStream2 {
    match disp {
        MemDisp::None => quote! { 0i32 },
        MemDisp::Imm(d) => quote! { #d },
        MemDisp::Splice(e) => quote! { (#e as i32) },
        MemDisp::NegSplice(e) => quote! { (0i32 - (#e as i32)) },
    }
}
