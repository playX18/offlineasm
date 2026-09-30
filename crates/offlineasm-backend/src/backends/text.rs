//! Shared plumbing for the assembly-text emitters.
//!
//! `offlineasm` lowers every mnemonic to the shared IR (`offlineasm_ir`) and
//! then prints each `Inst` as one or more assembly lines. This module holds
//! the parts that do not depend on the instruction set: resolving the IR's
//! opaque label and symbol handles to text, formatting immediates and
//! displacements, and small encoding predicates the per-ISA emitters share.
//!
//! The per-ISA printers live next door: [`text_x86`](super::text_x86),
//! [`text_arm64`](super::text_arm64), and
//! [`text_riscv64`](super::text_riscv64).

use super::LowerCtx;
use offlineasm_ir::{Disp, ExternId, Lbl, SymId};

/// Selects the instruction set a text emitter prints.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TextTarget {
    X86_64,
    Aarch64,
    Riscv64,
}

impl TextTarget {
    /// Returns the `offlineasm` backend name for this target.
    pub fn name(self) -> &'static str {
        match self {
            TextTarget::X86_64 => "X86_64",
            TextTarget::Aarch64 => "ARM64",
            TextTarget::Riscv64 => "RISCV64",
        }
    }

    /// Appends the directives that select this target's syntax, if any.
    pub fn prologue(self, ctx: &mut LowerCtx) {
        if self == TextTarget::X86_64 {
            // The dialect is destination-first, so print Intel syntax.
            ctx.emitter.put_str(".intel_syntax noprefix");
            ctx.emitter.put_str("");
        }
    }

    /// Returns this target's shared register file.
    pub fn regs(self) -> &'static offlineasm_ir::regs::TargetRegs {
        use offlineasm_ir::regs::{AARCH64, RISCV64, X86};
        match self {
            TextTarget::X86_64 => &X86,
            TextTarget::Aarch64 => &AARCH64,
            TextTarget::Riscv64 => &RISCV64,
        }
    }

    /// Returns this target's expansion scratch registers.
    pub fn scratch(self) -> offlineasm_ir::Scratch {
        self.regs().scratch
    }
}

/// Returns the assembler symbol for a label handle.
///
/// # Errors
///
/// Returns an error if `l` names a handle `ctx` never interned.
pub fn label_text(ctx: &LowerCtx, l: Lbl) -> Result<String, String> {
    match l {
        Lbl::Bound(h) => ctx
            .ir_labels
            .get(h.0 as usize)
            .cloned()
            .ok_or_else(|| format!("unknown label handle {}", h.0)),
        Lbl::Fresh(i) => ctx
            .ir_fresh
            .get(&i)
            .cloned()
            .ok_or_else(|| format!("unknown expansion label {}", i)),
    }
}

/// Returns the assembler symbol for an extern handle.
///
/// # Errors
///
/// Returns an error if `e` names a handle `ctx` never interned.
pub fn extern_text(ctx: &LowerCtx, e: ExternId) -> Result<String, String> {
    ctx.ir_externs
        .get(e.0 as usize)
        .cloned()
        .ok_or_else(|| format!("unknown extern handle {}", e.0))
}

/// Returns the label of the address-table slot holding extern `e`, emitting
/// the slot the first time: an 8-byte pointer in `.rdata`. COFF has no GOT
/// relocations, so far externs load their address from this slot instead,
/// with the same instructions a GOT load uses.
///
/// # Errors
///
/// Returns an error if `e` names a handle `ctx` never interned.
pub fn extern_slot(ctx: &mut LowerCtx, e: ExternId) -> Result<String, String> {
    if let Some(slot) = ctx.extern_slots.get(&e.0) {
        return Ok(slot.clone());
    }
    let symbol = extern_text(ctx, e)?;
    let slot = synth_name(ctx, "extern", e.0);
    ctx.emitter.puts(".pushsection .rdata, \"dr\"");
    ctx.emitter.puts(".p2align 3");
    ctx.emitter.put_str(&format!("{}:", slot));
    ctx.emitter.puts(&format!(".quad {}", symbol));
    ctx.emitter.puts(".popsection");
    ctx.extern_slots.insert(e.0, slot.clone());
    Ok(slot)
}

/// The error for an external symbol in an operand slot that does not take
/// one. The shared expansion rejects these shapes first, so a printer only
/// reaches this on a bug.
pub fn extern_operand_error() -> String {
    "an external symbol is only a `jmp`/`call` target or an address source".to_string()
}

/// Returns the assembler text for a symbolic operand slot (`{IDENT}`).
///
/// # Errors
///
/// Returns an error if `s` names a handle `ctx` never interned.
pub fn sym_text(ctx: &LowerCtx, s: SymId) -> Result<String, String> {
    ctx.ir_syms
        .get(s.0 as usize)
        .cloned()
        .ok_or_else(|| format!("unknown symbol handle {}", s.0))
}

/// Returns the decimal text of an immediate.
pub fn imm_text(v: i64) -> String {
    v.to_string()
}

/// Returns the text of a displacement: a signed decimal, or the `{IDENT}` symbol.
///
/// # Errors
///
/// Returns an error if `d` is a symbol handle `ctx` never interned.
pub fn disp_text(ctx: &LowerCtx, d: Disp) -> Result<String, String> {
    match d {
        Disp::Const(v) => Ok(v.to_string()),
        Disp::Sym(s) => sym_text(ctx, s),
    }
}

/// Reports whether `v` fits `bits` as a signed value.
pub fn fits_signed(v: i64, bits: u32) -> bool {
    match bits {
        8 => v == (v as i8) as i64,
        16 => v == (v as i16) as i64,
        32 => v == (v as i32) as i64,
        _ => true,
    }
}

/// Reports whether `v` fits `bits` as an unsigned value.
pub fn fits_unsigned(v: i64, bits: u32) -> bool {
    v >= 0 && (v as u64) >> bits == 0
}

/// Renders `v` as a signed offset term: `""`, `" + 8"`, or `" - 8"`.
pub fn offset_term(v: i64) -> String {
    if v == 0 {
        String::new()
    } else if v > 0 {
        format!(" + {}", v)
    } else {
        format!(" - {}", -v)
    }
}

/// Returns a symbol name no other label can collide with.
pub fn synth_name(ctx: &mut LowerCtx, tag: &str, id: u32) -> String {
    let uid = ctx.emitter.new_uid();
    ctx.local_symbol(&format!("__offlineasm_synth_{}_{}_{}", tag, uid, id))
}
