//! Defines the target-independent IR for offlineasm mnemonics, shared by
//! the `offlineasm` and `onlineasm` assemblers.
//!
//! This crate is the single place where mnemonic *algorithms* live. Both
//! assemblers run the same front half:
//!
//! ```text
//! spelling -`Mnemonic`-> `expand()` + `Op`s -> [`Expansion`] -backend-> machine code | asm text
//! ```
//!
//! * [`Mnemonic`] names the *operation*, one variant per operation rather than
//!   one per spelling: `addp`/`addq` are the same value, and `mnem` holds one
//!   constant per accepted spelling. [`Mnemonic::from_str`] is the crate's
//!   only string comparison, and each frontend calls it once per instruction.
//! * [`expand()`] turns one [`Mnemonic`] plus its `Op`s into core [`Inst`]
//!   nodes.
//!   Multi-instruction sequences (`truncatef2q`'s bias path,
//!   `cq2f`'s halving path, `bcd2i`, ...) are expanded here once, using only
//!   core nodes plus internal labels, so every backend inherits them.
//! * Backends implement the core [`Inst`] variants with their ISA. Adding a
//!   new backend means implementing `Inst`, never re-deriving 400+
//!   mnemonics. `onlineasm`'s backends (`x86`/`aarch64`/`riscv64`) emit
//!   machine code; `offlineasm`'s backends emit assembly text.
//!
//! # Operand order
//!
//! Mnemonics read destination first: `move dst, src`, and `addq dst, lhs,
//! rhs` means `dst = lhs + rhs`. Branches and tests have no destination, so
//! they keep `lhs, rhs, lbl` / `value, lbl`. Sources keep their relative
//! order after the destination.
//!
//! # Registers
//!
//! [`Gpr`]/[`Fpr`] hold architecture physical numbers (x86 `rax = 0`,
//! aarch64 `x0 = 0`, riscv `x10 = 10`, ...). Name resolution (offlineasm vreg
//! to number, including the per-arch default maps) lives in [`regs`], so both
//! frontends share one vocabulary.
//!
//! # Labels and symbols
//!
//! [`Label`] and [`SymId`] are opaque handles: each frontend owns a table
//! and interprets the index its own way (`onlineasm` holds asmkit label
//! handles and `offlineasm` holds symbol text). The IR never names either.
//!
//! # Implicit pairs
//!
//! A few nodes name no explicit register for ISA-implicit operands and use
//! the *accumulator convention* instead: the dividend/quotient lives in the
//! `t0` role, the high half / CAS expected value in the `t2` role
//! (x86 `rax`/`rdx`, aarch64 `x0`/`x2`, riscv `x10`/`x12`). Each backend maps
//! the roles to its own registers. User code keeps `t0`/`t2` mapped at their
//! ABI homes (as the default maps do).
//!
//! # Pending flags
//!
//! `*S` ALU nodes ([`Inst::AluS`]) and every compare/test leave *pending
//! flags*. [`Inst::FlagBranch`] and [`Inst::Adc`]/[`Inst::Sbb`] consume
//! them. Nodes from one mnemonic expansion run back-to-back, so the
//! state is always well-defined there. Across mnemonics it matches existing
//! usage (`bo`/`bs`/`bz`/`bnz` directly after a flag-setting op). RISC-V has
//! no flags: its backend materializes the predicate into a reserved scratch
//! register, which nothing else clobbers.

/// Names a general-purpose register by its architecture physical number.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Gpr(pub u8);

/// Names a floating-point or vector register by its architecture physical number.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Fpr(pub u8);

/// Identifies a code label with a frontend-owned handle.
///
/// The frontend owns the meaning: `onlineasm` maps the index to an asmkit
/// label handle, `offlineasm` to a symbol name. The same handle appears in
/// operands ([`Op::Label`]) and at [`Inst::Bind`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Label(pub u32);

/// Identifies a symbolic operand with a frontend-owned handle.
///
/// Only `offlineasm` produces these, for offsets it cannot fold to an
/// integer at compile time: the frontend renders the index as the assembler
/// template's `{IDENT}` placeholder. `onlineasm` has no symbolic operands
/// and rejects them.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SymId(pub u32);

/// Identifies an external symbol with a frontend-owned handle.
///
/// `onlineasm` maps the index to an asmkit symbol (an `ExternalName`),
/// `offlineasm` to the symbol's assembler text.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ExternId(pub u32);

/// Says how generated code reaches an external symbol.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Reach {
    /// A direct PC-relative reference. The symbol must be within the
    /// instruction's range of the code.
    Near,
    /// Through a pointer-sized slot in an address table next to the code,
    /// so the symbol can be anywhere.
    Far,
}

/// Refers to an external symbol.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Extern {
    pub id: ExternId,
    pub reach: Reach,
}

/// Refers to a code label. `Bound` comes from the frontend (a concrete
/// handle). `Fresh` labels are created by [`expand()`] for internal
/// sequences and are scoped to one expansion. Backends must resolve them
/// per mnemonic lowering.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Lbl {
    Bound(Label),
    Fresh(u32),
}

/// Holds a memory displacement: a folded constant or a frontend-owned symbol.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Disp {
    Const(i32),
    /// Holds `{IDENT}` in the `offlineasm` text template. `onlineasm` and
    /// RISC-style backends that must fold it reject this variant.
    Sym(SymId),
}

impl Disp {
    /// Returns the constant value, or `None` when symbolic.
    pub const fn constant(self) -> Option<i32> {
        match self {
            Disp::Const(v) => Some(v),
            Disp::Sym(_) => None,
        }
    }

    /// Returns the constant value, treating a symbolic displacement as `0`.
    ///
    /// Machine-code backends call this only after rejecting `Disp::Sym`.
    pub const fn const_or_zero(self) -> i32 {
        match self {
            Disp::Const(v) => v,
            Disp::Sym(_) => 0,
        }
    }
}

/// Holds a resolved machine address: `disp(base, index, scale)`.
/// Every backend lowers this. RISC backends synthesize the index/scale part
/// with the expansion scratch registers.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Mem {
    /// Holds the base register. `None` selects the absolute (`[disp]`) form:
    /// x86-64 encodes it directly, AArch64 and RISC-V 64 materialize the
    /// address into a scratch register.
    pub base: Option<Gpr>,
    /// Holds the index register and scale, when present.
    pub index: Option<(Gpr, u8)>,
    /// Holds the displacement.
    pub disp: Disp,
}

impl Mem {
    /// Builds `[base + disp]`.
    pub fn base(base: Gpr, disp: i32) -> Self {
        Self {
            base: Some(base),
            index: None,
            disp: Disp::Const(disp),
        }
    }

    /// Builds `[disp]`, with no base register.
    pub fn absolute(disp: Disp) -> Self {
        Self {
            base: None,
            index: None,
            disp,
        }
    }

    /// Returns the base register, or register 0 for the absolute form.
    ///
    /// Backends check [`Mem::base`] for the absolute form first and only
    /// call this on a based address.
    pub fn base_reg(&self) -> Gpr {
        self.base.unwrap_or(Gpr(0))
    }
}

/// Holds one operand of a mnemonic invocation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Op {
    Imm(i64),
    Gpr(Gpr),
    Fpr(Fpr),
    Mem(Mem),
    Label(Lbl),
    Sym(SymId),
    /// Only `call`, `jmp`, `move`, and the `lea` family accept it.
    Extern(Extern),
}

impl Op {
    /// Reports whether `self` is the immediate `0`.
    pub fn is_zero_imm(&self) -> bool {
        matches!(self, Op::Imm(0))
    }
}

/// Names an integer operand width.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Width {
    B8,
    B16,
    B32,
    B64,
}

impl Width {
    /// Returns the width in bytes.
    pub fn bytes(self) -> u32 {
        match self {
            Width::B8 => 1,
            Width::B16 => 2,
            Width::B32 => 4,
            Width::B64 => 8,
        }
    }

    /// Reports whether `v` fits in `self` as a signed value.
    pub fn fits(self, v: i64) -> bool {
        match self {
            Width::B8 => v == (v as i8) as i64,
            Width::B16 => v == (v as i16) as i64,
            Width::B32 => v == (v as i32) as i64,
            Width::B64 => true,
        }
    }
}

/// Names a scalar float kind.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FKind {
    F32,
    F64,
}

/// Names an integer comparison condition.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum IntCc {
    /// Equal.
    Eq,
    /// Not equal.
    Ne,
    /// Unsigned above (`>`, x86 `a`).
    Hi,
    /// Unsigned above-or-equal (`>=`, x86 `ae`).
    Hs,
    /// Unsigned below (`<`, x86 `b`).
    Lo,
    /// Unsigned below-or-equal (`<=`, x86 `be`).
    Ls,
    /// Signed greater-than.
    Gt,
    /// Signed greater-or-equal.
    Ge,
    /// Signed less-than.
    Lt,
    /// Signed less-or-equal.
    Le,
}

/// Names a float comparison condition.
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FCc {
    /// Equal.
    Eq,
    /// Not equal.
    Ne,
    /// Greater than.
    Gt,
    /// Greater than or equal.
    Ge,
    /// Less than.
    Lt,
    /// Less than or equal.
    Le,
    /// Unordered-or-equal (x86 `je` after `ucomi*`).
    EqUn,
    /// Unordered-or-not-equal.
    NeUn,
    /// Unordered-or-greater.
    GtUn,
    /// Unordered-or-greater-or-equal.
    GeUn,
    /// Unordered-or-less.
    LtUn,
    /// Unordered-or-less-or-equal.
    LeUn,
}

/// Names a pending-flag predicate.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PredFlag {
    /// Overflow (x86 `o`, ARM `vs`).
    O,
    /// Sign / minus (x86 `s`, ARM `mi`).
    S,
    /// Zero / equal (x86 `z`, ARM `eq`).
    Z,
    /// Not-zero (x86 `nz`, ARM `ne`).
    Nz,
}

/// Names a value test.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TestKind {
    /// Sign bit set (`bts*`, `t*s`).
    Sign,
    /// Whole value zero (`bt*z`, `t*z`).
    Zero,
    /// Whole value nonzero (`bt*nz`, `t*nz`).
    NonZero,
}

/// Names a shift or rotate operation.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ShiftOp {
    /// Shift left.
    Shl,
    /// Shift right, sign-extending.
    ShrSar,
    /// Shift right, zero-filling.
    Shr,
    /// Rotate left.
    Rotl,
    /// Rotate right.
    Rotr,
}

/// Names a float rounding mode.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum RoundMode {
    /// To nearest.
    Nearest,
    /// Toward negative infinity.
    Down,
    /// Toward positive infinity.
    Up,
    /// Toward zero.
    Trunc,
}

/// Names a jump or call target.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Target {
    Label(Lbl),
    Reg(Gpr),
    Mem(Mem),
    Abs(i64),
    Extern(Extern),
}

/// Supplies the scratch registers an expansion may use.
#[derive(Clone, Copy, Debug)]
pub struct Scratch {
    /// First scratch GPR.
    pub gpr: Gpr,
    /// Second scratch GPR.
    pub gpr2: Gpr,
    /// Scratch FPR.
    pub fpr: Fpr,
}

/// Reports a mnemonic expansion failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpandError {
    /// Unknown mnemonic spelling.
    UnknownMnemonic(String),
    /// Wrong operand count or kind.
    BadOperand { mnemonic: String, msg: String },
    /// Patch requested on a non-patchable mnemonic.
    NotPatchable(String),
}

impl ExpandError {
    /// Replaces the mnemonic spelling carried by `self`.
    pub fn renamed(self, spelling: &str) -> Self {
        match self {
            ExpandError::UnknownMnemonic(_) => ExpandError::UnknownMnemonic(spelling.to_string()),
            ExpandError::BadOperand { msg, .. } => ExpandError::BadOperand {
                mnemonic: spelling.to_string(),
                msg,
            },
            ExpandError::NotPatchable(_) => ExpandError::NotPatchable(spelling.to_string()),
        }
    }
}

impl std::fmt::Display for ExpandError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpandError::UnknownMnemonic(m) => write!(f, "unknown mnemonic `{}`", m),
            ExpandError::BadOperand { mnemonic, msg } => {
                write!(f, "`{}`: bad operand: {}", mnemonic, msg)
            }
            ExpandError::NotPatchable(m) => {
                write!(
                    f,
                    "`{}` cannot be a patch site (use jmp/call/branch/move-imm)",
                    m
                )
            }
        }
    }
}

impl std::error::Error for ExpandError {}

pub mod expand;
pub mod inst;
pub mod mnemonic;
pub mod regs;
pub mod riscv;

pub use expand::{
    aligned_push_bytes, aligned_push_offset, check_callee_saved, expand, patch_kind, Expansion,
    PatchKind,
};
pub use inst::*;
pub use mnemonic::{mnem, LeaForm, Mnemonic, SUPPORTED_MNEMONICS};
pub use regs::{RegInfo, RegKind, TargetRegs, VReg, TARGETS};

// Layout budget: emission keeps one expansion inline on the stack, so the IR
// node types must stay small. These fire at compile time when a change grows
// past what `Expansion` was sized for; grow `EXPANSION_INLINE` or accept the
// spill consciously instead of deleting them.
const _: () = {
    assert!(
        core::mem::size_of::<Op>() <= 16,
        "Op grew past the 16-byte inline budget"
    );
    assert!(
        core::mem::size_of::<Inst>() <= 72,
        "Inst grew past the 72-byte inline budget"
    );
    assert!(
        core::mem::size_of::<BranchArgs>() <= 56,
        "BranchArgs grew past the 56-byte inline budget"
    );
};
