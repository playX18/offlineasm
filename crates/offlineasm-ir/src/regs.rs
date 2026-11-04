#![allow(non_upper_case_globals)]

//! Maps portable register names to per-target physical registers.
//!
//! [`TARGETS`] lists the three targets.

use crate::{Fpr, Gpr, Scratch};

/// Lists every portable general-purpose register spelling.
pub const GPRS: &[&str] = &[
    "t0",
    "t1",
    "t2",
    "t3",
    "t4",
    "t5",
    "t6",
    "t7",
    "t8",
    "t9",
    "t10",
    "t11",
    "t12",
    "cfr",
    "sp",
    "lr",
    "pc",
    "zr",
    "zero",
    "tp",
    "fp",
    "csr0",
    "csr1",
    "csr2",
    "csr3",
    "csr4",
    "csr5",
    "csr6",
    "csr7",
    "csr8",
    "csr9",
    "csr10",
    // AArch64 scratch-pool GPRs (`t13`-`t15` map to `x13`-`x15`). Appended at
    // the end so every pre-existing vreg id stays stable.
    "t13",
    "t14",
    "t15",
    "invalidGPR",
];

/// Lists every portable float register spelling.
pub const FPRS: &[&str] = &[
    "ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7", "csfr0", "csfr1", "csfr2", "csfr3",
    "csfr4", "csfr5", "csfr6", "csfr7", "csfr8", "csfr9", "csfr10", "csfr11",
    // x86 `ft8`-`ft15` map to `xmm8`-`xmm15`. Appended so existing ids stay
    // stable.
    "ft8", "ft9", "ft10", "ft11", "ft12", "ft13", "ft14", "ft15",
    // AArch64 64-bit views of `v8`-`v15` (the callee-saved `csfr0`-`csfr7`).
    "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
];

/// Lists every portable vector register spelling and lane alias.
pub const VECS: &[&str] = &[
    "v0", "v0_b", "v0_h", "v0_i", "v0_q", "v1", "v1_b", "v1_h", "v1_i", "v1_q", "v2", "v2_b",
    "v2_h", "v2_i", "v2_q", "v3", "v3_b", "v3_h", "v3_i", "v3_q", "v4", "v4_b", "v4_h", "v4_i",
    "v4_q", "v5", "v5_b", "v5_h", "v5_i", "v5_q", "v6", "v6_b", "v6_h", "v6_i", "v6_q", "v7",
    "v7_b", "v7_h", "v7_i", "v7_q",
    // Caller-saved AArch64 vector registers the Tier 2 pool uses. Appended so
    // existing vector ids stay stable.
    "v24", "v25", "v26", "v27", "v28", "v29", "v30",
];

/// Counts the entries of [`GPRS`].
pub const GPR_COUNT: u16 = GPRS.len() as u16;
/// Counts the entries of [`FPRS`] plus [`VECS`].
pub const FPR_COUNT: u16 = (FPRS.len() + VECS.len()) as u16;

const fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// Returns the vreg id for a GPR spelling.
///
/// The id is the index into [`GPRS`]. Returns `None` when `name` names no
/// GPR.
pub const fn gpr_id(name: &str) -> Option<u16> {
    let bytes = name.as_bytes();
    let mut i = 0;
    while i < GPRS.len() {
        if bytes_eq(GPRS[i].as_bytes(), bytes) {
            return Some(i as u16);
        }
        i += 1;
    }
    None
}

/// Returns the vreg id for an FPR or vector spelling.
///
/// The id is the index into [`FPRS`], followed by [`VECS`]. Returns `None`
/// when `name` names neither.
pub const fn fpr_id(name: &str) -> Option<u16> {
    let bytes = name.as_bytes();
    let mut i = 0;
    while i < FPRS.len() {
        if bytes_eq(FPRS[i].as_bytes(), bytes) {
            return Some(i as u16);
        }
        i += 1;
    }
    let mut j = 0;
    while j < VECS.len() {
        if bytes_eq(VECS[j].as_bytes(), bytes) {
            return Some((FPRS.len() + j) as u16);
        }
        j += 1;
    }
    None
}

/// Calls [`gpr_id`] in a `const` context, such as [`VReg::gpr`].
///
/// # Panics
///
/// Panics if `name` is not one of [`GPRS`]. Only call this on a spelling
/// known at compile time.
#[allow(clippy::panic)]
pub const fn gpr_id_const(name: &str) -> u16 {
    match gpr_id(name) {
        Some(id) => id,
        None => panic!("offlineasm-ir: unknown GPR spelling"),
    }
}

/// Calls [`fpr_id`] in a `const` context, such as [`VReg::fpr`].
///
/// # Panics
///
/// Panics if `name` is not one of [`FPRS`] or [`VECS`]. Only call this on a
/// spelling known at compile time.
#[allow(clippy::panic)]
pub const fn fpr_id_const(name: &str) -> u16 {
    match fpr_id(name) {
        Some(id) => id,
        None => panic!("offlineasm-ir: unknown FPR spelling"),
    }
}

/// Returns the GPR spelling for vreg id `id`, the inverse of [`gpr_id`].
pub fn gpr_name(id: u16) -> Option<&'static str> {
    GPRS.get(id as usize).copied()
}

/// Returns the FPR or vector spelling for vreg id `id`, the inverse of [`fpr_id`].
pub fn fpr_name(id: u16) -> Option<&'static str> {
    let id = id as usize;
    FPRS.get(id)
        .or_else(|| VECS.get(id.wrapping_sub(FPRS.len())))
        .copied()
}

/// Identifies a portable register by class and vreg id.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct VReg {
    id: u16,
    kind: RegKind,
}

/// Names a portable register class.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RegKind {
    /// General-purpose register (`t0`, `csr0`, `sp`, ...).
    Gpr,
    /// Floating-point/vector register (`ft0`, `csfr0`, `v0`, ...).
    Fpr,
}

impl VReg {
    /// Builds a GPR [`VReg`] from a spelling.
    ///
    /// # Panics
    ///
    /// Panics if `name` is not one of [`GPRS`].
    pub const fn gpr(name: &'static str) -> Self {
        Self {
            id: gpr_id_const(name),
            kind: RegKind::Gpr,
        }
    }

    /// Builds an FPR [`VReg`] from a spelling.
    ///
    /// # Panics
    ///
    /// Panics if `name` is not one of [`FPRS`] or [`VECS`].
    pub const fn fpr(name: &'static str) -> Self {
        Self {
            id: fpr_id_const(name),
            kind: RegKind::Fpr,
        }
    }

    /// Builds a GPR [`VReg`] from a vreg id.
    pub const fn gpr_id(id: u16) -> Self {
        Self {
            id,
            kind: RegKind::Gpr,
        }
    }

    /// Builds an FPR [`VReg`] from a vreg id.
    pub const fn fpr_id(id: u16) -> Self {
        Self {
            id,
            kind: RegKind::Fpr,
        }
    }

    /// Returns the vreg id of `self`.
    pub const fn id(self) -> u16 {
        self.id
    }

    /// Returns the class of `self`.
    pub const fn kind(self) -> RegKind {
        self.kind
    }

    /// Returns the portable spelling of `self`, or `"?"` when the id is unknown.
    pub fn name(self) -> &'static str {
        match self.kind {
            RegKind::Gpr => gpr_name(self.id),
            RegKind::Fpr => fpr_name(self.id),
        }
        .unwrap_or("?")
    }
}

/// Pairs a portable register name with its class.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RegInfo {
    /// Holds the portable spelling such as `t0` or `ft0`.
    pub name: &'static str,
    /// Holds the register class.
    pub class: RegKind,
}

impl RegInfo {
    /// Builds a GPR entry for `name`.
    pub const fn gpr(name: &'static str) -> Self {
        Self {
            name,
            class: RegKind::Gpr,
        }
    }

    /// Builds an FPR entry for `name`.
    pub const fn fpr(name: &'static str) -> Self {
        Self {
            name,
            class: RegKind::Fpr,
        }
    }
}

/// Lists one target's registers and default vreg mapping.
#[derive(Clone, Copy, Debug)]
pub struct TargetRegs {
    /// Target name (`x86_64`, `aarch64`, `riscv64`).
    pub name: &'static str,
    /// Scratch registers expansions may clobber.
    pub scratch: Scratch,
    /// Portable registers this target exposes.
    pub registers: &'static [RegInfo],
    /// Default physical GPR per vreg id.
    pub vreg_gpr: &'static [(u16, Gpr)],
    /// Default physical FPR per vreg id.
    pub vreg_fpr: &'static [(u16, Fpr)],
}

impl TargetRegs {
    /// Returns the default physical GPR for vreg id `id`.
    ///
    /// Returns `None` when `id` has no entry in this target's default map.
    pub fn resolve_gpr(&self, id: u16) -> Option<Gpr> {
        self.vreg_gpr
            .iter()
            .find(|&&(i, _)| i == id)
            .map(|&(_, g)| g)
    }

    /// Returns the default physical FPR for vreg id `id`.
    ///
    /// Returns `None` when `id` has no entry in this target's default map.
    pub fn resolve_fpr(&self, id: u16) -> Option<Fpr> {
        self.vreg_fpr
            .iter()
            .find(|&&(i, _)| i == id)
            .map(|&(_, f)| f)
    }

    /// Resolves a GPR by vreg spelling instead of id.
    pub fn resolve_gpr_name(&self, name: &str) -> Option<Gpr> {
        self.resolve_gpr(gpr_id(name)?)
    }

    /// Resolves an FPR by vreg spelling instead of id.
    pub fn resolve_fpr_name(&self, name: &str) -> Option<Fpr> {
        self.resolve_fpr(fpr_id(name)?)
    }
}

/// Looks up a target's register table by name.
///
/// Names are `"x86_64"`, `"aarch64"`, and `"riscv64"`, as listed in
/// [`TARGETS`]. Returns `None` for anything else.
pub fn target_regs(name: &str) -> Option<&'static TargetRegs> {
    TARGETS.iter().copied().find(|t| t.name == name)
}

/// Lists the register tables of all three targets.
pub static TARGETS: &[&TargetRegs] = &[&X86, &AARCH64, &RISCV64];

/// Describes the x86-64 registers and vreg mapping.
pub const X86: TargetRegs = TargetRegs {
    name: "x86_64",
    scratch: Scratch {
        gpr: Gpr(11),
        gpr2: Gpr(11),
        fpr: Fpr(7),
    },
    registers: X86_REGS,
    vreg_gpr: X86_VREG_GPR,
    vreg_fpr: X86_VREG_FPR,
};

/// Describes the AArch64 registers and vreg mapping.
pub const AARCH64: TargetRegs = TargetRegs {
    name: "aarch64",
    scratch: Scratch {
        gpr: Gpr(16),
        gpr2: Gpr(17),
        fpr: Fpr(31),
    },
    registers: AARCH64_REGS,
    vreg_gpr: AARCH64_VREG_GPR,
    vreg_fpr: AARCH64_VREG_FPR,
};

/// Describes the RISC-V 64 registers and vreg mapping.
pub const RISCV64: TargetRegs = TargetRegs {
    name: "riscv64",
    scratch: Scratch {
        gpr: Gpr(31),
        gpr2: Gpr(29),
        fpr: Fpr(31),
    },
    registers: RISCV64_REGS,
    vreg_gpr: RISCV64_VREG_GPR,
    vreg_fpr: RISCV64_VREG_FPR,
};

const X86_REGS: &[RegInfo] = &[
    RegInfo::gpr("t0"),
    RegInfo::gpr("t1"),
    RegInfo::gpr("t2"),
    RegInfo::gpr("t3"),
    RegInfo::gpr("t4"),
    RegInfo::gpr("t5"),
    RegInfo::gpr("t6"),
    RegInfo::gpr("t7"),
    RegInfo::gpr("csr0"),
    RegInfo::gpr("csr1"),
    RegInfo::gpr("csr2"),
    RegInfo::gpr("csr3"),
    RegInfo::gpr("csr4"),
    RegInfo::gpr("csr5"),
    RegInfo::gpr("csr6"),
    RegInfo::gpr("cfr"),
    RegInfo::gpr("sp"),
    RegInfo::fpr("ft0"),
    RegInfo::fpr("ft1"),
    RegInfo::fpr("ft2"),
    RegInfo::fpr("ft3"),
    RegInfo::fpr("ft4"),
    RegInfo::fpr("ft5"),
    RegInfo::fpr("ft6"),
    RegInfo::fpr("ft7"),
    RegInfo::fpr("ft8"),
    RegInfo::fpr("ft9"),
    RegInfo::fpr("ft10"),
    RegInfo::fpr("ft11"),
    RegInfo::fpr("ft12"),
    RegInfo::fpr("ft13"),
    RegInfo::fpr("ft14"),
    RegInfo::fpr("ft15"),
];

const X86_VREG_GPR: &[(u16, Gpr)] = &[
    (gpr_id_const("t0"), Gpr(0)),
    (gpr_id_const("t1"), Gpr(6)),
    (gpr_id_const("t2"), Gpr(2)),
    (gpr_id_const("t3"), Gpr(1)),
    (gpr_id_const("t4"), Gpr(8)),
    (gpr_id_const("t5"), Gpr(10)),
    (gpr_id_const("t6"), Gpr(7)),
    (gpr_id_const("t7"), Gpr(9)),
    (gpr_id_const("csr0"), Gpr(3)),
    (gpr_id_const("csr1"), Gpr(12)),
    (gpr_id_const("csr2"), Gpr(13)),
    (gpr_id_const("csr3"), Gpr(14)),
    (gpr_id_const("csr4"), Gpr(15)),
    (gpr_id_const("csr5"), Gpr(6)),
    (gpr_id_const("csr6"), Gpr(7)),
    (gpr_id_const("cfr"), Gpr(5)),
    (gpr_id_const("sp"), Gpr(4)),
];

const X86_VREG_FPR: &[(u16, Fpr)] = &[
    (fpr_id_const("ft0"), Fpr(0)),
    (fpr_id_const("ft1"), Fpr(1)),
    (fpr_id_const("ft2"), Fpr(2)),
    (fpr_id_const("ft3"), Fpr(3)),
    (fpr_id_const("ft4"), Fpr(4)),
    (fpr_id_const("ft5"), Fpr(5)),
    (fpr_id_const("ft6"), Fpr(6)),
    (fpr_id_const("ft7"), Fpr(7)),
    (fpr_id_const("v0"), Fpr(0)),
    (fpr_id_const("v0_b"), Fpr(0)),
    (fpr_id_const("v0_h"), Fpr(0)),
    (fpr_id_const("v0_i"), Fpr(0)),
    (fpr_id_const("v0_q"), Fpr(0)),
    (fpr_id_const("v1"), Fpr(1)),
    (fpr_id_const("v1_b"), Fpr(1)),
    (fpr_id_const("v1_h"), Fpr(1)),
    (fpr_id_const("v1_i"), Fpr(1)),
    (fpr_id_const("v1_q"), Fpr(1)),
    (fpr_id_const("v2"), Fpr(2)),
    (fpr_id_const("v2_b"), Fpr(2)),
    (fpr_id_const("v2_h"), Fpr(2)),
    (fpr_id_const("v2_i"), Fpr(2)),
    (fpr_id_const("v2_q"), Fpr(2)),
    (fpr_id_const("v3"), Fpr(3)),
    (fpr_id_const("v3_b"), Fpr(3)),
    (fpr_id_const("v3_h"), Fpr(3)),
    (fpr_id_const("v3_i"), Fpr(3)),
    (fpr_id_const("v3_q"), Fpr(3)),
    (fpr_id_const("v4"), Fpr(4)),
    (fpr_id_const("v4_b"), Fpr(4)),
    (fpr_id_const("v4_h"), Fpr(4)),
    (fpr_id_const("v4_i"), Fpr(4)),
    (fpr_id_const("v4_q"), Fpr(4)),
    (fpr_id_const("v5"), Fpr(5)),
    (fpr_id_const("v5_b"), Fpr(5)),
    (fpr_id_const("v5_h"), Fpr(5)),
    (fpr_id_const("v5_i"), Fpr(5)),
    (fpr_id_const("v5_q"), Fpr(5)),
    (fpr_id_const("v6"), Fpr(6)),
    (fpr_id_const("v6_b"), Fpr(6)),
    (fpr_id_const("v6_h"), Fpr(6)),
    (fpr_id_const("v6_i"), Fpr(6)),
    (fpr_id_const("v6_q"), Fpr(6)),
    (fpr_id_const("v7"), Fpr(7)),
    (fpr_id_const("v7_b"), Fpr(7)),
    (fpr_id_const("v7_h"), Fpr(7)),
    (fpr_id_const("v7_i"), Fpr(7)),
    (fpr_id_const("v7_q"), Fpr(7)),
    (fpr_id_const("ft8"), Fpr(8)),
    (fpr_id_const("ft9"), Fpr(9)),
    (fpr_id_const("ft10"), Fpr(10)),
    (fpr_id_const("ft11"), Fpr(11)),
    (fpr_id_const("ft12"), Fpr(12)),
    (fpr_id_const("ft13"), Fpr(13)),
    (fpr_id_const("ft14"), Fpr(14)),
    (fpr_id_const("ft15"), Fpr(15)),
];

const AARCH64_REGS: &[RegInfo] = &[
    RegInfo::gpr("t0"),
    RegInfo::gpr("t1"),
    RegInfo::gpr("t2"),
    RegInfo::gpr("t3"),
    RegInfo::gpr("t4"),
    RegInfo::gpr("t5"),
    RegInfo::gpr("t6"),
    RegInfo::gpr("t7"),
    RegInfo::gpr("t8"),
    RegInfo::gpr("t9"),
    RegInfo::gpr("t10"),
    RegInfo::gpr("t11"),
    RegInfo::gpr("t12"),
    RegInfo::gpr("t13"),
    RegInfo::gpr("t14"),
    RegInfo::gpr("t15"),
    RegInfo::gpr("csr0"),
    RegInfo::gpr("csr1"),
    RegInfo::gpr("csr2"),
    RegInfo::gpr("csr3"),
    RegInfo::gpr("csr4"),
    RegInfo::gpr("csr5"),
    RegInfo::gpr("csr6"),
    RegInfo::gpr("csr7"),
    RegInfo::gpr("csr8"),
    RegInfo::gpr("csr9"),
    RegInfo::gpr("cfr"),
    RegInfo::gpr("lr"),
    RegInfo::gpr("sp"),
    RegInfo::gpr("zr"),
    RegInfo::fpr("ft0"),
    RegInfo::fpr("ft1"),
    RegInfo::fpr("ft2"),
    RegInfo::fpr("ft3"),
    RegInfo::fpr("ft4"),
    RegInfo::fpr("ft5"),
    RegInfo::fpr("ft6"),
    RegInfo::fpr("ft7"),
    RegInfo::fpr("csfr0"),
    RegInfo::fpr("csfr1"),
    RegInfo::fpr("csfr2"),
    RegInfo::fpr("csfr3"),
    RegInfo::fpr("csfr4"),
    RegInfo::fpr("csfr5"),
    RegInfo::fpr("csfr6"),
    RegInfo::fpr("csfr7"),
    RegInfo::fpr("d8"),
    RegInfo::fpr("d9"),
    RegInfo::fpr("d10"),
    RegInfo::fpr("d11"),
    RegInfo::fpr("d12"),
    RegInfo::fpr("d13"),
    RegInfo::fpr("d14"),
    RegInfo::fpr("d15"),
    RegInfo::fpr("v24"),
    RegInfo::fpr("v25"),
    RegInfo::fpr("v26"),
    RegInfo::fpr("v27"),
    RegInfo::fpr("v28"),
    RegInfo::fpr("v29"),
    RegInfo::fpr("v30"),
];

const AARCH64_VREG_GPR: &[(u16, Gpr)] = &[
    (gpr_id_const("t0"), Gpr(0)),
    (gpr_id_const("t1"), Gpr(1)),
    (gpr_id_const("t2"), Gpr(2)),
    (gpr_id_const("t3"), Gpr(3)),
    (gpr_id_const("t4"), Gpr(4)),
    (gpr_id_const("t5"), Gpr(5)),
    (gpr_id_const("t6"), Gpr(6)),
    (gpr_id_const("t7"), Gpr(7)),
    (gpr_id_const("t8"), Gpr(8)),
    (gpr_id_const("t9"), Gpr(9)),
    (gpr_id_const("t10"), Gpr(10)),
    (gpr_id_const("t11"), Gpr(11)),
    (gpr_id_const("t12"), Gpr(12)),
    (gpr_id_const("t13"), Gpr(13)),
    (gpr_id_const("t14"), Gpr(14)),
    (gpr_id_const("t15"), Gpr(15)),
    (gpr_id_const("csr0"), Gpr(19)),
    (gpr_id_const("csr1"), Gpr(20)),
    (gpr_id_const("csr2"), Gpr(21)),
    (gpr_id_const("csr3"), Gpr(22)),
    (gpr_id_const("csr4"), Gpr(23)),
    (gpr_id_const("csr5"), Gpr(24)),
    (gpr_id_const("csr6"), Gpr(25)),
    (gpr_id_const("csr7"), Gpr(26)),
    (gpr_id_const("csr8"), Gpr(27)),
    (gpr_id_const("csr9"), Gpr(28)),
    (gpr_id_const("cfr"), Gpr(29)),
    (gpr_id_const("lr"), Gpr(30)),
    (gpr_id_const("sp"), Gpr(31)),
    (gpr_id_const("zr"), Gpr(63)),
];

const AARCH64_VREG_FPR: &[(u16, Fpr)] = &[
    (fpr_id_const("ft0"), Fpr(0)),
    (fpr_id_const("ft1"), Fpr(1)),
    (fpr_id_const("ft2"), Fpr(2)),
    (fpr_id_const("ft3"), Fpr(3)),
    (fpr_id_const("ft4"), Fpr(4)),
    (fpr_id_const("ft5"), Fpr(5)),
    (fpr_id_const("ft6"), Fpr(6)),
    (fpr_id_const("ft7"), Fpr(7)),
    (fpr_id_const("csfr0"), Fpr(8)),
    (fpr_id_const("csfr1"), Fpr(9)),
    (fpr_id_const("csfr2"), Fpr(10)),
    (fpr_id_const("csfr3"), Fpr(11)),
    (fpr_id_const("csfr4"), Fpr(12)),
    (fpr_id_const("csfr5"), Fpr(13)),
    (fpr_id_const("csfr6"), Fpr(14)),
    (fpr_id_const("csfr7"), Fpr(15)),
    (fpr_id_const("v0"), Fpr(16)),
    (fpr_id_const("v0_b"), Fpr(16)),
    (fpr_id_const("v0_h"), Fpr(16)),
    (fpr_id_const("v0_i"), Fpr(16)),
    (fpr_id_const("v0_q"), Fpr(16)),
    (fpr_id_const("v1"), Fpr(17)),
    (fpr_id_const("v1_b"), Fpr(17)),
    (fpr_id_const("v1_h"), Fpr(17)),
    (fpr_id_const("v1_i"), Fpr(17)),
    (fpr_id_const("v1_q"), Fpr(17)),
    (fpr_id_const("v2"), Fpr(18)),
    (fpr_id_const("v2_b"), Fpr(18)),
    (fpr_id_const("v2_h"), Fpr(18)),
    (fpr_id_const("v2_i"), Fpr(18)),
    (fpr_id_const("v2_q"), Fpr(18)),
    (fpr_id_const("v3"), Fpr(19)),
    (fpr_id_const("v3_b"), Fpr(19)),
    (fpr_id_const("v3_h"), Fpr(19)),
    (fpr_id_const("v3_i"), Fpr(19)),
    (fpr_id_const("v3_q"), Fpr(19)),
    (fpr_id_const("v4"), Fpr(20)),
    (fpr_id_const("v4_b"), Fpr(20)),
    (fpr_id_const("v4_h"), Fpr(20)),
    (fpr_id_const("v4_i"), Fpr(20)),
    (fpr_id_const("v4_q"), Fpr(20)),
    (fpr_id_const("v5"), Fpr(21)),
    (fpr_id_const("v5_b"), Fpr(21)),
    (fpr_id_const("v5_h"), Fpr(21)),
    (fpr_id_const("v5_i"), Fpr(21)),
    (fpr_id_const("v5_q"), Fpr(21)),
    (fpr_id_const("v6"), Fpr(22)),
    (fpr_id_const("v6_b"), Fpr(22)),
    (fpr_id_const("v6_h"), Fpr(22)),
    (fpr_id_const("v6_i"), Fpr(22)),
    (fpr_id_const("v6_q"), Fpr(22)),
    (fpr_id_const("v7"), Fpr(23)),
    (fpr_id_const("v7_b"), Fpr(23)),
    (fpr_id_const("v7_h"), Fpr(23)),
    (fpr_id_const("v7_i"), Fpr(23)),
    (fpr_id_const("v7_q"), Fpr(23)),
    (fpr_id_const("d8"), Fpr(8)),
    (fpr_id_const("d9"), Fpr(9)),
    (fpr_id_const("d10"), Fpr(10)),
    (fpr_id_const("d11"), Fpr(11)),
    (fpr_id_const("d12"), Fpr(12)),
    (fpr_id_const("d13"), Fpr(13)),
    (fpr_id_const("d14"), Fpr(14)),
    (fpr_id_const("d15"), Fpr(15)),
    (fpr_id_const("v24"), Fpr(24)),
    (fpr_id_const("v25"), Fpr(25)),
    (fpr_id_const("v26"), Fpr(26)),
    (fpr_id_const("v27"), Fpr(27)),
    (fpr_id_const("v28"), Fpr(28)),
    (fpr_id_const("v29"), Fpr(29)),
    (fpr_id_const("v30"), Fpr(30)),
];

const RISCV64_REGS: &[RegInfo] = &[
    RegInfo::gpr("t0"),
    RegInfo::gpr("t1"),
    RegInfo::gpr("t2"),
    RegInfo::gpr("t3"),
    RegInfo::gpr("t4"),
    RegInfo::gpr("t5"),
    RegInfo::gpr("t6"),
    RegInfo::gpr("t7"),
    RegInfo::gpr("t8"),
    RegInfo::gpr("t9"),
    RegInfo::gpr("t10"),
    RegInfo::gpr("csr0"),
    RegInfo::gpr("csr1"),
    RegInfo::gpr("csr2"),
    RegInfo::gpr("csr3"),
    RegInfo::gpr("csr4"),
    RegInfo::gpr("csr5"),
    RegInfo::gpr("csr6"),
    RegInfo::gpr("csr7"),
    RegInfo::gpr("csr8"),
    RegInfo::gpr("csr9"),
    RegInfo::gpr("csr10"),
    RegInfo::gpr("cfr"),
    RegInfo::gpr("fp"),
    RegInfo::gpr("lr"),
    RegInfo::gpr("sp"),
    RegInfo::gpr("tp"),
    RegInfo::gpr("zero"),
    RegInfo::fpr("ft0"),
    RegInfo::fpr("ft1"),
    RegInfo::fpr("ft2"),
    RegInfo::fpr("ft3"),
    RegInfo::fpr("ft4"),
    RegInfo::fpr("ft5"),
    RegInfo::fpr("ft6"),
    RegInfo::fpr("ft7"),
    RegInfo::fpr("csfr0"),
    RegInfo::fpr("csfr1"),
    RegInfo::fpr("csfr2"),
    RegInfo::fpr("csfr3"),
    RegInfo::fpr("csfr4"),
    RegInfo::fpr("csfr5"),
    RegInfo::fpr("csfr6"),
    RegInfo::fpr("csfr7"),
];

const RISCV64_VREG_GPR: &[(u16, Gpr)] = &[
    (gpr_id_const("t0"), Gpr(10)),
    (gpr_id_const("t1"), Gpr(11)),
    (gpr_id_const("t2"), Gpr(12)),
    (gpr_id_const("t3"), Gpr(13)),
    (gpr_id_const("t4"), Gpr(14)),
    (gpr_id_const("t5"), Gpr(15)),
    (gpr_id_const("t6"), Gpr(16)),
    (gpr_id_const("t7"), Gpr(17)),
    (gpr_id_const("t8"), Gpr(5)),
    (gpr_id_const("t9"), Gpr(6)),
    (gpr_id_const("t10"), Gpr(7)),
    (gpr_id_const("csr0"), Gpr(18)),
    (gpr_id_const("csr1"), Gpr(19)),
    (gpr_id_const("csr2"), Gpr(20)),
    (gpr_id_const("csr3"), Gpr(21)),
    (gpr_id_const("csr4"), Gpr(22)),
    (gpr_id_const("csr5"), Gpr(23)),
    (gpr_id_const("csr6"), Gpr(24)),
    (gpr_id_const("csr7"), Gpr(25)),
    (gpr_id_const("csr8"), Gpr(26)),
    (gpr_id_const("csr9"), Gpr(27)),
    (gpr_id_const("csr10"), Gpr(9)),
    (gpr_id_const("cfr"), Gpr(8)),
    (gpr_id_const("fp"), Gpr(8)),
    (gpr_id_const("lr"), Gpr(1)),
    (gpr_id_const("sp"), Gpr(2)),
    (gpr_id_const("tp"), Gpr(4)),
    (gpr_id_const("zero"), Gpr(0)),
];

const RISCV64_VREG_FPR: &[(u16, Fpr)] = &[
    (fpr_id_const("ft0"), Fpr(8)),
    (fpr_id_const("ft1"), Fpr(10)),
    (fpr_id_const("ft2"), Fpr(12)),
    (fpr_id_const("ft3"), Fpr(14)),
    (fpr_id_const("ft4"), Fpr(16)),
    (fpr_id_const("ft5"), Fpr(18)),
    (fpr_id_const("ft6"), Fpr(20)),
    (fpr_id_const("ft7"), Fpr(22)),
    (fpr_id_const("csfr0"), Fpr(1)),
    (fpr_id_const("csfr1"), Fpr(3)),
    (fpr_id_const("csfr2"), Fpr(5)),
    (fpr_id_const("csfr3"), Fpr(7)),
    (fpr_id_const("csfr4"), Fpr(9)),
    (fpr_id_const("csfr5"), Fpr(11)),
    (fpr_id_const("csfr6"), Fpr(13)),
    (fpr_id_const("csfr7"), Fpr(15)),
    (fpr_id_const("v0"), Fpr(0)),
    (fpr_id_const("v0_b"), Fpr(0)),
    (fpr_id_const("v0_h"), Fpr(0)),
    (fpr_id_const("v0_i"), Fpr(0)),
    (fpr_id_const("v0_q"), Fpr(0)),
    (fpr_id_const("v1"), Fpr(2)),
    (fpr_id_const("v1_b"), Fpr(2)),
    (fpr_id_const("v1_h"), Fpr(2)),
    (fpr_id_const("v1_i"), Fpr(2)),
    (fpr_id_const("v1_q"), Fpr(2)),
    (fpr_id_const("v2"), Fpr(4)),
    (fpr_id_const("v2_b"), Fpr(4)),
    (fpr_id_const("v2_h"), Fpr(4)),
    (fpr_id_const("v2_i"), Fpr(4)),
    (fpr_id_const("v2_q"), Fpr(4)),
    (fpr_id_const("v3"), Fpr(6)),
    (fpr_id_const("v3_b"), Fpr(6)),
    (fpr_id_const("v3_h"), Fpr(6)),
    (fpr_id_const("v3_i"), Fpr(6)),
    (fpr_id_const("v3_q"), Fpr(6)),
    (fpr_id_const("v4"), Fpr(24)),
    (fpr_id_const("v4_b"), Fpr(24)),
    (fpr_id_const("v4_h"), Fpr(24)),
    (fpr_id_const("v4_i"), Fpr(24)),
    (fpr_id_const("v4_q"), Fpr(24)),
    (fpr_id_const("v5"), Fpr(26)),
    (fpr_id_const("v5_b"), Fpr(26)),
    (fpr_id_const("v5_h"), Fpr(26)),
    (fpr_id_const("v5_i"), Fpr(26)),
    (fpr_id_const("v5_q"), Fpr(26)),
    (fpr_id_const("v6"), Fpr(28)),
    (fpr_id_const("v6_b"), Fpr(28)),
    (fpr_id_const("v6_h"), Fpr(28)),
    (fpr_id_const("v6_i"), Fpr(28)),
    (fpr_id_const("v6_q"), Fpr(28)),
    (fpr_id_const("v7"), Fpr(30)),
    (fpr_id_const("v7_b"), Fpr(30)),
    (fpr_id_const("v7_h"), Fpr(30)),
    (fpr_id_const("v7_i"), Fpr(30)),
    (fpr_id_const("v7_q"), Fpr(30)),
];

pub const t0: VReg = VReg::gpr("t0");
pub const t1: VReg = VReg::gpr("t1");
pub const t2: VReg = VReg::gpr("t2");
pub const t3: VReg = VReg::gpr("t3");
pub const t4: VReg = VReg::gpr("t4");
pub const t5: VReg = VReg::gpr("t5");
pub const t6: VReg = VReg::gpr("t6");
pub const t7: VReg = VReg::gpr("t7");
pub const t8: VReg = VReg::gpr("t8");
pub const t9: VReg = VReg::gpr("t9");
pub const t10: VReg = VReg::gpr("t10");
pub const t11: VReg = VReg::gpr("t11");
pub const t12: VReg = VReg::gpr("t12");
pub const t13: VReg = VReg::gpr("t13");
pub const t14: VReg = VReg::gpr("t14");
pub const t15: VReg = VReg::gpr("t15");
pub const cfr: VReg = VReg::gpr("cfr");
pub const sp: VReg = VReg::gpr("sp");
pub const fp: VReg = VReg::gpr("fp");
pub const lr: VReg = VReg::gpr("lr");
pub const tp: VReg = VReg::gpr("tp");
pub const pc: VReg = VReg::gpr("pc");
pub const zr: VReg = VReg::gpr("zr");
pub const zero: VReg = VReg::gpr("zero");
pub const csr0: VReg = VReg::gpr("csr0");
pub const csr1: VReg = VReg::gpr("csr1");
pub const csr2: VReg = VReg::gpr("csr2");
pub const csr3: VReg = VReg::gpr("csr3");
pub const csr4: VReg = VReg::gpr("csr4");
pub const csr5: VReg = VReg::gpr("csr5");
pub const csr6: VReg = VReg::gpr("csr6");
pub const csr7: VReg = VReg::gpr("csr7");
pub const csr8: VReg = VReg::gpr("csr8");
pub const csr9: VReg = VReg::gpr("csr9");
pub const csr10: VReg = VReg::gpr("csr10");

pub const ft0: VReg = VReg::fpr("ft0");
pub const ft1: VReg = VReg::fpr("ft1");
pub const ft2: VReg = VReg::fpr("ft2");
pub const ft3: VReg = VReg::fpr("ft3");
pub const ft4: VReg = VReg::fpr("ft4");
pub const ft5: VReg = VReg::fpr("ft5");
pub const ft6: VReg = VReg::fpr("ft6");
pub const ft7: VReg = VReg::fpr("ft7");
pub const ft8: VReg = VReg::fpr("ft8");
pub const ft9: VReg = VReg::fpr("ft9");
pub const ft10: VReg = VReg::fpr("ft10");
pub const ft11: VReg = VReg::fpr("ft11");
pub const ft12: VReg = VReg::fpr("ft12");
pub const ft13: VReg = VReg::fpr("ft13");
pub const ft14: VReg = VReg::fpr("ft14");
pub const ft15: VReg = VReg::fpr("ft15");
pub const d8: VReg = VReg::fpr("d8");
pub const d9: VReg = VReg::fpr("d9");
pub const d10: VReg = VReg::fpr("d10");
pub const d11: VReg = VReg::fpr("d11");
pub const d12: VReg = VReg::fpr("d12");
pub const d13: VReg = VReg::fpr("d13");
pub const d14: VReg = VReg::fpr("d14");
pub const d15: VReg = VReg::fpr("d15");
pub const csfr0: VReg = VReg::fpr("csfr0");
pub const csfr1: VReg = VReg::fpr("csfr1");
pub const csfr2: VReg = VReg::fpr("csfr2");
pub const csfr3: VReg = VReg::fpr("csfr3");
pub const csfr4: VReg = VReg::fpr("csfr4");
pub const csfr5: VReg = VReg::fpr("csfr5");
pub const csfr6: VReg = VReg::fpr("csfr6");
pub const csfr7: VReg = VReg::fpr("csfr7");
pub const csfr8: VReg = VReg::fpr("csfr8");
pub const csfr9: VReg = VReg::fpr("csfr9");
pub const csfr10: VReg = VReg::fpr("csfr10");
pub const csfr11: VReg = VReg::fpr("csfr11");

macro_rules! vec_consts {
    ($($name:ident),* $(,)?) => {
        $(pub const $name: VReg = VReg::fpr(stringify!($name));)*
    };
}
vec_consts!(
    v0, v0_b, v0_h, v0_i, v0_q, v1, v1_b, v1_h, v1_i, v1_q, v2, v2_b, v2_h, v2_i, v2_q, v3, v3_b,
    v3_h, v3_i, v3_q, v4, v4_b, v4_h, v4_i, v4_q, v5, v5_b, v5_h, v5_i, v5_q, v6, v6_b, v6_h, v6_i,
    v6_q, v7, v7_b, v7_h, v7_i, v7_q, v24, v25, v26, v27, v28, v29, v30,
);
