use offlineasm_ir::regs::{self, fpr_id, gpr_id};
pub use offlineasm_ir::regs::{FPRS, GPRS, VECS};

/// Reports whether `name` is a portable GPR spelling.
pub fn is_gpr(name: &str) -> bool {
    GPRS.contains(&name)
}

/// Reports whether `name` is a portable FPR spelling.
pub fn is_fpr(name: &str) -> bool {
    FPRS.contains(&name)
}

/// Reports whether `name` is a portable vector spelling.
pub fn is_vec(name: &str) -> bool {
    VECS.contains(&name)
}

/// Reports whether `name` is any portable register spelling.
pub fn is_register_name(name: &str) -> bool {
    is_gpr(name) || is_fpr(name) || is_vec(name)
}

use crate::ast::Node;

/// Names whether a register survives a call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SaveClass {
    /// Holds a value the caller must spill around a call.
    CallerSaved,
    /// Holds a value that survives a call.
    CalleeSaved,
    /// Names no register on this target.
    Unmapped,
}

/// Names the calling convention for callee-saved queries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Abi {
    /// Selects the System V AMD64 ABI.
    ///
    /// ARM64 and RISC-V always use this ABI.
    #[default]
    SysV,
    /// Selects the Microsoft x64 calling convention.
    Windows,
}

impl Abi {
    /// Returns `sysv` or `windows`.
    pub fn as_str(self) -> &'static str {
        match self {
            Abi::SysV => "sysv",
            Abi::Windows => "windows",
        }
    }
}

/// Holds one row of the callee-saved table.
///
/// Each row lists the portable `csr*`/`csfr*` ids that survive a call for one
/// target and ABI. A new ABI is one entry.
struct CalleeSaved {
    backend: &'static str,
    abi: Abi,
    gprs: &'static [u16],
    fprs: &'static [u16],
}

/// Holds the callee-saved sets per target and ABI.
///
/// Only x86-64 distinguishes ABIs here. The RISC-V and AArch64 rows use
/// `SysV`, the only ABI those targets run under in this crate.
const CALLEE_SAVED: &[CalleeSaved] = &[
    CalleeSaved {
        backend: "X86_64",
        abi: Abi::SysV,
        gprs: &[
            regs::csr0.id(),
            regs::csr1.id(),
            regs::csr2.id(),
            regs::csr3.id(),
            regs::csr4.id(),
        ],
        fprs: &[],
    },
    CalleeSaved {
        backend: "X86_64",
        abi: Abi::Windows,
        gprs: &[
            regs::csr0.id(),
            regs::csr1.id(),
            regs::csr2.id(),
            regs::csr3.id(),
            regs::csr4.id(),
            regs::csr5.id(),
            regs::csr6.id(),
        ],
        fprs: &[],
    },
    CalleeSaved {
        backend: "ARM64",
        abi: Abi::SysV,
        gprs: &[
            regs::csr0.id(),
            regs::csr1.id(),
            regs::csr2.id(),
            regs::csr3.id(),
            regs::csr4.id(),
            regs::csr5.id(),
            regs::csr6.id(),
            regs::csr7.id(),
            regs::csr8.id(),
            regs::csr9.id(),
        ],
        fprs: &[
            regs::csfr0.id(),
            regs::csfr1.id(),
            regs::csfr2.id(),
            regs::csfr3.id(),
            regs::csfr4.id(),
            regs::csfr5.id(),
            regs::csfr6.id(),
            regs::csfr7.id(),
        ],
    },
    CalleeSaved {
        backend: "RISCV64",
        abi: Abi::SysV,
        gprs: &[
            regs::csr0.id(),
            regs::csr1.id(),
            regs::csr2.id(),
            regs::csr3.id(),
            regs::csr4.id(),
            regs::csr5.id(),
            regs::csr6.id(),
            regs::csr7.id(),
            regs::csr8.id(),
            regs::csr9.id(),
            regs::csr10.id(),
        ],
        fprs: &[
            regs::csfr0.id(),
            regs::csfr1.id(),
            regs::csfr2.id(),
            regs::csfr3.id(),
            regs::csfr4.id(),
            regs::csfr5.id(),
            regs::csfr6.id(),
            regs::csfr7.id(),
            regs::csfr8.id(),
            regs::csfr9.id(),
            regs::csfr10.id(),
            regs::csfr11.id(),
        ],
    },
];

/// Returns the `CALLEE_SAVED` row for `backend`.
///
/// Matches `abi` only where a backend has more than one row.
fn callee_saved_row(backend: &str, abi: Abi) -> Option<&'static CalleeSaved> {
    CALLEE_SAVED
        .iter()
        .find(|row| row.backend == backend && (row.backend != "X86_64" || row.abi == abi))
}

/// Returns the ABI label for `backend`.
///
/// Returns `None` for unknown backends.
pub fn backend_abi(backend: &str, abi: Abi) -> Option<&'static str> {
    match backend {
        "X86_64" => Some(abi.as_str()),
        "ARM64" | "ARM64E" => Some("aapcs64"),
        "RISCV64" => Some("riscv"),
        _ => None,
    }
}

/// Lists the physical callee-saved GPR names for an ABI label.
pub fn abi_callee_saved_gprs(abi: &str) -> &'static [&'static str] {
    match abi {
        "sysv" => &["rbx", "rsp", "rbp", "r12", "r13", "r14", "r15"],
        "windows" => &[
            "rbx", "rsp", "rbp", "rsi", "rdi", "r12", "r13", "r14", "r15",
        ],
        "aapcs64" => &[
            "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29", "sp",
        ],
        "riscv" => &[
            "x2", "x8", "x9", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27",
        ],
        _ => &[],
    }
}

/// Lists the physical callee-saved FPR names for an ABI label.
pub fn abi_callee_saved_fprs(abi: &str) -> &'static [&'static str] {
    match abi {
        "windows" => &[
            "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15",
        ],
        "aapcs64" => &["d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"],
        "riscv" => &[
            "f8", "f9", "f18", "f19", "f20", "f21", "f22", "f23", "f24", "f25", "f26", "f27",
        ],
        _ => &[],
    }
}

/// Returns the stack alignment in bytes for an ABI label.
pub fn abi_stack_align(abi: &str) -> Option<u32> {
    match abi {
        "sysv" | "windows" | "aapcs64" | "riscv" => Some(16),
        _ => None,
    }
}

/// Returns the portable callee-saved GPR ids for `backend` and `abi`.
pub fn callee_saved_gprs(backend: &str, abi: Abi) -> &'static [u16] {
    let backend = if backend == "ARM64E" {
        "ARM64"
    } else {
        backend
    };
    callee_saved_row(backend, abi).map_or(&[], |row| row.gprs)
}

/// Returns the portable callee-saved FPR ids for `backend` and `abi`.
pub fn callee_saved_fprs(backend: &str, abi: Abi) -> &'static [u16] {
    let backend = if backend == "ARM64E" {
        "ARM64"
    } else {
        backend
    };
    callee_saved_row(backend, abi).map_or(&[], |row| row.fprs)
}

/// Lists the portable GPR ids the RLOOP interpreter maps.
const RLOOP_GPR_IDS: &[u16] = &[
    regs::t0.id(),
    regs::t1.id(),
    regs::t2.id(),
    regs::t3.id(),
    regs::t4.id(),
    regs::t5.id(),
    regs::t6.id(),
    regs::t7.id(),
    regs::csr0.id(),
    regs::csr1.id(),
    regs::csr2.id(),
    regs::csr3.id(),
    regs::cfr.id(),
    regs::lr.id(),
    regs::sp.id(),
];

/// Lists the portable FPR ids the RLOOP interpreter maps.
const RLOOP_FPR_IDS: &[u16] = &[
    regs::ft0.id(),
    regs::ft1.id(),
    regs::ft2.id(),
    regs::ft3.id(),
    regs::ft4.id(),
    regs::ft5.id(),
    regs::ft6.id(),
    regs::ft7.id(),
];

fn gpr_mapped(backend: &str, name: &str) -> bool {
    if let Some(t) = target_regs(backend) {
        return t.resolve_gpr_name(name).is_some();
    }
    match backend {
        "RLOOP" => gpr_id(name).is_some_and(|id| RLOOP_GPR_IDS.contains(&id)),
        _ => false,
    }
}

fn fpr_mapped(backend: &str, name: &str) -> bool {
    if let Some(t) = target_regs(backend) {
        return t.resolve_fpr_name(name).is_some();
    }
    match backend {
        "RLOOP" => fpr_id(name).is_some_and(|id| RLOOP_FPR_IDS.contains(&id)),
        _ => false,
    }
}

/// Returns the IR register table for `backend`.
///
/// Returns `None` for `RLOOP` and unknown backends.
pub fn target_regs(backend: &str) -> Option<&'static offlineasm_ir::regs::TargetRegs> {
    match backend {
        "X86_64" => Some(&offlineasm_ir::regs::X86),
        "ARM64" | "ARM64E" => Some(&offlineasm_ir::regs::AARCH64),
        "RISCV64" => Some(&offlineasm_ir::regs::RISCV64),
        _ => None,
    }
}

/// Returns the physical callee-saved GPR numbers for `backend` and `abi`.
pub fn callee_saved_gpr_ids(backend: &str, abi: Abi) -> Vec<u8> {
    let Some(t) = target_regs(backend) else {
        return Vec::new();
    };
    callee_saved_gprs(backend, abi)
        .iter()
        .filter_map(|&id| t.resolve_gpr(id).map(|g| g.0))
        .collect()
}

/// Returns the save class of GPR `name` on `backend` and `abi`.
pub fn gpr_save_class(backend: &str, abi: Abi, name: &str) -> SaveClass {
    if let Some(id) = gpr_id(name) {
        if callee_saved_gprs(backend, abi).contains(&id) {
            return SaveClass::CalleeSaved;
        }
    }
    if gpr_mapped(backend, name) {
        return SaveClass::CallerSaved;
    }
    SaveClass::Unmapped
}

/// Returns the save class of FPR `name` on `backend` and `abi`.
pub fn fpr_save_class(backend: &str, abi: Abi, name: &str) -> SaveClass {
    if let Some(id) = fpr_id(name) {
        if callee_saved_fprs(backend, abi).contains(&id) {
            return SaveClass::CalleeSaved;
        }
    }
    if fpr_mapped(backend, name) {
        return SaveClass::CallerSaved;
    }
    SaveClass::Unmapped
}

/// Checks that every operand is a GPR callee-saved on `backend` under `abi`.
///
/// # Errors
///
/// Returns an error if any operand is not a `Node::Register`, or names a
/// register that is not callee-saved on `backend`.
pub fn check_callee_saved_gprs(backend: &str, abi: Abi, operands: &[Node]) -> Result<(), String> {
    for op in operands {
        match op {
            Node::Register { name, .. } => {
                if gpr_save_class(backend, abi, name) != SaveClass::CalleeSaved {
                    return Err(format!("{name} is not callee-saved on {backend}"));
                }
            }
            _ => return Err("callee-save helpers take GPRs only".to_string()),
        }
    }
    Ok(())
}
