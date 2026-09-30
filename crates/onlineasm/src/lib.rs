#![warn(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
// Lowering handlers take the shared context plus decoded operands. Bundling
// the parameters into a struct would obscure the 1:1 mapping with the
// mnemonic tables and add churn without improving safety.
#![allow(clippy::too_many_arguments)]

//! `onlineasm`: a minimal, portable runtime assembler.
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use onlineasm::{onlineasm, Assembler, JitAllocator, Target};
//!
//! let mut asm = Assembler::native();
//!
//! let (arg0, arg1) = match asm.target() {
//!     Target::X64 => (onlineasm::regs::t6, onlineasm::regs::t1),
//!     Target::AArch64 | Target::RISCV64 => (onlineasm::regs::t0, onlineasm::regs::t1),
//! };
//! onlineasm!(asm;
//!     =>add;
//!     move t0, {arg0};
//!     addq t0, {arg1};
//!     ret;
//! );
//! let code = asm.finish()?;
//! let entry = code.offset(add).ok_or("add is unbound")?;
//! let mut jit = JitAllocator::new(Default::default());
//! let span = code.allocate(&mut jit)?;
//! let f: extern "C" fn(u64, u64) -> u64 =
//!     unsafe { std::mem::transmute(span.rx().add(entry as usize)) };
//! assert_eq!(f(40, 2), 42);
//! # Ok(())
//! # }
//! ```
//!
//! ## External symbols
//!
//! Generated code references host functions and data by [`ExternalName`]
//! and resolves them when the code is loaded:
//!
//! ```ignore
//! let helper = ExternalName::user(0, 3);
//! onlineasm!(asm;
//!     call extern {helper.clone()};
//! );
//! let code = asm.finish()?.load(&mut jit, |name| {
//!     if *name == helper { helper_fn as *const u8 } else { std::ptr::null() }
//! })?;
//! ```
//!
//! A far extern ([`Assembler::extern_far`], `extern` in the macro) is reached
//! through an address table placed after the code, so it can be anywhere,
//! and [`LoadedCode::rebind`] binds it later. A near extern
//! ([`Assembler::extern_near`], `extern near`) is a direct PC-relative
//! reference and must be within the instruction's range of the code
//! (x86-64 and RISC-V 64: +/-2 GiB; AArch64 `bl`/`b`: +/-128 MiB, `adrp`:
//! +/-4 GiB); loading fails otherwise.
//!
//!
//! ## Instruction reference
//!
//! See [crate::reference].

use asmkit::{
    Arch, AsmError, CodeBuffer, CodeBufferFinalized, Environment, RelocDistance, RelocTarget, Span,
};
use offlineasm_ir::Lbl;

mod aarch64;
mod insn;
mod lower;
mod riscv64;
mod x86;

pub(crate) mod ir {
    pub use crate::lower::{LabelResolver, LowerError, PatchHandle};
    pub use offlineasm_ir::*;
}

pub use offlineasm_ir::regs;

#[doc = include_str!("../docs/reference.md")]
pub mod reference {}

#[allow(non_upper_case_globals, non_snake_case)]
pub mod mnem {
    include!(concat!(env!("OUT_DIR"), "/mnem.rs"));
}

pub use asmkit::{
    CodeLocationData, CodeLocationJump, DataLabel, ExternalName, JitAllocator, JitAllocatorOptions,
    LoadedCode, PatchableJump, ResetPolicy, UserExternalName,
};
pub use ir::{
    Disp, Extern, Fpr, Gpr, Label, LowerError, Mem, Mnemonic, Op, PatchHandle, Reach, Scratch,
    SymId, SUPPORTED_MNEMONICS,
};
pub use onlineasm_macros::onlineasm;
pub use regs::{RegInfo, RegKind, VReg};

/// Target for the assembler.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Target {
    /// x86-64.
    X64,
    /// AArch64.
    AArch64,
    /// RISC-V 64 (rv64gc).
    RISCV64,
}

#[allow(clippy::from_over_into)]
impl Into<Arch> for Target {
    fn into(self) -> Arch {
        match self {
            Self::AArch64 => Arch::AArch64,
            Self::RISCV64 => Arch::RISCV64,
            Self::X64 => Arch::X64,
        }
    }
}

impl Target {
    /// All supported targets.
    pub const ALL: [Target; 3] = [Target::X64, Target::AArch64, Target::RISCV64];

    /// Names of the callee-saved GPRs on this target under the
    /// default ABI (SystemV, AAPCS, RISCV64)
    pub const fn callee_saved_gprs(self) -> &'static [&'static str] {
        match self {
            Target::X64 => &["csr0", "csr1", "csr2", "csr3", "csr4"],
            Target::AArch64 => &[
                "csr0", "csr1", "csr2", "csr3", "csr4", "csr5", "csr6", "csr7", "csr8", "csr9",
            ],
            Target::RISCV64 => &[
                "csr0", "csr1", "csr2", "csr3", "csr4", "csr5", "csr6", "csr7", "csr8", "csr9",
                "csr10",
            ],
        }
    }

    /// Names of the callee-saved GPRs on this target under `abi`.
    pub const fn callee_saved_gprs_for(self, abi: Abi) -> &'static [&'static str] {
        match (self, abi) {
            (Target::X64, Abi::Windows) => {
                &["csr0", "csr1", "csr2", "csr3", "csr4", "csr5", "csr6"]
            }
            _ => self.callee_saved_gprs(),
        }
    }

    /// Names of the callee-saved FPRs on this target.
    pub const fn callee_saved_fprs(self) -> &'static [&'static str] {
        match self {
            Target::X64 => &[],
            Target::AArch64 => &[
                "csfr0", "csfr1", "csfr2", "csfr3", "csfr4", "csfr5", "csfr6", "csfr7",
            ],
            Target::RISCV64 => &[
                "csfr0", "csfr1", "csfr2", "csfr3", "csfr4", "csfr5", "csfr6", "csfr7",
            ],
        }
    }

    /// Names of the callee-saved FPRs on this target under `abi`.
    pub const fn callee_saved_fprs_for(self, abi: Abi) -> &'static [&'static str] {
        let _ = abi;
        self.callee_saved_fprs()
    }

    /// Returns the target matching the host architecture.
    ///
    /// # Panics
    ///
    /// Panics if host architecture is not supported.
    pub const fn native() -> Self {
        #[cfg(target_arch = "x86_64")]
        {
            Target::X64
        }
        #[cfg(target_arch = "aarch64")]
        {
            Target::AArch64
        }
        #[cfg(target_arch = "riscv64")]
        {
            Target::RISCV64
        }
        #[cfg(not(any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "riscv64"
        )))]
        {
            panic!("onlineasm: unsupported host architecture")
        }
    }

    pub const fn arch(self) -> Arch {
        match self {
            Target::X64 => Arch::X64,
            Target::AArch64 => Arch::AArch64,
            Target::RISCV64 => Arch::RISCV64,
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Target::X64 => "x86_64",
            Target::AArch64 => "aarch64",
            Target::RISCV64 => "riscv64",
        }
    }

    pub(crate) const fn info(self) -> &'static TargetInfo {
        match self {
            Target::X64 => &x86::INFO,
            Target::AArch64 => &aarch64::INFO,
            Target::RISCV64 => &riscv64::INFO,
        }
    }

    pub const fn registers(self) -> &'static [RegInfo] {
        self.info().registers
    }
}

impl std::fmt::Display for Target {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

pub(crate) type LowerFn =
    fn(&mut CodeBuffer, &Scratch, &[asmkit::Label], Mnemonic, &[Op], Abi) -> Result<(), LowerError>;

pub(crate) type LowerPatchedFn = fn(
    &mut CodeBuffer,
    &Scratch,
    &[asmkit::Label],
    Mnemonic,
    &[Op],
    Abi,
) -> Result<PatchHandle, LowerError>;

/// Per-target lowering hooks and register tables.
pub(crate) struct TargetInfo {
    pub(crate) scratch: Scratch,
    pub(crate) registers: &'static [RegInfo],
    pub(crate) vreg_gpr: &'static [(u16, Gpr)],
    pub(crate) vreg_fpr: &'static [(u16, Fpr)],
    pub(crate) lower: LowerFn,
    pub(crate) lower_patched: LowerPatchedFn,
}

fn lookup_gpr(table: &[(u16, Gpr)], id: u16) -> Option<Gpr> {
    table.iter().find(|&&(i, _)| i == id).map(|&(_, g)| g)
}

fn lookup_fpr(table: &[(u16, Fpr)], id: u16) -> Option<Fpr> {
    table.iter().find(|&&(i, _)| i == id).map(|&(_, v)| v)
}

fn reject_offlineasm_only(mnemonic: Mnemonic, ops: &[Op]) -> Result<(), LowerError> {
    let bad = |msg: &str| LowerError::BadOperand {
        mnemonic: mnemonic.as_str().to_string(),
        msg: msg.to_string(),
    };
    for op in ops {
        match op {
            Op::Sym(_) => return Err(bad("symbolic immediates are offlineasm-only")),
            Op::Mem(m) if m.disp.constant().is_none() => {
                return Err(bad("symbolic displacements are offlineasm-only"))
            }
            _ => {}
        }
    }
    Ok(())
}

/// Calling convention to use during code generation.
///
/// Call argument marshalling is not handled automatically, but the `csr` and
/// `csfr` register sets and the thread-local slot base depend on this. Only
/// x64 has more than one callee-saved set (Windows vs. SysV).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub enum Abi {
    /// System V ABI (AAPCS64 on AArch64).
    #[default]
    SysV,
    /// Windows x64 ABI.
    Windows,
    /// Apple platforms: the System V callee-saved sets (AAPCS64 on AArch64),
    /// with thread-local slots in the pthread TSD (`gs` on x64,
    /// `tpidrro_el0` on AArch64).
    Darwin,
}

impl Abi {
    /// Detects the ABI to use for `target` on this host.
    pub fn detect_for(target: Target) -> Self {
        let host = if cfg!(target_arch = "x86_64") {
            Some(Target::X64)
        } else if cfg!(target_arch = "aarch64") {
            Some(Target::AArch64)
        } else if cfg!(target_arch = "riscv64") {
            Some(Target::RISCV64)
        } else {
            None
        };
        if cfg!(target_os = "windows") && host == Some(target) && target == Target::X64 {
            Abi::Windows
        } else if cfg!(target_vendor = "apple") && host == Some(target) {
            Abi::Darwin
        } else {
            Abi::SysV
        }
    }
}

/// Configuration options for [`Assembler`].
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AssemblerOptions {
    /// Codegen environment (target plus CPU features).
    pub environment: Environment,
    /// Calling convention for the callee-saved sets.
    pub abi: Abi,
}

impl Default for AssemblerOptions {
    fn default() -> Self {
        Self {
            environment: Environment::host(),
            abi: Abi::detect_for(Target::native()),
        }
    }
}

impl AssemblerOptions {
    /// Detects the default options for `target` on this host.
    pub fn detected(target: Target) -> Self {
        Self {
            environment: Environment::new(target.into()),
            abi: Abi::detect_for(target),
        }
    }

    /// Overrides the environment.
    ///
    /// # Panics
    ///
    /// Panics for architectures other than x64, AArch64, and RISC-V 64.
    pub fn with_environment(mut self, env: Environment) -> Self {
        if !matches!(env.arch(), Arch::AArch64 | Arch::RISCV64 | Arch::X64) {
            todo!("unsupported architecture")
        }
        self.environment = env;
        self
    }

    /// Toggles position-independent code generation. With PIC on, every extern is reached through
    /// the address table, as if declared [`Reach::Far`]. offlineasm's `PIC`
    /// setting does the same.
    pub fn with_pic(mut self, pic: bool) -> Self {
        self.environment.set_pic(pic);
        self
    }

    /// Overrides the ABI.
    pub fn with_abi(mut self, abi: Abi) -> Self {
        self.abi = abi;
        self
    }

    /// Returns the target the environment encodes.
    pub fn target(&self) -> Target {
        match self.environment.arch() {
            Arch::AArch64 => Target::AArch64,
            Arch::RISCV64 => Target::RISCV64,
            Arch::X64 => Target::X64,
            _ => unreachable!(),
        }
    }
}

pub use asmkit;

/// Runtime assembler for onlineasm.
///
/// A wrapper over [`asmkit::CodeBuffer`] plus the data needed for emission.
///
/// NOTE: instruction documentation cannot be generated automatically, and to save time
/// most of the comments on scratches and instruction behaviour
/// are pasted from [`mod@reference`]. This process is manual at the moment, and
/// they could be outdated, consult reference if you want most up to date information.
pub struct Assembler {
    info: &'static TargetInfo,
    target: Target,
    buf: CodeBuffer,
    ctx: Scratch,
    labels: Vec<asmkit::Label>,
    externs: Vec<(ExternalName, Extern)>,
    abi: Abi,
}

impl Assembler {
    /// Creates an assembler for `target`.
    pub fn new(target: Target) -> Self {
        Self::with_options(AssemblerOptions::detected(target))
    }

    /// Creates an assembler for `target` with explicit [`AssemblerOptions`].
    pub fn with_options(options: AssemblerOptions) -> Self {
        let target = options.target();
        let info = target.info();
        Self {
            info,
            target,
            buf: CodeBuffer::new(options.environment),
            ctx: info.scratch,
            labels: Vec::new(),
            externs: Vec::new(),
            abi: options.abi,
        }
    }

    /// Declares external symbol `name`, reached as `reach`, and returns the
    /// operand naming it. Declaring the same name and reach again returns the
    /// same handle. Under [PIC](AssemblerOptions::with_pic) every extern is
    /// [`Reach::Far`], no matter what `reach` says.
    ///
    /// An [`Extern`] is a `jmp`/`call` target or the source of
    /// `move`/`leap`/`globaladdr`/`la` (its address). The code then has to
    /// be loaded with [`Finished::load`].
    pub fn extern_name(&mut self, name: impl Into<ExternalName>, reach: Reach) -> Extern {
        let name = name.into();
        let reach = if self.pic() { Reach::Far } else { reach };
        if let Some((_, ext)) = self
            .externs
            .iter()
            .find(|(n, e)| *n == name && e.reach == reach)
        {
            return *ext;
        }
        let distance = match reach {
            Reach::Near => RelocDistance::Near,
            Reach::Far => RelocDistance::Far,
        };
        let sym = self.buf.add_symbol(name.clone(), distance);
        let ext = Extern {
            id: ir::ExternId(sym.id()),
            reach,
        };
        self.externs.push((name, ext));
        ext
    }

    /// [`Assembler::extern_name`] with [`Reach::Far`].
    pub fn extern_far(&mut self, name: impl Into<ExternalName>) -> Extern {
        self.extern_name(name, Reach::Far)
    }

    /// [`Assembler::extern_name`] with [`Reach::Near`].
    pub fn extern_near(&mut self, name: impl Into<ExternalName>) -> Extern {
        self.extern_name(name, Reach::Near)
    }

    /// Returns the underlying code buffer.
    pub fn code_buffer(&self) -> &CodeBuffer {
        &self.buf
    }

    /// Returns the assembler's environment.
    pub fn environment(&self) -> &Environment {
        self.code_buffer().env()
    }

    /// Returns the assembler's ABI.
    pub const fn abi(&self) -> Abi {
        self.abi
    }

    /// Reports whether the assembler generates position-independent code
    /// ([`AssemblerOptions::with_pic`]).
    pub fn pic(&self) -> bool {
        self.environment().pic()
    }

    /// Creates an assembler for the host architecture.
    pub fn native() -> Self {
        Self::new(Target::native())
    }

    /// Returns the assembler's target.
    pub fn target(&self) -> Target {
        self.target
    }

    /// Returns the expansion scratch registers (`gpr`, `gpr2`, `fpr`).
    pub fn scratch(&self) -> Scratch {
        self.ctx
    }

    /// Resolves a portable GPR vreg to its physical register, or `None` when
    /// this target does not have it.
    pub fn try_vreg_gpr(&self, vreg: VReg) -> Option<Gpr> {
        (vreg.kind() == RegKind::Gpr)
            .then(|| lookup_gpr(self.info.vreg_gpr, vreg.id()))
            .flatten()
    }

    /// Resolves a portable FPR vreg to its physical register, or `None` when
    /// this target lacks it.
    pub fn try_vreg_fpr(&self, vreg: VReg) -> Option<Fpr> {
        (vreg.kind() == RegKind::Fpr)
            .then(|| lookup_fpr(self.info.vreg_fpr, vreg.id()))
            .flatten()
    }

    /// Resolves a portable GPR vreg to its physical register.
    ///
    /// # Panics
    ///
    /// Panics when the vreg is not a GPR or the target backend lacks it.
    #[allow(clippy::panic)]
    pub fn vreg_gpr(&self, vreg: VReg) -> Gpr {
        self.try_vreg_gpr(vreg).unwrap_or_else(|| {
            panic!(
                "onlineasm: cannot use register `{}` on {}",
                vreg.name(),
                self.target
            )
        })
    }

    /// Resolves a portable FPR vreg to its physical register.
    ///
    /// # Panics
    ///
    /// Panics when the vreg is not an FPR or the target backend lacks it.
    #[allow(clippy::panic)]
    pub fn vreg_fpr(&self, vreg: VReg) -> Fpr {
        self.try_vreg_fpr(vreg).unwrap_or_else(|| {
            panic!(
                "onlineasm: cannot use register `{}` on {}",
                vreg.name(),
                self.target
            )
        })
    }

    /// Creates a new label.
    pub fn label(&mut self) -> Label {
        let l = self.buf.get_label();
        self.labels.push(l);
        Label(self.labels.len() as u32 - 1)
    }

    #[allow(clippy::panic)]
    fn asm_label(&self, label: Label) -> asmkit::Label {
        match self.labels.get(label.0 as usize) {
            Some(&l) => l,
            None => panic!("onlineasm: label handle does not belong to this assembler"),
        }
    }

    /// Binds a label at the current position.
    ///
    /// # Panics
    ///
    /// Panics if `label` belongs to another assembler.
    pub fn bind(&mut self, label: Label) {
        let l = self.asm_label(label);
        self.buf.bind_label(l);
    }

    /// Returns the current byte offset of a label, or `u32::MAX` when it is
    /// not bound yet. On x86-64 this is best effort: [`Assembler::finish`]
    /// shrinks jumps to rel8 where they reach, which moves the code after
    /// them. Finalized offsets are available through [`Finished::offset`].
    ///
    /// # Panics
    ///
    /// Panics if `label` belongs to another assembler.
    pub fn offset(&self, label: Label) -> u32 {
        self.buf.label_offset(self.asm_label(label))
    }

    /// Pads with architecture `nop`s until the next emitted instruction is
    /// aligned to `alignment` bytes (a power of two).
    ///
    /// # Panics
    ///
    /// Panics when `alignment` is not a power of two.
    pub fn align(&mut self, alignment: u32) {
        assert!(
            alignment.is_power_of_two(),
            "onlineasm: alignment {alignment} is not a power of two"
        );
        if self.target == Target::X64 {
            self.buf.align_to(alignment);
            return;
        }
        while self.buf.cur_offset() & (alignment - 1) != 0 {
            let before = self.buf.cur_offset();
            if self.emit(Mnemonic::Nop, &[]).is_err() {
                unreachable!("the built-in `nop` lowering cannot fail");
            }
            assert!(
                self.buf.cur_offset() > before,
                "onlineasm: `nop` did not advance the buffer"
            );
        }
    }

    /// Embeds `data` in the image and returns the label naming it.
    /// Reference its address with `leap reg, {label}`, then load its
    /// contents through `reg` (`loadq dst, [reg]`). The data is appended at
    /// the current position as a constant island (16-byte aligned
    /// for payloads over 8 bytes, 8-byte otherwise), so code must jump
    /// over it.
    ///
    /// # Panics
    ///
    /// Panics when the buffer already failed.
    pub fn embed_data(&mut self, data: &[u8]) -> Label {
        let constant = self.buf.add_constant(data.to_vec());
        self.labels.push(self.buf.get_label_for_constant(constant));
        Label(self.labels.len() as u32 - 1)
    }

    /// Converts `v` into an assembler operand.
    pub fn op(&self, v: impl IntoOperand) -> Op {
        v.into_operand(self)
    }

    /// Builds a `[base + disp]` memory operand (resolving a portable base).
    ///
    /// # Panics
    ///
    /// Panics when `base` does not resolve to a general-purpose register.
    pub fn mem(&self, base: impl IntoOperand, disp: i32) -> Mem {
        Mem {
            base: Some(self.gpr_operand(base)),
            index: None,
            disp: Disp::Const(disp),
        }
    }

    /// Builds a `[base + index*scale + disp]` memory operand.
    ///
    /// # Panics
    ///
    /// Panics when `base`/`index` do not resolve to general-purpose
    /// registers, or when `scale` is not 1, 2, 4, or 8.
    pub fn mem_indexed(
        &self,
        base: impl IntoOperand,
        index: impl IntoOperand,
        scale: u8,
        disp: i32,
    ) -> Mem {
        assert!(
            matches!(scale, 1 | 2 | 4 | 8),
            "scale must be 1, 2, 4, or 8"
        );
        Mem {
            base: Some(self.gpr_operand(base)),
            index: Some((self.gpr_operand(index), scale)),
            disp: Disp::Const(disp),
        }
    }

    #[allow(clippy::panic)]
    fn gpr_operand(&self, v: impl IntoOperand) -> Gpr {
        match v.into_operand(self) {
            Op::Gpr(g) => g,
            other => panic!("onlineasm: expected a register operand, got {other:?}"),
        }
    }

    /// Emits one onlineasm mnemonic.
    ///
    /// # Errors
    ///
    /// Returns an error if the mnemonic is offlineasm-only or lowering fails.
    pub fn emit(&mut self, mnemonic: Mnemonic, ops: &[Op]) -> Result<(), LowerError> {
        reject_offlineasm_only(mnemonic, ops)?;
        (self.info.lower)(
            &mut self.buf,
            &self.ctx,
            &self.labels,
            mnemonic,
            ops,
            self.abi,
        )
    }

    #[allow(clippy::panic)]
    fn emit_checked(&mut self, mnemonic: Mnemonic, ops: &[Op]) {
        if let Err(e) = self.emit(mnemonic, ops) {
            panic!("onlineasm: lowering `{mnemonic}` failed: {e}");
        }
    }

    /// Emits one onlineasm mnemonic and returns its patch handle.
    ///
    /// # Errors
    ///
    /// Returns an error if the mnemonic is offlineasm-only, lowering fails,
    /// or the mnemonic is not patchable.
    pub fn emit_patched(
        &mut self,
        mnemonic: Mnemonic,
        ops: &[Op],
    ) -> Result<PatchHandle, LowerError> {
        reject_offlineasm_only(mnemonic, ops)?;
        (self.info.lower_patched)(
            &mut self.buf,
            &self.ctx,
            &self.labels,
            mnemonic,
            ops,
            self.abi,
        )
    }

    /// Finalizes the code buffer.
    ///
    /// # Errors
    ///
    /// Returns an error if finalization fails.
    pub fn finish(mut self) -> Result<Finished, AsmError> {
        self.buf.emit_island(u32::MAX)?;
        let labels = std::mem::take(&mut self.labels);
        let inner = self.buf.finish()?;
        let offsets: Vec<u32> = labels.iter().map(|l| inner.label_offset(*l)).collect();
        Ok(Finished {
            inner,
            offsets,
            linked: false,
        })
    }
}

impl Default for Assembler {
    fn default() -> Self {
        Self::native()
    }
}

/// A finalized machine-code image plus the offsets of the labels.
pub struct Finished {
    inner: CodeBufferFinalized,
    offsets: Vec<u32>,
    linked: bool,
}

/// Where a [`PatchHandle`] is in a [`Finished`] image.
#[derive(Clone, Copy, Debug)]
pub enum PatchLocation {
    /// A jump or call, retargeted with [`asmkit::repatch_jump_span`].
    Jump(CodeLocationJump),
    /// An immediate, rewritten with [`repatch_u64`].
    Data(CodeLocationData),
}

impl Finished {
    /// Returns the machine-code bytes.
    pub fn data(&self) -> &[u8] {
        self.inner.data()
    }

    /// Returns the final byte offset of a label, or `None` when it was never
    /// bound or belongs to another image.
    pub fn offset(&self, label: Label) -> Option<u32> {
        match self.offsets.get(label.0 as usize) {
            Some(&off) if off != u32::MAX => Some(off),
            _ => None,
        }
    }

    /// Returns where a [`PatchHandle`] returned while assembling
    /// (`#[patch = h]` or [`Assembler::emit_patched`]) is in this image, or
    /// `None` for a linked image, whose handles are not preserved.
    pub fn location(&self, handle: PatchHandle) -> Option<PatchLocation> {
        if self.linked {
            return None;
        }
        Some(match handle {
            PatchHandle::Jump(jump) => PatchLocation::Jump(self.inner.location_of(jump)),
            PatchHandle::Data(data) => PatchLocation::Data(self.inner.location_of(data)),
        })
    }

    /// Loads the image into executable memory.
    ///
    /// # Errors
    ///
    /// Returns an error if the image references externs (load it with
    /// [`Finished::load`] instead) or the JIT allocation fails.
    pub fn allocate(&self, jit: &mut JitAllocator) -> Result<Span, AsmError> {
        if self.has_externs() {
            return Err(AsmError::InvalidState);
        }
        self.inner.allocate(jit)
    }

    /// Reports whether the image references external symbols.
    pub fn has_externs(&self) -> bool {
        self.inner
            .relocs()
            .iter()
            .any(|r| matches!(r.target, RelocTarget::Sym(_)))
    }

    /// Loads the image into executable memory, resolving each external
    /// symbol through `resolve`. Far externs get a slot in an address table
    /// placed after the code, which [`LoadedCode::rebind`] can repoint.
    ///
    /// # Errors
    ///
    /// Returns an error if `resolve` returns null for a name, a near extern
    /// is out of its instruction's range, or the JIT allocation fails.
    pub fn load(
        &self,
        jit: &mut JitAllocator,
        resolve: impl Fn(&ExternalName) -> *const u8,
    ) -> Result<LoadedCode, AsmError> {
        self.inner.load(jit, resolve)
    }

    /// Links finalized images into one. Label and patch handles from the
    /// individual images are not preserved (their offsets move).
    ///
    /// # Errors
    ///
    /// Returns an error if `images` is empty or linking fails.
    pub fn link(images: impl IntoIterator<Item = Finished>) -> Result<Finished, AsmError> {
        let mut linker = asmkit::Linker::new();
        let mut any = false;
        for image in images {
            linker.add_buffer(image.inner);
            any = true;
        }
        if !any {
            return Err(AsmError::NoCodeGenerated);
        }
        Ok(Finished {
            inner: linker.link()?,
            offsets: Vec::new(),
            linked: true,
        })
    }

    /// Returns the underlying asmkit image.
    pub fn inner(&self) -> &CodeBufferFinalized {
        &self.inner
    }
}

/// Writes `value` into the immediate at `location`.
///
/// # Errors
///
/// Returns an error if `location` is a jump, or `value` does not fit the
/// immediate.
///
/// # Safety
///
/// `span` must hold the image `location` came from, and no thread may run
/// the patched instruction while it is rewritten.
pub unsafe fn repatch_u64(
    jit: &mut JitAllocator,
    span: &mut Span,
    location: &PatchLocation,
    value: u64,
) -> Result<(), AsmError> {
    let PatchLocation::Data(data) = *location else {
        return Err(AsmError::InvalidArgument);
    };
    // SAFETY: forwarded from the caller.
    unsafe { asmkit::repatch_value_span(jit, span, data, value) }
}

/// Converts a Rust value into an assembler operand.
pub trait IntoOperand {
    /// Converts `self` into an operand, resolving vregs against `asm`.
    fn into_operand(self, asm: &Assembler) -> Op;
}

impl IntoOperand for Op {
    fn into_operand(self, _asm: &Assembler) -> Op {
        self
    }
}

macro_rules! imm_operand {
    ($($t:ty),* $(,)?) => {
        $(impl IntoOperand for $t {
            fn into_operand(self, _asm: &Assembler) -> Op {
                Op::Imm(self as i64)
            }
        })*
    };
}
imm_operand!(i8, i16, i32, i64, u8, u16, u32, u64, isize, usize);

impl IntoOperand for Gpr {
    fn into_operand(self, _asm: &Assembler) -> Op {
        Op::Gpr(self)
    }
}

impl IntoOperand for Fpr {
    fn into_operand(self, _asm: &Assembler) -> Op {
        Op::Fpr(self)
    }
}

impl IntoOperand for Mem {
    fn into_operand(self, _asm: &Assembler) -> Op {
        Op::Mem(self)
    }
}

impl IntoOperand for Extern {
    fn into_operand(self, _asm: &Assembler) -> Op {
        Op::Extern(self)
    }
}

impl IntoOperand for Label {
    fn into_operand(self, _asm: &Assembler) -> Op {
        Op::Label(Lbl::Bound(self))
    }
}

impl IntoOperand for VReg {
    fn into_operand(self, asm: &Assembler) -> Op {
        match self.kind() {
            RegKind::Gpr => Op::Gpr(asm.vreg_gpr(self)),
            RegKind::Fpr => Op::Fpr(asm.vreg_fpr(self)),
        }
    }
}

impl<T: IntoOperand + Copy> IntoOperand for &T {
    fn into_operand(self, asm: &Assembler) -> Op {
        (*self).into_operand(asm)
    }
}
