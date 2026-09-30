//! `offlineasm`: a portable assembler for x86-64, AArch64, and RISC-V 64.
//!
//! The [`offlineasm!`] macro parses offlineasm assembly at compile time.
//! With `backend = native` it emits `global_asm!()` for the target, and with
//! `backend = rloop` it emits a dispatch loop in Rust.
//!
//! [`offlineasm_include!`] includes a file and compiles it the same way.
//!
//! ```no_run
//! use offlineasm::offlineasm;
//!
//! offlineasm! {
//!     settings {
//!         backend = native,
//!     }
//!
//!     global _answer
//!     _answer:
//!         move t0, 42
//!         ret
//! }
//!
//! fn main() {}
//! ```
//!
//! Each `settings { ... }` entry maps an offlineasm setting to a Rust `cfg`
//! predicate, and a generated `macro_rules!` chain resolves it at compile
//! time, because a proc macro cannot evaluate `cfg(...)` itself. Without a
//! `settings` block the macro emits every valid combination behind its own
//! `#[cfg(...)]` guard.
//!
//! ## The rloop backend
//!
//! `backend = rloop` emits one `Opcode` enum per program and a trait the host
//! implements. [`crate::rt`] supplies the owned machine state: `Machine` with
//! its `Registers`. `push`/`pop` (and `peek`/`poke`) address memory at
//! `regs.sp` directly, just like `loadp`/`storep`, so the host must point
//! `sp` at a real stack buffer before running generated code.
//!
//! ```ignore
//! use offlineasm::rt::*;
//!
//! offlineasm! {
//!     settings {
//!         backend = rloop,
//!     }
//!
//!     global _answer
//!     _answer:
//!         move t0, 42
//!         ret
//! }
//! ```
//!
//! The generated labels call each other with `extern "rust-preserve-none"`,
//! so a crate that expands the macro with `backend = rloop` needs nightly
//! Rust and `#![feature(rust_preserve_none_cc)]`. The rest of this crate stays
//! on stable Rust.
//!
//! ## Instruction reference
//!
//! See [mod@reference].

pub mod rt;

#[doc = include_str!("../docs/reference.md")]
pub mod reference {}

#[allow(non_upper_case_globals, non_snake_case)]
pub mod mnem {
    include!(concat!(env!("OUT_DIR"), "/mnem.rs"));
}

pub use offlineasm_macros::{offlineasm, offlineasm_include};

#[doc(hidden)]
pub use offlineasm_macros::offlineasm_inner as __offlineasm_inner;
