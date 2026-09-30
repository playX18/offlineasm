//! The shared compiler behind `offlineasm!` (compile-time) and
//! `onlineasm!` (runtime).

pub mod ast;
pub mod backends;
pub mod code_origin;
pub mod config;
pub mod driver;
pub mod instructions;
pub mod offsets;
pub mod parser;
#[doc = include_str!("../docs/reference.md")]
pub mod reference;
pub mod registers;
pub mod settings;
pub mod transform;
