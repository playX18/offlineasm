//! AArch64 `add`/`sub` with `sp` as the right-hand register operand.
//!
//! The GNU/LLVM assembler rejects `sp` as `Rm` outright (`ADD`/`SUB
//! (shifted register)` only ever decodes that field as `xzr`/`wzr`; `sp`
//! is valid only as `Rn`), so `subq t0, sp`, `addq t0, sp`, and `subq t1,
//! t0, sp` used to emit unassemblable text like `sub x0, x0, sp`.
//! Confirmed with `clang --target=aarch64-unknown-linux-musl -c` (a
//! plain GNU `as` was not on this host).

use offlineasm_backend::backends::Backend;
use offlineasm_backend::driver::{compile_str, CompileOptions};
use offlineasm_backend::parser::ParserOptions;

fn arm64(src: &str) -> Result<String, String> {
    let options = CompileOptions {
        backend: Some(Backend::Arm64),
        ..Default::default()
    };
    compile_str(
        src,
        "sp-operand-fixture",
        &options,
        &ParserOptions::default(),
    )
    .map(|out| out.template)
    .map_err(|e| e.to_string())
}

/// `add` is commutative: no scratch needed, just swap operands so `sp`
/// lands in `Rn`.
#[test]
fn add_swaps_sp_into_rn() {
    let template = arm64("global _p\n_p:\n addq t0, sp\n ret\n").expect("compiles");
    assert!(
        template.contains("add x0, sp, x0"),
        "expected `sp` swapped into Rn:\n{template}"
    );
    assert_no_add_sub_with_sp_as_rm(&template);
}

/// No `add`/`sub` line ends in `, sp` (a plain `mov x.., sp` staging line
/// is fine; only the ALU op's own operand list matters).
fn assert_no_add_sub_with_sp_as_rm(template: &str) {
    for line in template.lines().map(str::trim) {
        if (line.starts_with("add") || line.starts_with("sub")) && line.ends_with(", sp") {
            panic!("add/sub with `sp` as Rm:\n{line}\nin:\n{template}");
        }
    }
}

/// `sub` is not commutative: `sp` stages through a scratch GPR first.
#[test]
fn sub_stages_sp_through_scratch() {
    let template = arm64("global _p\n_p:\n subq t0, sp\n ret\n").expect("compiles");
    let body: Vec<&str> = template.lines().map(str::trim).collect();
    assert!(
        body.contains(&"mov x17, sp"),
        "expected `sp` staged through x17:\n{template}"
    );
    assert!(
        body.contains(&"sub x0, x0, x17"),
        "expected the subtract to use the staged copy:\n{template}"
    );
}

/// The 3-operand form (`sp` as the rightmost/`Rm` source) gets the same
/// treatment.
#[test]
fn sub3_stages_sp_through_scratch() {
    let template = arm64("global _p\n_p:\n subq t1, t0, sp\n ret\n").expect("compiles");
    assert!(
        template.contains("mov x17, sp"),
        "expected `sp` staged through x17:\n{template}"
    );
    assert_no_add_sub_with_sp_as_rm(&template);
}

/// `sp` as the *left* operand (`Rn`) was always valid and must stay
/// untouched by the new right-hand-side handling.
#[test]
fn sp_as_lhs_is_unaffected() {
    let template = arm64("global _p\n_p:\n subq t0, sp, t1\n ret\n").expect("compiles");
    assert!(
        template.contains("sub x0, sp, x1"),
        "expected a direct sub with `sp` as Rn:\n{template}"
    );
    assert!(
        !template.contains("mov x17, sp") && !template.contains("mov x16, sp"),
        "no staging needed when `sp` is already Rn:\n{template}"
    );
}
