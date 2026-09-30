//! AArch64 `push`/`pop`: one 16-byte-aligned block per instruction, with the
//! operand layout of the 8-byte-slot targets (last operand at `[sp]`).

use offlineasm_backend::backends::Backend;
use offlineasm_backend::driver::{compile_str, CompileOptions};
use offlineasm_backend::parser::ParserOptions;

fn arm64(src: &str) -> Result<String, String> {
    let options = CompileOptions {
        backend: Some(Backend::Arm64),
        ..Default::default()
    };
    compile_str(src, "push-pop-fixture", &options, &ParserOptions::default())
        .map(|out| out.template)
        .map_err(|e| e.to_string())
}

/// The template's instruction lines, trimmed, without labels or directives.
fn lines(template: &str) -> Vec<String> {
    template
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.ends_with(':') && !l.starts_with('.'))
        .map(str::to_string)
        .collect()
}

#[test]
fn groups_keep_sp_aligned() {
    let template = arm64(
        "global _p\n_p:\n push t1, t2, t3\n pop t1, t2, t3\n push t0\n pop t0\n push t0, t1\n pop t0, t1\n ret",
    )
    .expect("compiles");
    let body = lines(&template);
    let want = [
        "stp x3, x2, [sp, #-32]!",
        "str x1, [sp, #16]",
        "ldr x1, [sp, #16]",
        "ldp x3, x2, [sp], #32",
        "str x0, [sp, #-16]!",
        "ldr x0, [sp], #16",
        "stp x1, x0, [sp, #-16]!",
        "ldp x1, x0, [sp], #16",
    ];
    for w in want {
        assert!(body.iter().any(|l| l == w), "missing `{w}` in:\n{template}");
    }
    assert!(!template.contains("#-8]!"), "no 8-byte pushes:\n{template}");
}

#[test]
fn immediates_stage_through_scratch() {
    let template = arm64("global _p\n_p:\n push 1, t0\n pop t1, t0\n ret").expect("compiles");
    assert!(template.contains("stp x0, x17, [sp, #-16]!"), "{template}");
}

#[test]
fn sp_relative_memory_is_rejected() {
    let err = arm64("global _p\n_p:\n push 8[sp]\n ret").expect_err("sp-relative push");
    assert!(err.contains("sp"), "{err}");
}
