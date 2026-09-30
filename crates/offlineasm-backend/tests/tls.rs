//! Thread-local slot lowering across backends.
//!
//! Pins the ergonomics added for `tls_*`: the width family, `tls_leap`,
//! and the per-OS segment choice (Linux/BSD `fs:` vs Windows `gs:` on
//! x86-64, `tpidr_el0` with no masking on AArch64, `tp` on RISC-V 64,
//! `Machine.tls` on rloop).

use offlineasm_backend::backends::Backend;
use offlineasm_backend::driver::{compile_str, CompileOptions};
use offlineasm_backend::parser::ParserOptions;

fn compile(backend: Backend, src: &str, platform: Option<&str>) -> String {
    let options = CompileOptions {
        backend: Some(backend),
        platform: platform.map(str::to_string),
        ..Default::default()
    };
    let out = compile_str(src, "tls-fixture", &options, &ParserOptions::default())
        .unwrap_or_else(|e| panic!("expected TLS fixture to compile: {e}"));
    out.template
}

const TLS_BODY: &str = r#"
    global _tlsProbe
    _tlsProbe:
        tls_loadp t0, 2
        tls_storep 3, t0
        tls_loadb t1, 4
        tls_storeh 5, t1
        tls_loadi t2, 6
        tls_leap t3, 1
        ret
"#;

#[test]
fn x86_uses_fs_by_default() {
    let template = compile(Backend::X86_64, TLS_BODY, None);
    assert!(
        template.contains("fs:["),
        "expected fs: segment, got:\n{template}"
    );
    assert!(
        !template.contains("gs:["),
        "must not use gs: by default, got:\n{template}"
    );
    assert!(
        template.contains("qword ptr fs:[16]"),
        "slot 2 is byte 16, got:\n{template}"
    );
    assert!(
        template.contains("byte ptr fs:[32]"),
        "tls_loadb width, got:\n{template}"
    );
    assert!(
        template.contains("word ptr fs:[40]"),
        "tls_storeh width, got:\n{template}"
    );
    assert!(
        template.contains("dword ptr fs:[48]"),
        "tls_loadi width, got:\n{template}"
    );
    assert!(
        template.contains("lea"),
        "tls_leap emits lea, got:\n{template}"
    );
}

#[test]
fn x86_uses_gs_on_windows() {
    let template = compile(Backend::X86_64, TLS_BODY, Some("Windows"));
    assert!(
        template.contains("gs:["),
        "expected gs: on Windows, got:\n{template}"
    );
    assert!(
        !template.contains("fs:["),
        "must not use fs: on Windows, got:\n{template}"
    );
}

#[test]
fn arm64_reads_tpidr_without_masking() {
    let template = compile(Backend::Arm64, TLS_BODY, None);
    assert!(
        template.contains("tpidr_el0"),
        "expected TPIDR_EL0 read, got:\n{template}"
    );
    assert!(
        !template.contains("bic"),
        "no masking of the thread pointer, got:\n{template}"
    );
    assert!(template.contains("ldrb"), "tls_loadb, got:\n{template}");
    assert!(template.contains("strh"), "tls_storeh, got:\n{template}");
}

#[test]
fn riscv64_reads_tp_directly() {
    let template = compile(Backend::Riscv64, TLS_BODY, None);
    assert!(
        template.contains("(x4)"),
        "expected tp-relative access, got:\n{template}"
    );
    assert!(
        !template.contains("tpidr"),
        "no system register on RISC-V, got:\n{template}"
    );
    assert!(template.contains("lbu"), "tls_loadb, got:\n{template}");
    assert!(template.contains("sh"), "tls_storeh, got:\n{template}");
}

#[test]
fn tls_aliases_assemble() {
    let src = r#"
    global _tlsAlias
    _tlsAlias:
        tls_loadq t0, 0
        tls_storeq 1, t0
        ret
"#;
    let template = compile(Backend::X86_64, src, None);
    assert!(
        template.contains("qword ptr fs:[0]"),
        "tls_loadq alias, got:\n{template}"
    );
    assert!(
        template.contains("qword ptr fs:[8]"),
        "tls_storeq alias, got:\n{template}"
    );
}
