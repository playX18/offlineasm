//! Characterization tests for the `syn`-based parser (`offlineasm_backend::parser`).
//!
//! Each fixture exercises one grammar construct end-to-end through
//! `parse_data`. These are not a byte-for-byte port of a pre-existing
//! suite (the crate had none before this rewrite); they were written
//! alongside the new parser to pin its observable behavior.

use offlineasm_backend::parser::{parse_data, ParseSession};

fn parse_ok(src: &str) -> offlineasm_backend::ast::Node {
    let mut session = ParseSession::new(Default::default());
    parse_data(src, "fixture", &mut session)
        .unwrap_or_else(|e| panic!("expected {:?} to parse, got: {}", src, e))
}

fn parse_err(src: &str) -> syn::Error {
    let mut session = ParseSession::new(Default::default());
    parse_data(src, "fixture", &mut session).expect_err("expected a parse error")
}

/// The `offlineasm!{...}` body from `examples/rloop.rs`, minus the
/// `settings {...}` preamble (which `offlineasm-macros` strips before
/// calling into this parser, not part of its grammar).
const RLOOP_BODY: &str = r#"
    macro prologue()
        push cfr
        subq sp, 8
    end

    macro epilogue()
        addq sp, 8
        pop cfr
    end

    global _rloopSum
    _rloopSum:
        prologue()
        move t0, 0
        move t1, 10
    .loop:
        addi t0, t1
        subi t1, 1
        btinz t1, .loop
        epilogue()
        ret
"#;

#[test]
fn rloop_example_body_parses() {
    let node = parse_ok(RLOOP_BODY);
    let dump = node.dump();
    assert!(dump.contains("macro prologue()"));
    assert!(dump.contains("_rloopSum:"));
    assert!(dump.contains(".loop:"));
    assert!(dump.contains("btinz"));
}

#[test]
fn const_decl_form_parses() {
    let node = parse_ok("const FOO = 4\nmove t0, FOO");
    assert!(node.dump().contains("const FOO = 4"));
}

#[test]
fn const_block_form_parses() {
    let node = parse_ok("move t0, const { 1 + 2 }");
    assert!(node.dump().contains("const {"));
}

#[test]
fn const_block_keeps_dollar_param_unexpanded() {
    // A macro body referencing its own parameter inside a `const {...}`
    // block: the raw tokens (including `$n`) are captured as-is by the
    // parser; substitution is `transform`'s job at macro-instantiation
    // time, not the parser's.
    let node = parse_ok("macro m(n)\n    move t0, const { $n + 1 }\nend");
    let dump = node.dump();
    assert!(dump.contains("const {"));
}

#[test]
fn macro_with_params_and_call_parses() {
    let node = parse_ok("macro add(a, b)\n    addi a, b\nend\nadd(t0, t1)");
    let dump = node.dump();
    assert!(dump.contains("macro add(a, b)"));
    assert!(dump.contains("add(t0, t1)"));
}

#[test]
fn if_elsif_else_chain_parses() {
    let node = parse_ok(
        "if X86_64\n    move t0, 1\nelsif ARM64\n    move t0, 2\nelse\n    move t0, 3\nend",
    );
    let dump = node.dump();
    assert!(dump.contains("if"));
}

#[test]
fn label_reference_with_offset_folds_via_add() {
    // The parser itself always emits `offset: 0`; a trailing `+ N` is a
    // separate `Add` node that `transform::fold` later merges into the
    // label reference's offset. Confirm the parser at least accepts the
    // syntax and produces the expected shape.
    let node = parse_ok("la t0, _foo\nla t1, _foo + 4");
    let dump = node.dump();
    assert!(dump.contains("_foo"));
}

#[test]
fn base_index_and_absolute_address_parse() {
    // `[]` (empty brackets after an expression) is offlineasm's absolute
    // address form; `[base, index, scale]` is base-index.
    let node = parse_ok("loadp t0, [t1, t2, 8]\nloadp t0, [t1]\nloadp t0, 100[]");
    let dump = node.dump();
    assert!(dump.contains("[t1, t2, 8]") || dump.contains("t1, t2, 8"));
}

#[test]
fn ordinary_comments_are_ignored() {
    // `#`-line-comments and `// text`-as-output-annotation are both
    // dropped features (see `parser.rs`'s module doc); only plain `//`
    // and `/* */` Rust-style comments remain, and they're silently
    // discarded by `proc_macro2`'s own tokenizer.
    let node =
        parse_ok("// a leading comment\nmove t0, 1 // a trailing comment\n/* block */ move t1, 2");
    let dump = node.dump();
    assert!(dump.contains("move t0, 1"));
    assert!(dump.contains("move t1, 2"));
}

#[test]
fn malformed_snippet_reports_a_useful_span() {
    let err = parse_err("move t0, @@@");
    // The error must point at (or after) the bad token, not just at
    // some generic call-site span with no location info.
    let line = err.span().start().line;
    assert_eq!(
        line, 1,
        "expected the error span to land on the source line, got: {:?}",
        err
    );
}

#[test]
fn unknown_mnemonic_like_word_is_a_macro_call_or_error() {
    // `frobnicate` isn't a real mnemonic; used bare with no `(...)`, it
    // has no valid statement reading and must be rejected, not silently
    // accepted as garbage.
    let err = parse_err("frobnicate t0");
    assert!(!err.to_string().is_empty());
}

#[test]
fn bracket_address_can_be_the_first_operand() {
    let node = parse_ok("jmp [t1, t0, 8]\njmp [t1]");
    let dump = node.dump();
    assert!(dump.contains("jmp"));
    assert!(dump.contains("t1, t0, 8"));
}

#[test]
fn label_after_operandless_mnemonic_starts_a_statement() {
    let node = parse_ok("_a:\n    ret\n_b:\n    ret\n.c:\n    nop\n.d:\n    ret");
    let dump = node.dump();
    assert!(dump.contains("_b:"), "{dump}");
    assert!(dump.contains(".d:"), "{dump}");
}
