# offlineasm

A portable assembler for Rust (based on [WebKit's offlineasm](https://github.com/WebKit/WebKit/tree/main/Source/JavaScriptCore/offlineasm)).

- `offlineasm` assembles at compile time to `global_asm!()` (or a Rust dispatch loop with `backend = rloop`).
- `onlineasm` assembles at runtime to machine code.

## Quickstart

Compile-time assembly with `offlineasm`:

```rust
use offlineasm::offlineasm;

offlineasm! {
    settings {
        backend = native,   // or `rloop` for the portable interpreter
    }

    global _answer
    _answer:
        move t0, 42
        ret
}
```

Runtime assembly with `onlineasm`:

```rust
use onlineasm::{onlineasm, Assembler, JitAllocator, Target};

let mut asm = Assembler::native();
// Neither crate has built-in `arg0`/`arg1` ABI aliases. Declare the
// argument registers yourself per target and ABI.
let (arg0, arg1) = match asm.target() {
    Target::X64 => (onlineasm::regs::t6, onlineasm::regs::t1),
    Target::AArch64 | Target::RISCV64 => (onlineasm::regs::t0, onlineasm::regs::t1),
};
onlineasm!(asm;
    =>add;
    move t0, {arg0};
    addq t0, {arg1};
    ret;
);
let code = asm.finish().expect("assemble");
let entry = code.offset(add).expect("add is bound");
let mut jit = JitAllocator::new(Default::default());
let span = code.allocate(&mut jit).expect("allocate");
let f: extern "C" fn(u64, u64) -> u64 =
    unsafe { std::mem::transmute(span.rx().add(entry as usize)) };
assert_eq!(f(40, 2), 42);
```

## Examples

| Example | Assembler | Shows |
| --- | --- | --- |
| [`llint`](examples/llint/) | offlineasm, native and rloop | A register-based bytecode interpreter in the style of WebKit's LLInt in `llint.asm`. Frames on `sp`/`cfr`, bytecode calls as machine `call`/`ret`, handler macros instantiated per dispatch style with jump table. |
| [`green_threads`](examples/green_threads.rs) | offlineasm, native | Stack switching: per-target callee-saved sets (including FP registers), `lr`, and initialization of first frame. |
| [`rloop`](examples/rloop.rs) | offlineasm, rloop | The smallest rloop program. |
| [`bf_jit`](crates/onlineasm/examples/bf_jit.rs) | onlineasm | A Brainfuck JIT: labels created at runtime and spliced in, calls into Rust. |
```bash
cargo run --release --example llint
```

`llint` and `rloop` need nightly (`rust_preserve_none_cc`). The onlineasm
examples run with `cargo run -p onlineasm --example <name>`.

