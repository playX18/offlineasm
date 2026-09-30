# onlineasm

Portable assembler for x86-64, AArch64, and RISC-V 64. 

```rust
use onlineasm::{onlineasm, Assembler, JitAllocator, Target};

let mut asm = Assembler::native();
// onlineasm has no built-in `arg0`/`arg1` ABI aliases. Declare them
// yourself, per target/ABI (see reference).
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
// `add` is a Rust `Label` in scope after the macro.
let code = asm.finish().expect("assemble");
let entry = code.offset(add).expect("add is bound");
let mut jit = JitAllocator::new(Default::default());
let span = code.allocate(&mut jit).expect("allocate");
let f: extern "C" fn(u64, u64) -> u64 =
    unsafe { std::mem::transmute(span.rx().add(entry as usize)) };
assert_eq!(f(40, 2), 42);
```

