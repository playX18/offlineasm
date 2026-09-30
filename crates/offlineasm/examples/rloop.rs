#![feature(rust_preserve_none_cc)]

use offlineasm::offlineasm;
use offlineasm::rt::*;

offlineasm! {
    settings {
        // backend = native
        backend = rloop
    }

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
}

use offlineasm_rloop_config_0::{InterpretedCode, Opcode};

struct SumHost;

impl InterpretedCode for SumHost {
    unsafe fn call_native(&mut self, _m: &mut Machine, target: u64, arg0: u64, arg1: u64) -> u64 {
        let func: extern "C" fn(u64, u64) -> u64 = core::mem::transmute(target as usize);
        func(arg0, arg1)
    }
}

fn main() {
    let mut host = SumHost;
    let mut m = Machine::new();

    let mut stack_buf = [0u64; 64];
    m.regs.sp = stack_buf.as_mut_ptr().wrapping_add(stack_buf.len()) as u64;

    let stopped = host.run(&mut m);

    assert_eq!(stopped, Opcode::Done, "the program returned");
    println!("1 + 2 + ... + 10 = {}", m.regs.t0);
    assert_eq!(m.regs.t0, 55);
}
