//! Accessing a Rust `thread_local!` from JIT code through `tls_*`.

use onlineasm::{onlineasm, Assembler, JitAllocator};
use std::cell::Cell;

thread_local! {
    static COUNTER: Cell<u64> = const { Cell::new(0) };
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn tls_base() -> u64 {
    // `fs:[0]` holds the TCB's own address, which is the `fs` base.
    let base: u64;
    unsafe { core::arch::asm!("mov {}, fs:[0]", out(reg) base) };
    base
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
fn tls_base() -> u64 {
    // `gs:[0x30]` is `NT_TIB.Self`, the TEB's own address.
    let base: u64;
    unsafe { core::arch::asm!("mov {}, gs:[0x30]", out(reg) base) };
    base
}

#[cfg(all(target_arch = "aarch64", not(target_vendor = "apple")))]
fn tls_base() -> u64 {
    let base: u64;
    unsafe { core::arch::asm!("mrs {}, tpidr_el0", out(reg) base) };
    base
}

#[cfg(target_arch = "riscv64")]
fn tls_base() -> u64 {
    let base: u64;
    unsafe { core::arch::asm!("mv {}, tp", out(reg) base) };
    base
}

#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
fn tls_base() -> u64 {
    let base: u64;
    unsafe { core::arch::asm!("mrs {}, tpidrro_el0", out(reg) base) };
    base
}

/// Returns the slot index of `COUNTER` relative to this thread's base.
fn counter_slot() -> i64 {
    let addr = COUNTER.with(|c| c.as_ptr() as u64);
    let off = addr.wrapping_sub(tls_base()) as i64;
    assert_eq!(off % 8, 0, "COUNTER is not 8-byte aligned to the base");
    off / 8
}

fn main() {
    let idx = counter_slot();
    println!("COUNTER is at TLSBase() {:+x} bytes", idx * 8);

    let mut asm = Assembler::native();
    onlineasm!(asm;
        =>entry;
        tls_leap t0, {idx} // or use `tls_loadp t0, {idx}` directly
        loadp t0, [t0]
        addp t0, 1
        tls_storep {idx}, t0
        ret
    );
    let code = asm.finish().expect("assemble");
    let offset = code.offset(entry).expect("entry is bound");
    let mut jit = JitAllocator::new(Default::default());
    let span = code.allocate(&mut jit).expect("allocate");
    let bump: extern "C" fn() -> u64 =
        unsafe { std::mem::transmute(span.rx().add(offset as usize)) };

    for want in 1..=3 {
        assert_eq!(bump(), want);
        assert_eq!(COUNTER.get(), want);
    }
    COUNTER.set(41);
    assert_eq!(bump(), 42, "the JIT sees Rust's store");
    println!("main thread: COUNTER = {}", COUNTER.get());

    // works only on linux, offset is fixed between threads.
    #[cfg(target_os = "linux")]
    std::thread::spawn(move || {
        println!("slot: {:x}", counter_slot());
        assert_eq!(counter_slot(), idx, "static TLS offset is per-process");
        assert_eq!(bump(), 1, "a fresh thread starts from zero");
        println!("other thread: COUNTER = {}", COUNTER.get());
    })
    .join()
    .unwrap();
}
