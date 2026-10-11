//! Post-emission patching: rewrite an immediate, retarget a jump, and fill
//! an absolute call target.
//!
//! Run with: `cargo run -p onlineasm --example patch`

use onlineasm::{onlineasm, Assembler, JitAllocator, PatchLocation, Target};

/// Builds a `fn() -> u64` that returns whatever immediate its `#[patch]`ed
/// `move` currently holds, then rewrites that immediate at runtime.
fn patched_constant() -> Result<(), Box<dyn std::error::Error>> {
    let mut asm = Assembler::native();
    onlineasm!(asm;
        #[patch = slot] move t0, 0;
        ret;
    );
    let code = asm.finish()?;
    // A patched `move` is an immediate site ...
    let location = code.location(slot).ok_or("slot is unbound")?;
    assert!(matches!(location, PatchLocation::Data(_)));

    let mut jit = JitAllocator::new(Default::default());
    let mut span = code.allocate(&mut jit)?;
    // ... rewritten with `repatch_u64`.
    //
    // SAFETY: `span` holds `code`, and nothing executes the patched
    // instruction while it is rewritten.
    unsafe { onlineasm::repatch_u64(&mut jit, &mut span, &location, 42)? };

    // SAFETY: the image is one `extern "C" fn() -> u64`, and `span`/`jit`
    // outlive the call.
    let f: extern "C" fn() -> u64 = unsafe { std::mem::transmute(span.rx()) };
    assert_eq!(f(), 42);

    // The site stays writable: patch it again and the next call sees it.
    unsafe { onlineasm::repatch_u64(&mut jit, &mut span, &location, 7)? };
    assert_eq!(f(), 7);
    println!("patched `move` immediate: 42, then 7");
    Ok(())
}

/// Builds a function that jumps to one of two blocks, then retargets the
/// patched jump at runtime so the next call takes the other block.
fn retargeted_jump() -> Result<(), Box<dyn std::error::Error>> {
    let mut asm = Assembler::native();
    onlineasm!(asm;
        #[patch = j] jmp .slow;
        =>fast;
        move t0, 2;
        ret;
        .slow:
        move t0, 1;
        ret;
    );
    let code = asm.finish()?;
    // A patched `jmp`/`call`/branch is a jump site ...
    let PatchLocation::Jump(jump) = code.location(j).ok_or("jump is unbound")? else {
        panic!("a patched `jmp` is a jump, not an immediate");
    };
    let fast = code.offset(fast).ok_or("fast is unbound")?;

    let mut jit = JitAllocator::new(Default::default());
    let mut span = code.allocate(&mut jit)?;
    // SAFETY: as above.
    let f: extern "C" fn() -> u64 = unsafe { std::mem::transmute(span.rx()) };
    assert_eq!(f(), 1);

    // ... retargeted with `repatch_jump_span` to an absolute address. The new
    // target must be within the jump's range (same image always is).
    //
    // SAFETY: `span` holds `code`, and nothing executes the jump while it is
    // rewritten.
    let target = unsafe { span.rx().add(fast as usize) };
    unsafe { onlineasm::asmkit::repatch_jump_span(&mut jit, &mut span, jump, target)? };
    assert_eq!(f(), 2);
    println!("retargeted `jmp`: 1, then 2");
    Ok(())
}

/// Calls a Rust helper through `#[patch_abs]`, which reserves a 64-bit
/// absolute-address slot and branches to it indirectly, so the callee can
/// live anywhere (unlike a range-limited relative `call`).
fn absolute_call() -> Result<(), Box<dyn std::error::Error>> {
    extern "C" fn helper() -> u64 {
        99
    }

    let mut asm = Assembler::native();
    // `call` writes `lr` on AArch64 and RISC-V, so save it around the call.
    let frame: i32 = if asm.target() == Target::X64 { 8 } else { 16 };
    onlineasm!(asm;
        subp sp, {frame};
    );
    if asm.target() != Target::X64 {
        onlineasm!(asm; storeq [sp], lr;);
    }
    // The placeholder target just reserves the slot; it is overwritten below.
    onlineasm!(asm;
        #[patch_abs = callee] call {0i64};
    );
    if asm.target() != Target::X64 {
        onlineasm!(asm; loadq lr, [sp];);
    }
    onlineasm!(asm;
        addp sp, {frame};
        ret;
    );

    let code = asm.finish()?;
    // `#[patch_abs]` binds the address slot, an immediate site ...
    let location = code.location(callee).ok_or("callee is unbound")?;
    assert!(matches!(location, PatchLocation::Data(_)));

    let mut jit = JitAllocator::new(Default::default());
    let mut span = code.allocate(&mut jit)?;
    // ... filled in with the helper's absolute address.
    //
    // SAFETY: `span` holds `code`, and nothing executes the call while its
    // target is written.
    unsafe {
        onlineasm::repatch_u64(&mut jit, &mut span, &location, helper as *const () as u64)?;
    }

    // SAFETY: the image is one `extern "C" fn() -> u64`.
    let f: extern "C" fn() -> u64 = unsafe { std::mem::transmute(span.rx()) };
    assert_eq!(f(), 99);
    println!("`#[patch_abs]` call: 99");
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    patched_constant()?;
    retargeted_jump()?;
    absolute_call()?;
    println!("ok");
    Ok(())
}
