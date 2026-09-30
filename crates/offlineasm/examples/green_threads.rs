use offlineasm::offlineasm;

offlineasm! {
    settings {
        backend = native
    }

    if X86_64
        const a0 = t6
        const a1 = t1
        const a2 = t2
    else
        const a0 = t0
        const a1 = t1
        const a2 = t2
    end

    // `m(offset, reg)` for each saved GPR and `f(offset, reg)` for each
    // saved FPR, at byte offsets in a FRAME-byte block (a multiple of 16).
    if X86_64
        const FRAME = 48
        const RETURN_SLOT = 48
        macro forEachSaved(m, f)
            m(0, csr0)
            m(8, csr1)
            m(16, csr2)
            m(24, csr3)
            m(32, csr4)
            m(40, cfr)
        end
    elsif ARM64
        const FRAME = 160
        const RETURN_SLOT = 88
        macro forEachSaved(m, f)
            m(0, csr0)
            m(8, csr1)
            m(16, csr2)
            m(24, csr3)
            m(32, csr4)
            m(40, csr5)
            m(48, csr6)
            m(56, csr7)
            m(64, csr8)
            m(72, csr9)
            m(80, cfr)
            m(88, lr)
            f(96, csfr0)
            f(104, csfr1)
            f(112, csfr2)
            f(120, csfr3)
            f(128, csfr4)
            f(136, csfr5)
            f(144, csfr6)
            f(152, csfr7)
        end
    elsif RISCV64
        const FRAME = 208
        const RETURN_SLOT = 96
        macro forEachSaved(m, f)
            m(0, csr0)
            m(8, csr1)
            m(16, csr2)
            m(24, csr3)
            m(32, csr4)
            m(40, csr5)
            m(48, csr6)
            m(56, csr7)
            m(64, csr8)
            m(72, csr9)
            m(80, csr10)
            m(88, cfr)
            m(96, lr)
            f(104, %f8)
            f(112, %f9)
            f(120, %f18)
            f(128, %f19)
            f(136, %f20)
            f(144, %f21)
            f(152, %f22)
            f(160, %f23)
            f(168, %f24)
            f(176, %f25)
            f(184, %f26)
            f(192, %f27)
        end
    end

    macro saveGpr(offset, reg)
        storeq offset[sp], reg
    end
    macro saveFpr(offset, reg)
        stored offset[sp], reg
    end
    macro loadGpr(offset, reg)
        loadq reg, offset[sp]
    end
    macro loadFpr(offset, reg)
        loadd reg, offset[sp]
    end
    macro zeroGpr(offset, reg)
        storeq offset[t0], t3
    end
    macro skipFpr(offset, reg)
    end

    // coro_switch(save_sp: *mut u64, load_sp: u64)
    global _coro_switch
    _coro_switch:
        subp sp, FRAME
        forEachSaved(saveGpr, saveFpr)
        move t2, sp
        storeq 0[a0], t2
        move sp, a1
        forEachSaved(loadGpr, loadFpr)
        addp sp, FRAME
        ret

    // coro_init(stack_top: u64, entry: u64, arg: u64) -> u64
    //
    // Builds a frame below `stack_top` (16-byte aligned) that
    // `coro_switch` restores: every saved register zero except csr0 =
    // entry and csr1 = arg, and a return address of `coro_trampoline`.
    // Returns the `sp` to switch to.
    global _coro_init
    _coro_init:
        move t0, a0
        if X86_64
            // After `ret` pops the return slot, `sp` must be 16-byte aligned
            // for the trampoline's `call`: frame, return slot, then 16
            // bytes of padding up to the top.
            subp t0, FRAME + 24
        else
            subp t0, FRAME
        end
        move t3, 0
        forEachSaved(zeroGpr, skipFpr)
        storeq 0[t0], a1
        storeq 8[t0], a2
        leap t3, _coro_trampoline
        storeq RETURN_SLOT[t0], t3
        ret

    // Runs on the new stack: entry(arg). Never returns from entry
    _coro_trampoline:
        move a0, csr1
        call csr0
        break
}

extern "C" {
    fn coro_switch(save_sp: *mut u64, load_sp: u64);
    fn coro_init(stack_top: u64, entry: u64, arg: u64) -> u64;
}

struct Generator {
    sp: u64,
    caller_sp: u64,
    value: Option<u64>,
    finished: bool,
    body: fn(&mut Yielder),
    _stack: Vec<u128>,
}

struct Yielder(*mut Generator);

impl Yielder {
    fn yield_(&mut self, value: u64) {
        // SAFETY: the generator outlives its body
        unsafe {
            (*self.0).value = Some(value);
            coro_switch(&mut (*self.0).sp, (*self.0).caller_sp);
        }
    }
}

extern "C" fn generator_entry(gen_: *mut Generator) {
    // SAFETY: `coro_init` was handed this generator's address.
    unsafe {
        let body = (*gen_).body;
        body(&mut Yielder(gen_));
        (*gen_).finished = true;
        coro_switch(&mut (*gen_).sp, (*gen_).caller_sp);
    }
    unreachable!("a finished generator was resumed");
}

impl Generator {
    /// Creates a suspended generator.
    fn new(body: fn(&mut Yielder)) -> Box<Self> {
        let stack = vec![0u128; 64 * 1024 / 16];
        let top = stack.as_ptr_range().end as u64;
        let mut gen_ = Box::new(Self {
            sp: 0,
            caller_sp: 0,
            value: None,
            finished: false,
            body,
            _stack: stack,
        });
        let arg = &mut *gen_ as *mut Generator as u64;
        // SAFETY: `top` is the 16-byte aligned end of a stack this
        // generator owns.
        gen_.sp = unsafe { coro_init(top, generator_entry as *const () as u64, arg) };
        gen_
    }

    fn resume(&mut self) -> Option<u64> {
        if self.finished {
            return None;
        }
        // SAFETY: `self.sp` is a suspended stack produced by `coro_init` or
        // by the generator's last switch.
        unsafe { coro_switch(&mut self.caller_sp, self.sp) };
        self.value.take()
    }
}

fn fibonacci(y: &mut Yielder) {
    let (mut a, mut b) = (0u64, 1u64);
    loop {
        y.yield_(a);
        (a, b) = (b, a.wrapping_add(b));
    }
}

fn primes(y: &mut Yielder) {
    let mut found: Vec<u64> = Vec::new();
    let mut n = 2u64;
    loop {
        if found.iter().all(|p| n % p != 0) {
            found.push(n);
            y.yield_(n);
        }
        n += 1;
    }
}

fn countdown(y: &mut Yielder) {
    for i in (1..=3).rev() {
        y.yield_(i);
    }
}

fn main() {
    let mut fib = Generator::new(fibonacci);
    let mut prime = Generator::new(primes);
    let mut interleaved = Vec::new();
    for _ in 0..10 {
        interleaved.push(fib.resume().expect("fibonacci is endless"));
        interleaved.push(prime.resume().expect("primes are endless"));
    }
    println!("fib/prime interleaved: {interleaved:?}");
    assert_eq!(
        interleaved,
        [0, 2, 1, 3, 1, 5, 2, 7, 3, 11, 5, 13, 8, 17, 13, 19, 21, 23, 34, 29]
    );

    let mut count = Generator::new(countdown);
    let drained: Vec<u64> = std::iter::from_fn(|| count.resume()).collect();
    println!("countdown: {drained:?}");
    assert_eq!(drained, [3, 2, 1]);
    assert_eq!(count.resume(), None, "a finished generator stays finished");

    // Many more round trips; the sequence must pick up where it left off.
    let (mut a, mut b) = (55u64, 89u64);
    for _ in 0..10_000 {
        assert_eq!(fib.resume(), Some(a));
        (a, b) = (b, a.wrapping_add(b));
    }
    println!("10000 more switches into the fibonacci generator: ok");
}
