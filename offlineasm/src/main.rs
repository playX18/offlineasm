use offlineasm_expand::offlineasm;
use offlineasm_expand::offlineasm_inner;
offlineasm!(
    settings {
        x86_64 = target_arch="x86_64"
    }

    macro inc1(c) {
        addi c, c, 1
    }

    macro forLoop(counter, limit, inc, body) {
        move counter, 0
        loop_header: 
            bigteq counter, limit, =>loop_end
            body()
            inc(counter)
            jmp =>loop_header
        loop_end:
    }

    ->test_fn:
    {
        const src = a0;
        const dst = a1;
        const mulval = a2;
        const len = a3;

        push csr0
        move csr0, 0

        forLoop(csr0, len, inc1, macro body() {
            loadi t0, [src + csr0 * 4]
            muli t0, t0, mulval
            storei [dst + csr0 * 4], t0
        })
        pop csr0
        ret
    }

    ->test_fn2:
        move r0, const 42
        ret

    ->factorial:
        bineq a0, 0, =>recurse
        move r0, 1
        ret
    recurse:
        push a0
        subi a0, a0, 1
        call &factorial
        pop a0
        muli r0, r0, a0
        ret
);

extern "C" {
    fn factorial(x: u32) -> u32;
    fn test_fn(src: *const u32, dst: *mut u32, mulval: u32, len: u32);
}

fn main() {
    unsafe {
        println!("{}", factorial(5));
        let src = [1, 2, 3, 4, 5];
        let mut dst = [0; 5];
        test_fn(src.as_ptr(), dst.as_mut_ptr(), 2, 5);
        println!("{:?}", dst);
    }
}
