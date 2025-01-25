use offlineasm::*;

offlineasm!(
    ->factorial:
        bineq a0, 0, =>recurse
        mov r0, 1
        ret
    recurse:
        push a0
        subi a0, a0, 1
        call &factorial
        pop a0
        muli r0, a0, r0
        ret


    ->test_fn:
        cdeq r0, fa0, fa1 
        ret 
    ->itest_fn:
        cieq r0, a0, a1 
        ret
    export test_fn as unsafe extern "C" fn test_fn(a0: f64, a1: f64) -> u32;
    export itest_fn as unsafe extern "C" fn itest_fn(a0: u32, a1: u32) -> u32;
    export factorial as unsafe extern "C" fn factorial(a0: u32) -> u32;
);

::core::arch::global_asm!(
    r#"
        itest_fn2:
            cmp edi, eax 

    "#
);
const X: isize = 0x42;
fn main() {
    println!("{ASM}");
    println!("{}", unsafe { test_fn(2.0, 2.0) });
    println!("{}", unsafe { itest_fn(2, 2) });
    println!("{}", unsafe { factorial(5) });
}
