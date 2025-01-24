use offlineasm::*;
offlineasm! {
    ; ->test_fn:
    ;   tzcnti a0, r0
    ;   ret
    ;
    ; export test_fn as unsafe extern "C" fn foo(x: u32) -> u32;
}

const _X: offlineasm::instructions::mov = offlineasm::instructions::mov;

fn main() {
    let x = 0x42u32;

    println!("{}", x.trailing_zeros());
    println!("{}", unsafe { foo(x) } );
}
