use offlineasm::*;

offlineasm!(
    ->factorial:
        bineq a0, 0, =>recurse 
        mov 1, r0 
        ret 
    recurse: 
        push a0 
        subi a0, 1, a0
        call &factorial 
        pop a0
        muli a0, r0, r0
        ret 

    export factorial as unsafe extern "C" fn factorial(a0: u32) -> u32;
);

fn main() {
    println!("{ASM}");
    println!("{}", unsafe { factorial(5) });
}
