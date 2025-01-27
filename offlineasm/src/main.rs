use offlineasm_proc::offlineasm;

offlineasm! {
    macro foo(a, b) {
        addi r0, a, 1
        b(r0)
        ret 
    }

    ->foo:
        foo(a0, macro cb(x) {
            addi r0, x, 2
        })
}

fn main() {}
