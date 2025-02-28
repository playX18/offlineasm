use offlineasm_expand::offlineasm;
use offlineasm_expand::offlineasm_inner;

extern "C-unwind" fn external() {
    println!("hello, world!");
}

offlineasm!(
    settings {
        x86_64 = target_arch="x86_64"
    }

    ->foo:
        call &external 
        ret
);

extern "C" {
    fn foo();
}

fn main() {
    unsafe {
        foo();
    }
}
