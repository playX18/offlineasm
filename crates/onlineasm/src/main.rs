use onlineasm::*;

fn main() {
    let mut asm = Assembler::native();

    onlineasm!(asm;
        move %rax, 42
        ret
    );
}
