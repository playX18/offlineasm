
use std::arch::global_asm;

use offlineasm::*;

const fn fac(x: u32) -> u32 {
    if x == 0 {
        return 1;
    }
    return x * fac(x - 1);
}

#[repr(C)]
struct Point {
    x: u32,
    y: u32
}

offlineasm!(
    ; const POINT_Y_OFFSET = const std::mem::offset_of!(Point, y)
    ; ->test_fn:
    ;   loadi POINT_Y_OFFSET[a0], r0
    ;   leap  &test_fn, r0
    ;   ret
);

extern "C" {
    fn test_fn(point: *const Point) -> u64;
}
fn main() {
    let point = Point { x: 1, y: 2 };
    println!("{:p}", test_fn as *const u8);
    println!("{:x}", unsafe { test_fn(&point) });
}
