//! Emission-throughput benchmarks
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use onlineasm::{regs, Assembler, BackwardAssembler, Gpr, Mem};

struct Regs {
    t0: Gpr,
    t1: Gpr,
    t2: Gpr,
}

fn setup() -> (Regs, Mem, Mem) {
    // Resolve portable vregs once; the loops measure emission only.
    let probe = Assembler::native();
    let r = Regs {
        t0: probe.vreg_gpr(regs::t0),
        t1: probe.vreg_gpr(regs::t1),
        t2: probe.vreg_gpr(regs::t2),
    };
    let mem_a = probe.mem(regs::t0, 8);
    let mem_b = probe.mem(regs::t0, 16);
    (r, mem_a, mem_b)
}

fn iters() -> usize {
    std::env::var("MIX_N")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1000)
}

#[inline(never)]
fn mix<const B: bool>(asm: &mut Assembler<B>, r: &Regs, mem_a: Mem, mem_b: Mem) {
    let l1 = asm.label();
    let l2 = asm.label();
    asm.r#move(r.t0, 1i32);
    asm.addq(r.t0, r.t0, r.t1);
    asm.loadq(r.t2, mem_a);
    asm.storeq(mem_b, r.t2);
    asm.push(&[r.t0, r.t1]);
    asm.pop(&[r.t0, r.t1]);
    asm.bqeq(r.t0, r.t1, l1);
    asm.baddqo(r.t0, r.t0, r.t1, l1);
    asm.jmp(l2);
    asm.bind(l1);
    asm.nop();
    asm.bind(l2);
}

fn bench_alu(c: &mut Criterion) {
    let (r, _, _) = setup();
    let n = iters();
    c.bench_function(format!("emit_alu/{n}").as_str(), |b| {
        b.iter(|| {
            let mut asm = Assembler::native();
            for _ in 0..n {
                asm.r#move(r.t0, 1i32);
                asm.addq(r.t0, r.t0, r.t1);
                asm.subq(r.t0, r.t0, 2i32);
                asm.mulq(r.t0, r.t0, r.t1);
                asm.andq(r.t0, r.t0, r.t1);
                asm.orq(r.t0, r.t0, r.t1);
                asm.xorq(r.t0, r.t0, r.t1);
            }
            black_box(asm.finish().unwrap().data().len());
        })
    });
}

fn bench_mem(c: &mut Criterion) {
    let (r, mem_a, mem_b) = setup();
    let n = iters();
    c.bench_function(format!("emit_mem/{n}").as_str(), |b| {
        b.iter(|| {
            let mut asm = Assembler::native();
            for _ in 0..n {
                asm.loadq(r.t2, mem_a);
                asm.storeq(mem_b, r.t2);
                asm.leap(r.t2, mem_a);
                asm.loadq(r.t0, mem_b);
                asm.storeq(mem_a, r.t0);
            }
            black_box(asm.finish().unwrap().data().len());
        })
    });
}

fn bench_branch(c: &mut Criterion) {
    let (r, _, _) = setup();
    let n = iters();
    c.bench_function(format!("emit_branch/{n}").as_str(), |b| {
        b.iter(|| {
            let mut asm = Assembler::native();
            for _ in 0..n {
                let l1 = asm.label();
                let l2 = asm.label();
                asm.bqeq(r.t0, r.t1, l1);
                asm.baddqo(r.t0, r.t0, r.t1, l1);
                asm.jmp(l2);
                asm.bind(l1);
                asm.nop();
                asm.bind(l2);
            }
            black_box(asm.finish().unwrap().data().len());
        })
    });
}

fn bench_push(c: &mut Criterion) {
    let (r, _, _) = setup();
    let n = iters();
    c.bench_function(format!("emit_push/{n}").as_str(), |b| {
        b.iter(|| {
            let mut asm = Assembler::native();
            for _ in 0..n {
                asm.push(&[r.t0, r.t1]);
                asm.pop(&[r.t0, r.t1]);
                asm.push(&[r.t0, r.t1, r.t2, r.t0]);
                asm.pop(&[r.t0, r.t1, r.t2, r.t0]);
            }
            black_box(asm.finish().unwrap().data().len());
        })
    });
}

fn bench_mix(c: &mut Criterion) {
    let (r, mem_a, mem_b) = setup();
    let n = iters();
    c.bench_function(format!("emit_mix/{n}").as_str(), |b| {
        b.iter(|| {
            let mut asm = Assembler::native();
            for _ in 0..n {
                mix(&mut asm, &r, mem_a, mem_b);
            }
            black_box(asm.finish().unwrap().data().len());
        })
    });
}

fn bench_backward(c: &mut Criterion) {
    let (r, mem_a, mem_b) = setup();
    let n = iters();
    c.bench_function(format!("emit_backward/{n}").as_str(), |b| {
        b.iter(|| {
            let mut asm = BackwardAssembler::native_backward();
            for _ in 0..n {
                mix(&mut asm, &r, mem_a, mem_b);
            }
            black_box(asm.finish().unwrap().data().len());
        })
    });
}

/// One completed image per iteration, through a fresh assembler versus one
/// reused via `finish(&mut self)`.
fn bench_reuse(c: &mut Criterion) {
    let (r, mem_a, mem_b) = setup();
    let n = iters().min(200);
    let mut group = c.benchmark_group("image");
    group.bench_function(format!("fresh/{n}"), |b| {
        b.iter(|| {
            for _ in 0..n {
                let mut asm = Assembler::native();
                mix(&mut asm, &r, mem_a, mem_b);
                black_box(asm.finish().unwrap().data().len());
            }
        })
    });
    let mut asm = Assembler::native();
    group.bench_function(format!("reused/{n}"), |b| {
        b.iter(|| {
            for _ in 0..n {
                mix(&mut asm, &r, mem_a, mem_b);
                black_box(asm.finish().unwrap().data().len());
            }
        })
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_alu,
    bench_mem,
    bench_branch,
    bench_push,
    bench_mix,
    bench_backward,
    bench_reuse
);
criterion_main!(benches);
