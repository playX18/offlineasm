use std::sync::LazyLock;

use regex::Regex;

pub const GPRS: [&str; 39] = [
    "t0",
    "t1",
    "t2",
    "t3",
    "t4",
    "t5",
    "t6",
    "t7",
    "t8",
    "t9",
    "t10",
    "t11",
    "t12",
    "cfr",
    "a0",
    "a1",
    "a2",
    "a3",
    "a4",
    "a5",
    "a6",
    "a7",
    "r0",
    "r1",
    "sp",
    "lr",
    "pc",
    // 64-bit only registers:
    "csr0",
    "csr1",
    "csr2",
    "csr3",
    "csr4",
    "csr5",
    "csr6",
    "csr7",
    "csr8",
    "csr9",
    "csr10",
    "invalidGPR",
];

pub const FPRS: [&str; 23] = [
    "ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "fa0", "fa1", "fa2", "fa3", "csfr0", "csfr1",
    "csfr2", "csfr3", "csfr4", "csfr5", "csfr6", "csfr7", "csfr8", "csfr9", "csfr10", "csfr11",
    "fr",
];

pub const VECS: [&str; 40] = [
    "v0", "v0_b", "v0_h", "v0_i", "v0_q", "v1", "v1_b", "v1_h", "v1_i", "v1_q", "v2", "v2_b",
    "v2_h", "v2_i", "v2_q", "v3", "v3_b", "v3_h", "v3_i", "v3_q", "v4", "v4_b", "v4_h", "v4_i",
    "v4_q", "v5", "v5_b", "v5_h", "v5_i", "v5_q", "v6", "v6_b", "v6_h", "v6_i", "v6_q", "v7",
    "v7_b", "v7_h", "v7_i", "v7_q",
];

pub const REGISTERS: [&str; 102] = [
    "t0",
    "t1",
    "t2",
    "t3",
    "t4",
    "t5",
    "t6",
    "t7",
    "t8",
    "t9",
    "t10",
    "t11",
    "t12",
    "cfr",
    "a0",
    "a1",
    "a2",
    "a3",
    "a4",
    "a5",
    "a6",
    "a7",
    "r0",
    "r1",
    "sp",
    "lr",
    "pc",
    // 64-bit only registers:
    "csr0",
    "csr1",
    "csr2",
    "csr3",
    "csr4",
    "csr5",
    "csr6",
    "csr7",
    "csr8",
    "csr9",
    "csr10",
    "invalidGPR",
    "ft0",
    "ft1",
    "ft2",
    "ft3",
    "ft4",
    "ft5",
    "fa0",
    "fa1",
    "fa2",
    "fa3",
    "csfr0",
    "csfr1",
    "csfr2",
    "csfr3",
    "csfr4",
    "csfr5",
    "csfr6",
    "csfr7",
    "csfr8",
    "csfr9",
    "csfr10",
    "csfr11",
    "fr",
    "v0",
    "v0_b",
    "v0_h",
    "v0_i",
    "v0_q",
    "v1",
    "v1_b",
    "v1_h",
    "v1_i",
    "v1_q",
    "v2",
    "v2_b",
    "v2_h",
    "v2_i",
    "v2_q",
    "v3",
    "v3_b",
    "v3_h",
    "v3_i",
    "v3_q",
    "v4",
    "v4_b",
    "v4_h",
    "v4_i",
    "v4_q",
    "v5",
    "v5_b",
    "v5_h",
    "v5_i",
    "v5_q",
    "v6",
    "v6_b",
    "v6_h",
    "v6_i",
    "v6_q",
    "v7",
    "v7_b",
    "v7_h",
    "v7_i",
    "v7_q",
];

pub static GPR_PATTERN: LazyLock<Regex> = LazyLock::new(|| {
    let regs = GPRS.join(")|(");
    Regex::new(&format!("\\A(({}))", regs)).unwrap()
});

pub static FPR_PATTERN: LazyLock<Regex> = LazyLock::new(|| {
    let regs = FPRS.join(")|(");
    Regex::new(&format!("\\A(({}))", regs)).unwrap()
});

pub static VEC_PATTERN: LazyLock<Regex> = LazyLock::new(|| {
    let regs = VECS.join(")|(");
    Regex::new(&format!("\\A(({}))", regs)).unwrap()
});

pub static REGISTER_PATTERN: LazyLock<Regex> = LazyLock::new(|| {
    let regs = REGISTERS.join(")|(");
    Regex::new(&format!("\\A(({}))", regs)).unwrap()
});
