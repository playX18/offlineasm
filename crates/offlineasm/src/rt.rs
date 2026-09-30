//! Owns the machine state for the `backend = rloop` dispatch loop.
//!
//! [`Machine`] holds the register file ([`Registers`]). `push`/`pop` and their
//! kin read and write memory at `regs.sp` directly, the same way
//! `loadp`/`storep` do, so the host must point `sp` at real addressable memory
//! before running generated code. Generated code runs on a caller-owned
//! `Machine`.

/// Holds the rloop interpreter register file.
#[derive(Debug, Default, Clone, Copy)]
#[allow(non_snake_case)]
pub struct Registers {
    pub t0: u64,
    pub t1: u64,
    pub t2: u64,
    pub t3: u64,
    pub t4: u64,
    pub t5: u64,
    pub t6: u64,
    pub t7: u64,
    /// Program counter.
    pub pc: u64,
    /// `csr0`.
    pub t9: u64,
    /// `csr1`.
    pub t8: u64,
    /// `csr2`.
    pub t10: u64,
    /// `csr3`.
    pub t11: u64,
    pub cfr: u64,
    /// Link register: the opcode to dispatch to on `ret`.
    pub lr: u64,
    pub sp: u64,
    pub d0: u64,
    pub d1: u64,
    pub d2: u64,
    pub d3: u64,
    pub d4: u64,
    pub d5: u64,
    pub d6: u64,
}

impl Registers {
    /// Creates zeroed registers.
    pub const fn new() -> Self {
        Self {
            t0: 0,
            t1: 0,
            t2: 0,
            t3: 0,
            t4: 0,
            t5: 0,
            t6: 0,
            t7: 0,
            pc: 0,
            t8: 0,
            t9: 0,
            t10: 0,
            t11: 0,
            cfr: 0,
            lr: 0,
            sp: 0,
            d0: 0,
            d1: 0,
            d2: 0,
            d3: 0,
            d4: 0,
            d5: 0,
            d6: 0,
        }
    }
}

/// Holds the owned state a generated dispatch loop runs on.
#[derive(Debug, Default)]
pub struct Machine {
    /// The machine register file.
    pub regs: Registers,
}

impl Machine {
    /// Creates a zeroed machine.
    pub const fn new() -> Self {
        Self {
            regs: Registers::new(),
        }
    }

    /// Resets registers to zero.
    ///
    /// This does not touch whatever memory `regs.sp` points at; the caller
    /// owns that buffer and must reset it separately if needed.
    pub fn reset(&mut self) {
        *self = Self::new();
    }

    /// Reads `regs.lr` as the raw opcode value a generated
    /// `Opcode::from_u64` accepts.
    pub fn lr_as_u64(&self) -> u64 {
        self.regs.lr
    }
}
