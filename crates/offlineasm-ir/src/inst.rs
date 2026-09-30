use super::*;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Alu3 {
    pub dst: Op,
    pub lhs: Op,
    pub rhs: Op,
}

impl Alu3 {
    /// Builds an `Alu3` from a 2- or 3-operand invocation.
    ///
    /// `dst` doubles as `lhs` in the 2-operand form.
    ///
    /// # Errors
    ///
    /// [`ExpandError::BadOperand`] if `ops` has neither 2 nor 3 elements.
    pub fn from_operands(mn: Mnemonic, ops: &[Op]) -> Result<Self, ExpandError> {
        match ops {
            [dst, rhs] => Ok(Alu3 {
                dst: *dst,
                lhs: *dst,
                rhs: *rhs,
            }),
            [dst, lhs, rhs] => Ok(Alu3 {
                dst: *dst,
                lhs: *lhs,
                rhs: *rhs,
            }),
            _ => Err(bad(mn, "takes 2 or 3 operands")),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Inst {
    Mov {
        w: Width,
        dst: Op,
        src: Op,
        patch: bool,
    },
    Bind(Lbl),
    MovZero32 {
        dst: Op,
        src: Op,
    },
    Bswap {
        w: Width,
        dst: Op,
        src: Op,
    },
    Load {
        w: Width,
        sx: Sx,
        dst: Gpr,
        addr: Mem,
        acquire: bool,
    },
    Store {
        w: Width,
        src: Op,
        addr: Mem,
    },
    LoadF {
        k: FKind,
        dst: Fpr,
        addr: Mem,
    },
    StoreF {
        k: FKind,
        src: Fpr,
        addr: Mem,
    },
    FMov {
        k: FKind,
        dst: Fpr,
        src: Fpr,
    },
    LoadV {
        dst: Fpr,
        addr: Mem,
    },
    StoreV {
        src: Fpr,
        addr: Mem,
    },
    VMov {
        dst: Fpr,
        src: Fpr,
    },
    Lea {
        w: Width,
        dst: Gpr,
        src: LeaSrc,
    },
    Push {
        op: Op,
    },
    Pop {
        op: Op,
    },
    PushV {
        src: Fpr,
    },
    PopV {
        dst: Fpr,
    },
    Peek {
        disp: i32,
        dst: Gpr,
    },
    Poke {
        disp: i32,
        src: Gpr,
    },

    Add {
        w: Width,
        op: Alu3,
    },
    Sub {
        w: Width,
        op: Alu3,
    },
    Mul {
        w: Width,
        op: Alu3,
    },
    And {
        w: Width,
        op: Alu3,
    },
    Or {
        w: Width,
        op: Alu3,
    },
    Xor {
        w: Width,
        op: Alu3,
    },
    Not {
        w: Width,
        dst: Op,
    },
    Neg {
        w: Width,
        dst: Op,
    },
    Shift {
        w: Width,
        op: ShiftOp,
        dst: Gpr,
        cnt: ShiftCnt,
    },
    MulImm {
        w: Width,
        dst: Gpr,
        lhs: Gpr,
        imm: i64,
    },
    AluS {
        op: AluOp,
        w: Width,
        alu: Alu3,
    },
    Adc {
        dst: Op,
        src: Op,
    },
    Sbb {
        dst: Op,
        src: Op,
    },
    MulWide {
        signed: bool,
        dst: Gpr,
        lhs: Gpr,
        rhs: Gpr,
    },
    MulHigh {
        signed: bool,
        rhs: Op,
    },
    DivMod1 {
        signed: bool,
        w: Width,
        divisor: Op,
    },
    Div3 {
        signed: bool,
        w: Width,
        dst: Gpr,
        dvd: Op,
        dvs: Op,
    },
    Rem3 {
        signed: bool,
        w: Width,
        dst: Gpr,
        dvd: Op,
        dvs: Op,
    },
    Extend {
        from: Width,
        to: Width,
        sx: Sx,
        dst: Gpr,
        src: Op,
    },
    Ctz {
        w: Width,
        dst: Gpr,
        src: Op,
    },
    Clz {
        w: Width,
        dst: Gpr,
        src: Op,
    },
    Popcnt {
        w: Width,
        dst: Gpr,
        src: Op,
    },
    Cqo {
        quad: bool,
    },
    AddShifted {
        dst: Gpr,
        lhs: Gpr,
        rhs: Gpr,
        amount: u8,
    },
    Cmov {
        w: Width,
        zero: bool,
        dst: Gpr,
        src: Op,
        test: Gpr,
    },
    VecExtract {
        w: Width,
        dst: Gpr,
        src: Fpr,
        lane: u8,
    },

    Branch {
        cc: IntCc,
        w: Width,
        lhs: Op,
        rhs: Op,
        target: Lbl,
        patch: bool,
    },

    TestBranch {
        w: Width,
        value: Op,
        mask: Option<Op>,
        test: TestKind,
        target: Lbl,
        patch: bool,
    },

    OpBranch {
        op: FlagAlu,
        w: Width,
        flag: PredFlag,
        args: Vec<Op>,
        target: Lbl,
        patch: bool,
    },

    FlagBranch {
        flag: PredFlag,
        target: Lbl,
        patch: bool,
    },
    Jump {
        target: Target,
        patch: bool,
    },
    Call {
        target: Target,
        patch: bool,
    },
    Ret,
    /// Traps. `break` lowers to `int3`, `brk`, or `ebreak`.
    Break,
    Nop,

    /// Compares integers and writes 0 or 1 to `dst`.
    IntSet {
        cc: IntCc,
        w: Width,
        dst: Op,
        lhs: Op,
        rhs: Op,
    },
    /// Tests a value and writes 0 or 1 to `dst`.
    TestSet {
        w: Width,
        value: Op,
        mask: Option<Op>,
        test: TestKind,
        dst: Op,
    },

    /// Runs scalar float arithmetic such as `addf` through `divd`.
    FArith {
        op: FAlu,
        k: FKind,
        arith: FArith3,
    },
    /// Runs a fused multiply-add. `dst` is `op(a, b, c)`.
    Fma {
        op: FmaOp,
        k: FKind,
        a: Op,
        b: Op,
        c: Op,
        dst: Fpr,
    },
    FSqrt {
        k: FKind,
        dst: Fpr,
        src: Op,
    },
    FRound {
        k: FKind,
        mode: RoundMode,
        dst: Fpr,
        src: Op,
    },
    FAbs {
        k: FKind,
        dst: Fpr,
        src: Op,
    },
    FNeg {
        k: FKind,
        dst: Fpr,
        src: Op,
    },
    /// Runs bitwise logic on float bits.
    FBit {
        or: bool,
        k: FKind,
        dst: Fpr,
        src: Op,
    },
    /// Truncates a float to an integer when the value is in range.
    ///
    /// Out-of-range results are the backend's native saturate value.
    CvtFI {
        k: FKind,
        w: Width,
        dst: Gpr,
        src: Op,
    },
    /// Converts an integer to a float exactly.
    CvtIF {
        signed: bool,
        from: Width,
        k: FKind,
        dst: Fpr,
        src: Op,
    },
    /// Narrows or widens a float.
    CvtFF {
        from: FKind,
        to: FKind,
        dst: Fpr,
        src: Op,
    },
    /// Reinterprets bits between integer and float.
    Bitcast {
        dir: BitcastDir,
        dst: Op,
        src: Op,
    },
    /// Compares floats and branches on the result.
    BranchF {
        cc: FCc,
        k: FKind,
        lhs: Op,
        rhs: Op,
        target: Lbl,
        patch: bool,
    },
    /// Compares floats and writes 0 or 1.
    FSet {
        cc: FCc,
        k: FKind,
        dst: Op,
        lhs: Op,
        rhs: Op,
    },

    /// Orders memory. `memfence` is a full barrier and `fence` is inner-shareable.
    Fence {
        full: bool,
    },
    /// Hints a spin loop. Emits `PAUSE` on x86 and RISC-V, `YIELD` on AArch64.
    Pause,
    /// Loads a thread-local slot into a register.
    ///
    /// Slots are 8 bytes wide. Sub-word widths zero-extend, matching
    /// `loadb`/`loadh`/`loadi`.
    TlsLoad {
        w: Width,
        dst: Gpr,
        idx: i64,
    },
    /// Stores a register into a thread-local slot.
    ///
    /// Only the low `w` bytes are written; the rest of the slot is
    /// preserved.
    TlsStore {
        w: Width,
        src: Gpr,
        idx: i64,
    },
    /// Materializes the address of a thread-local slot.
    TlsLea {
        dst: Gpr,
        idx: i64,
    },
    /// Runs an atomic read-modify-write.
    AtomicRmw {
        op: AtomicOp,
        w: Width,
        a: Op,
        b: Op,
    },
    /// Compares and swaps atomically. The expected value lives in `t0`.
    ///
    /// `branch` holds the `batomicweakcas*` target when present.
    AtomicCas {
        w: Width,
        mem: Mem,
        src: Gpr,
        branch: Option<Lbl>,
    },
    /// Loads linked for a later store-conditional.
    LoadLinked {
        w: Width,
        mem: Mem,
        dst: Gpr,
    },
    /// Stores conditionally. Writes 0 or 1 to `status`.
    StoreCond {
        w: Width,
        status: Gpr,
        src: Gpr,
        mem: Mem,
    },
    /// Loads a pair of values from one address.
    PairLoad {
        w: PairW,
        dst1: Op,
        dst2: Op,
        mem: Mem,
    },
    /// Stores a pair of values to one address.
    PairStore {
        w: PairW,
        src1: Op,
        src2: Op,
        mem: Mem,
    },
}

/// Selects sign or zero extension.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Sx {
    Zero,
    Sign,
}

/// Holds a shift count as an immediate or a register.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ShiftCnt {
    Imm(i64),
    Reg(Gpr),
}

/// Holds a `lea` source: memory, a label, or an external symbol.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum LeaSrc {
    Mem(Mem),
    Label(Lbl),
    Extern(Extern),
}

/// Names the ALU op fused into [`Inst::OpBranch`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FlagAlu {
    Add,
    Sub,
    Mul,
    Or,
}

/// Names an ALU op that sets the pending flag.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AluOp {
    Add,
    Sub,
    Or,
}

/// Names a scalar floating-point operation.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FAlu {
    Add,
    Sub,
    Mul,
    Div,
    Min,
    Max,
}

impl FAlu {
    /// Reports whether `self` commutes.
    pub const fn is_commutative(self) -> bool {
        matches!(self, FAlu::Add | FAlu::Mul | FAlu::Min | FAlu::Max)
    }
}

/// Names a fused multiply-add operation.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FmaOp {
    /// `a*b + c`.
    Add,
    /// `a*b - c`.
    Sub,
    /// `-(a*b) + c`.
    NegAdd,
    /// `-(a*b) - c`.
    NegSub,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FArith3 {
    pub dst: Fpr,
    pub lhs: Op,
    pub rhs: Option<Op>,
}

impl FArith3 {
    /// Builds an `FArith3` from a 2-operand (`dst, lhs`) mnemonic
    /// invocation. `rhs` stays `None`.
    ///
    /// # Errors
    ///
    /// [`ExpandError::BadOperand`] if `ops` does not have exactly 2
    /// elements, or if the first is not [`Op::Fpr`].
    pub fn from_operands(mn: Mnemonic, ops: &[Op]) -> Result<Self, ExpandError> {
        match ops {
            [dst, lhs] => Ok(FArith3 {
                dst: fpr_op(mn, dst)?,
                lhs: *lhs,
                rhs: None,
            }),
            _ => Err(bad(mn, "takes 2 operands")),
        }
    }
}

/// Names a bitcast direction.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BitcastDir {
    Q2D,
    D2Q,
    I2F,
    F2I,
}

/// Names an atomic read-modify-write operation.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AtomicOp {
    Add,
    Sub,
    Xchg,
    And,
    Or,
    Xor,
}

/// Names a paired-access width.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PairW {
    B32,
    B64,
    F64,
    V128,
}

/// Builds an [`ExpandError::BadOperand`] for `mn`.
///
/// `msg` describes what was wrong with its operands.
pub fn bad(mn: Mnemonic, msg: impl Into<String>) -> ExpandError {
    ExpandError::BadOperand {
        mnemonic: mn.as_str().to_string(),
        msg: msg.into(),
    }
}

/// Checks that `ops` has exactly `n` elements.
///
/// # Errors
///
/// [`ExpandError::BadOperand`] if `ops.len() != n`.
pub fn expect_len(mn: Mnemonic, ops: &[Op], n: usize) -> Result<(), ExpandError> {
    if ops.len() == n {
        Ok(())
    } else {
        Err(bad(
            mn,
            format!("expected {} operands, got {}", n, ops.len()),
        ))
    }
}

/// Returns the immediate in `op`.
///
/// # Errors
///
/// [`ExpandError::BadOperand`] if `op` is not [`Op::Imm`].
pub fn imm_op(mn: Mnemonic, op: &Op) -> Result<i64, ExpandError> {
    match op {
        Op::Imm(v) => Ok(*v),
        _ => Err(bad(mn, "expected immediate")),
    }
}

/// Returns the GPR in `op`.
///
/// # Errors
///
/// [`ExpandError::BadOperand`] if `op` is not [`Op::Gpr`].
pub fn gpr_op(mn: Mnemonic, op: &Op) -> Result<Gpr, ExpandError> {
    match op {
        Op::Gpr(g) => Ok(*g),
        _ => Err(bad(mn, "expected GPR")),
    }
}

/// Returns the FPR in `op`.
///
/// # Errors
///
/// [`ExpandError::BadOperand`] if `op` is not [`Op::Fpr`].
pub fn fpr_op(mn: Mnemonic, op: &Op) -> Result<Fpr, ExpandError> {
    match op {
        Op::Fpr(x) => Ok(*x),
        _ => Err(bad(mn, "expected FPR")),
    }
}

/// Returns the address in `op`.
///
/// # Errors
///
/// [`ExpandError::BadOperand`] if `op` is not [`Op::Mem`].
pub fn mem_op(mn: Mnemonic, op: &Op) -> Result<Mem, ExpandError> {
    match op {
        Op::Mem(a) => Ok(*a),
        _ => Err(bad(mn, "expected memory")),
    }
}

/// Returns the label in `op`.
///
/// # Errors
///
/// [`ExpandError::BadOperand`] if `op` is not [`Op::Label`].
pub fn label_op(mn: Mnemonic, op: &Op) -> Result<Lbl, ExpandError> {
    match op {
        Op::Label(l) => Ok(*l),
        _ => Err(bad(mn, "expected label")),
    }
}

/// Compares two operands for equality.
///
/// Only immediates and registers compare equal. Memory, label, and symbolic
/// operands always compare unequal.
pub fn op_eq(a: &Op, b: &Op) -> bool {
    match (a, b) {
        (Op::Imm(x), Op::Imm(y)) => x == y,
        (Op::Gpr(x), Op::Gpr(y)) => x == y,
        (Op::Fpr(x), Op::Fpr(y)) => x == y,
        _ => false,
    }
}

impl Inst {
    /// Visits every label this instruction binds, branches to, or names.
    ///
    /// Frontends use this to resolve the opaque handles of one expansion
    /// (notably the `Fresh` labels `expand` mints) before printing or
    /// encoding the sequence.
    pub fn visit_labels(&self, f: &mut dyn FnMut(Lbl)) {
        fn visit_op(f: &mut dyn FnMut(Lbl), o: &Op) {
            if let Op::Label(l) = o {
                f(*l);
            }
        }
        fn visit_target(f: &mut dyn FnMut(Lbl), t: &Target) {
            if let Target::Label(l) = t {
                f(*l);
            }
        }
        fn visit_lea(f: &mut dyn FnMut(Lbl), s: &LeaSrc) {
            if let LeaSrc::Label(l) = s {
                f(*l);
            }
        }
        fn visit_ops(f: &mut dyn FnMut(Lbl), ops: &[Op]) {
            for o in ops {
                visit_op(f, o);
            }
        }
        match self {
            Inst::Mov { dst, src, .. }
            | Inst::MovZero32 { dst, src }
            | Inst::Bswap { dst, src, .. }
            | Inst::Adc { dst, src }
            | Inst::Sbb { dst, src }
            | Inst::Bitcast { dst, src, .. } => {
                visit_op(f, dst);
                visit_op(f, src);
            }
            Inst::IntSet { dst, lhs, rhs, .. } | Inst::FSet { dst, lhs, rhs, .. } => {
                visit_op(f, dst);
                visit_op(f, lhs);
                visit_op(f, rhs);
            }
            Inst::Bind(l) => f(*l),
            Inst::Lea { src, .. } => visit_lea(f, src),
            Inst::Store { src, .. } => visit_op(f, src),
            Inst::Push { op } | Inst::Pop { op } => visit_op(f, op),
            Inst::Add { op: a, .. }
            | Inst::Sub { op: a, .. }
            | Inst::Mul { op: a, .. }
            | Inst::And { op: a, .. }
            | Inst::Or { op: a, .. }
            | Inst::Xor { op: a, .. } => {
                visit_op(f, &a.dst);
                visit_op(f, &a.lhs);
                visit_op(f, &a.rhs);
            }
            Inst::AluS { alu, .. } => {
                visit_op(f, &alu.dst);
                visit_op(f, &alu.lhs);
                visit_op(f, &alu.rhs);
            }
            Inst::Not { dst, .. } | Inst::Neg { dst, .. } => visit_op(f, dst),
            Inst::MulHigh { rhs, .. } => visit_op(f, rhs),
            Inst::DivMod1 { divisor, .. } => visit_op(f, divisor),
            Inst::Div3 { dvd, dvs, .. } | Inst::Rem3 { dvd, dvs, .. } => {
                visit_op(f, dvd);
                visit_op(f, dvs);
            }
            Inst::Branch {
                lhs, rhs, target, ..
            } => {
                visit_op(f, lhs);
                visit_op(f, rhs);
                f(*target);
            }
            Inst::TestBranch {
                value,
                mask,
                target,
                ..
            } => {
                visit_op(f, value);
                if let Some(m) = mask {
                    visit_op(f, m);
                }
                f(*target);
            }
            Inst::OpBranch { args, target, .. } => {
                visit_ops(f, args);
                f(*target);
            }
            Inst::FlagBranch { target, .. } => f(*target),
            Inst::Jump { target, .. } | Inst::Call { target, .. } => visit_target(f, target),
            Inst::TestSet {
                value, mask, dst, ..
            } => {
                visit_op(f, value);
                if let Some(m) = mask {
                    visit_op(f, m);
                }
                visit_op(f, dst);
            }
            Inst::FArith { arith, .. } => {
                visit_op(f, &arith.lhs);
                if let Some(r) = &arith.rhs {
                    visit_op(f, r);
                }
            }
            Inst::Fma { a, b, c, .. } => {
                visit_op(f, a);
                visit_op(f, b);
                visit_op(f, c);
            }
            Inst::FSqrt { src, .. }
            | Inst::FRound { src, .. }
            | Inst::FAbs { src, .. }
            | Inst::FNeg { src, .. }
            | Inst::FBit { src, .. }
            | Inst::CvtFI { src, .. }
            | Inst::CvtIF { src, .. }
            | Inst::CvtFF { src, .. } => visit_op(f, src),
            Inst::BranchF {
                lhs, rhs, target, ..
            } => {
                visit_op(f, lhs);
                visit_op(f, rhs);
                f(*target);
            }
            Inst::AtomicRmw { a, b, .. } => {
                visit_op(f, a);
                visit_op(f, b);
            }
            Inst::Load { .. }
            | Inst::LoadF { .. }
            | Inst::StoreF { .. }
            | Inst::FMov { .. }
            | Inst::LoadV { .. }
            | Inst::StoreV { .. }
            | Inst::VMov { .. }
            | Inst::PushV { .. }
            | Inst::PopV { .. }
            | Inst::Peek { .. }
            | Inst::Poke { .. }
            | Inst::Shift { .. }
            | Inst::MulImm { .. }
            | Inst::Extend { .. }
            | Inst::Ctz { .. }
            | Inst::Clz { .. }
            | Inst::Popcnt { .. }
            | Inst::Cqo { .. }
            | Inst::MulWide { .. }
            | Inst::AddShifted { .. }
            | Inst::Cmov { .. }
            | Inst::VecExtract { .. }
            | Inst::Fence { .. }
            | Inst::Pause
            | Inst::TlsLoad { .. }
            | Inst::TlsStore { .. }
            | Inst::TlsLea { .. }
            | Inst::AtomicCas { .. }
            | Inst::LoadLinked { .. }
            | Inst::StoreCond { .. }
            | Inst::PairLoad { .. }
            | Inst::PairStore { .. }
            | Inst::Ret
            | Inst::Break
            | Inst::Nop => {}
        }
    }
}
