use crate::*;

/// Names the address form of a `lea` mnemonic.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum LeaForm {
    /// `leai`/`leap`: the address itself.
    Plain,
    /// `pcrtoaddr`: the address of a PC-relative slot.
    PcRel,
    /// `globaladdr`: the address of a global.
    Global,
    /// Loads an address with the portable `la` spelling.
    La,
}

/// Names one operation shared by one or more mnemonic spellings.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Mnemonic {
    Move,
    Load(Width),
    Store(Width),
    Extend {
        from: Width,
        to: Width,
        sx: Sx,
    },
    MovZero32,
    Transfer(Width),
    FMove(FKind),
    VMove {
        store: bool,
    },
    Lea {
        w: Width,
        form: LeaForm,
    },
    LoadQInc,
    LoadPair(PairW),
    StorePair(PairW),
    Push,
    Pop,
    PushV,
    PopV,
    PushCalleeSaves,
    PopCalleeSaves,
    Peek,
    Poke,
    TlsLoad(Width),
    TlsStore(Width),
    TlsLea,

    Add(Width),
    Sub(Width),
    Mul(Width),
    And(Width),
    Or(Width),
    Xor(Width),
    FBit {
        or: bool,
        k: FKind,
    },
    Not(Width),
    Neg(Width),
    Shift {
        w: Width,
        op: ShiftOp,
    },
    Bswap(Width),
    Adc,
    Sbb,
    MulHigh {
        signed: bool,
    },
    MulWide {
        signed: bool,
    },
    AluS {
        op: AluOp,
        w: Width,
    },
    RiscAluS {
        op: AluOp,
        w: Width,
    },
    AddShifted,
    Cqo {
        quad: bool,
    },
    DivMod1 {
        signed: bool,
        w: Width,
    },
    Div {
        signed: bool,
        w: Width,
    },
    Rem {
        signed: bool,
        w: Width,
    },
    IntSet {
        w: Width,
        cc: IntCc,
    },
    TestSet {
        w: Width,
        test: TestKind,
    },
    Cmov {
        zero: bool,
    },
    BitCount {
        w: Width,
        trailing: bool,
    },
    Popcnt(Width),
    Bfi,

    IntBranch {
        w: Width,
        cc: IntCc,
    },
    TestBranch {
        w: Width,
        test: TestKind,
    },
    OpBranch {
        op: FlagAlu,
        w: Width,
        flag: PredFlag,
    },
    FlagBranch(PredFlag),
    BranchF {
        cc: FCc,
        k: FKind,
    },
    Jmp,
    Call,
    Ret,
    Break,
    Nop,

    FArith {
        op: FAlu,
        k: FKind,
    },
    Fma {
        op: FmaOp,
        k: FKind,
    },
    FSqrt(FKind),
    FRound {
        k: FKind,
        mode: RoundMode,
    },
    FAbs {
        k: FKind,
        negate: bool,
    },
    FSet {
        cc: FCc,
        k: FKind,
    },
    CvtFI {
        k: FKind,
        w: Width,
    },
    CvtQuad(FKind),
    CvtIF {
        signed: bool,
        from: Width,
        k: FKind,
    },
    CvtFF {
        from: FKind,
        to: FKind,
    },
    Bitcast(BitcastDir),
    MovDZ,
    TruncQSlow(FKind),
    Btd2i,
    Bcd2i,
    VecExtract(Width),

    AtomicRmw {
        op: AtomicOp,
        w: Width,
    },
    AtomicRmwNot(Width),
    AtomicLoad(Width),
    AtomicCas {
        w: Width,
        branch: bool,
    },
    LoadLinked(Width),
    StoreCond(Width),
    Fence {
        full: bool,
    },
    Pause,
    TagCodePtr,
    TagReturnAddress,
    UntagReturnAddress,
    RemoveCodePtrTag,
    UntagArrayPtr,
    RemoveArrayPtrTag,
}

impl Mnemonic {
    /// Returns the canonical spelling of `self`.
    #[allow(clippy::too_many_lines)]
    pub const fn as_str(self) -> &'static str {
        match self {
            Mnemonic::Move => "move",
            Mnemonic::Load(w) => match w {
                Width::B32 => "loadi",
                _ => "loadq",
            },
            Mnemonic::Store(w) => match w {
                Width::B8 => "storeb",
                Width::B16 => "storeh",
                Width::B32 => "storei",
                Width::B64 => "storeq",
            },
            Mnemonic::Extend { from, to, sx } => match (from, to, sx) {
                (Width::B32, _, Sx::Sign) => "loadis",
                (Width::B8, Width::B64, Sx::Sign) => "loadbsq",
                (Width::B16, Width::B64, Sx::Sign) => "loadhsq",
                (Width::B8, _, Sx::Sign) => "loadbsi",
                (Width::B16, _, Sx::Sign) => "loadhsi",
                (Width::B8, Width::B64, Sx::Zero) => "zxb2q",
                (Width::B16, Width::B64, Sx::Zero) => "zxh2q",
                (Width::B8, _, Sx::Zero) => "loadb",
                (_, _, Sx::Zero) => "loadh",
                _ => "loadis",
            },
            Mnemonic::MovZero32 => "zxi2q",
            Mnemonic::Transfer(w) => match w {
                Width::B32 => "transferi",
                _ => "transferq",
            },
            Mnemonic::FMove(k) => match k {
                FKind::F32 => "loadf",
                FKind::F64 => "moved",
            },
            Mnemonic::VMove { store: false } => "loadv",
            Mnemonic::VMove { store: true } => "storev",
            Mnemonic::Lea { w, form } => match (w, form) {
                (Width::B32, _) => "leai",
                (_, LeaForm::Plain) => "leap",
                (_, LeaForm::PcRel) => "pcrtoaddr",
                (_, LeaForm::Global) => "globaladdr",
                (_, LeaForm::La) => "la",
            },
            Mnemonic::LoadQInc => "loadqinc",
            Mnemonic::LoadPair(w) => match w {
                PairW::B32 => "loadpairi",
                PairW::B64 => "loadpairq",
                PairW::F64 => "loadpaird",
                PairW::V128 => "loadpairv",
            },
            Mnemonic::StorePair(w) => match w {
                PairW::B32 => "storepairi",
                PairW::B64 => "storepairq",
                PairW::F64 => "storepaird",
                PairW::V128 => "storepairv",
            },
            Mnemonic::Push => "push",
            Mnemonic::Pop => "pop",
            Mnemonic::PushV => "pushv",
            Mnemonic::PopV => "popv",
            Mnemonic::PushCalleeSaves => "pushCalleeSaves",
            Mnemonic::PopCalleeSaves => "popCalleeSaves",
            Mnemonic::Peek => "peek",
            Mnemonic::Poke => "poke",
            Mnemonic::TlsLoad(w) => match w {
                Width::B8 => "tls_loadb",
                Width::B16 => "tls_loadh",
                Width::B32 => "tls_loadi",
                Width::B64 => "tls_loadp",
            },
            Mnemonic::TlsStore(w) => match w {
                Width::B8 => "tls_storeb",
                Width::B16 => "tls_storeh",
                Width::B32 => "tls_storei",
                Width::B64 => "tls_storep",
            },
            Mnemonic::TlsLea => "tls_leap",

            Mnemonic::Add(w) => width_alu(w, "addi", "addq"),
            Mnemonic::Sub(w) => width_alu(w, "subi", "subq"),
            Mnemonic::Mul(w) => width_alu(w, "muli", "mulq"),
            Mnemonic::And(w) => width_alu(w, "andi", "andq"),
            Mnemonic::Or(w) => match w {
                Width::B16 => "orh",
                Width::B32 => "ori",
                _ => "orq",
            },
            Mnemonic::Xor(w) => width_alu(w, "xori", "xorq"),
            Mnemonic::FBit { or, k } => match (or, k) {
                (true, FKind::F32) => "orf",
                (true, FKind::F64) => "ord",
                (false, FKind::F32) => "andf",
                (false, FKind::F64) => "andd",
            },
            Mnemonic::Not(w) => width_alu(w, "noti", "notq"),
            Mnemonic::Neg(w) => width_alu(w, "negi", "negq"),
            Mnemonic::Shift { w, op } => match (op, w) {
                (ShiftOp::Shl, Width::B32) => "lshifti",
                (ShiftOp::Shl, _) => "lshiftq",
                (ShiftOp::ShrSar, Width::B32) => "rshifti",
                (ShiftOp::ShrSar, _) => "rshiftq",
                (ShiftOp::Shr, Width::B32) => "urshifti",
                (ShiftOp::Shr, _) => "urshiftq",
                (ShiftOp::Rotl, Width::B32) => "lrotatei",
                (ShiftOp::Rotl, _) => "lrotateq",
                (ShiftOp::Rotr, Width::B32) => "rrotatei",
                (ShiftOp::Rotr, _) => "rrotateq",
            },
            Mnemonic::Bswap(w) => width_alu(w, "bswapi", "bswapq"),
            Mnemonic::Adc => "adcq",
            Mnemonic::Sbb => "sbcq",
            Mnemonic::MulHigh { signed: false } => "umulhq",
            Mnemonic::MulHigh { signed: true } => "smulhq",
            Mnemonic::MulWide { signed: false } => "umulli",
            Mnemonic::MulWide { signed: true } => "smulli",
            Mnemonic::AluS { op, .. } => match op {
                AluOp::Sub => "subqs",
                _ => "addqs",
            },
            Mnemonic::RiscAluS { op, w } => match (op, w) {
                (AluOp::Add, Width::B64) => "addps",
                (AluOp::Add, _) => "addis",
                (AluOp::Sub, _) => "subis",
                (AluOp::Or, _) => "oris",
            },
            Mnemonic::AddShifted => "addlshiftp",
            Mnemonic::Cqo { quad: false } => "cdqi",
            Mnemonic::Cqo { quad: true } => "cqoq",
            Mnemonic::DivMod1 { signed, w } => match (signed, w) {
                (true, Width::B32) => "idivi",
                (false, Width::B32) => "udivi",
                (true, _) => "idivq",
                (false, _) => "udivq",
            },
            Mnemonic::Div { signed, w } => match (signed, w) {
                (false, Width::B32) => "divi",
                (true, Width::B32) => "divis",
                (false, _) => "divq",
                (true, _) => "divqs",
            },
            Mnemonic::Rem { signed, w } => match (signed, w) {
                (false, Width::B32) => "remi",
                (true, Width::B32) => "remis",
                (false, _) => "remq",
                (true, _) => "remqs",
            },
            Mnemonic::IntSet { w, cc } => int_cc_name(false, w, cc),
            Mnemonic::TestSet { w, test } => test_name(false, w, test),
            Mnemonic::Cmov { zero: true } => "movz",
            Mnemonic::Cmov { zero: false } => "movn",
            Mnemonic::BitCount { w, trailing } => match (trailing, w) {
                (true, Width::B32) => "tzcnti",
                (true, _) => "tzcntq",
                (false, Width::B32) => "lzcnti",
                (false, _) => "lzcntq",
            },
            Mnemonic::Popcnt(w) => width_alu(w, "popcnti", "popcntq"),
            Mnemonic::Bfi => "bfiq",

            Mnemonic::IntBranch { w, cc } => int_cc_name(true, w, cc),
            Mnemonic::TestBranch { w, test } => test_name(true, w, test),
            Mnemonic::OpBranch { op, w, flag } => op_branch_name(op, w, flag),
            Mnemonic::FlagBranch(flag) => match flag {
                PredFlag::O => "bo",
                PredFlag::S => "bs",
                PredFlag::Z => "bz",
                PredFlag::Nz => "bnz",
            },
            Mnemonic::BranchF { cc, k } => match (cc, k) {
                (FCc::Eq, FKind::F32) => "bfeq",
                (FCc::Ne, FKind::F32) => "bfneq",
                (FCc::Gt, FKind::F32) => "bfgt",
                (FCc::Ge, FKind::F32) => "bfgteq",
                (FCc::Lt, FKind::F32) => "bflt",
                (FCc::Le, FKind::F32) => "bflteq",
                (FCc::EqUn, FKind::F32) => "bfequn",
                (FCc::NeUn, FKind::F32) => "bfnequn",
                (FCc::GtUn, FKind::F32) => "bfgtun",
                (FCc::GeUn, FKind::F32) => "bfgtequn",
                (FCc::LtUn, FKind::F32) => "bfltun",
                (FCc::LeUn, FKind::F32) => "bfltequn",
                (FCc::Eq, FKind::F64) => "bdeq",
                (FCc::Ne, FKind::F64) => "bdneq",
                (FCc::Gt, FKind::F64) => "bdgt",
                (FCc::Ge, FKind::F64) => "bdgteq",
                (FCc::Lt, FKind::F64) => "bdlt",
                (FCc::Le, FKind::F64) => "bdlteq",
                (FCc::EqUn, FKind::F64) => "bdequn",
                (FCc::NeUn, FKind::F64) => "bdnequn",
                (FCc::GtUn, FKind::F64) => "bdgtun",
                (FCc::GeUn, FKind::F64) => "bdgtequn",
                (FCc::LtUn, FKind::F64) => "bdltun",
                (FCc::LeUn, FKind::F64) => "bdltequn",
            },
            Mnemonic::Jmp => "jmp",
            Mnemonic::Call => "call",
            Mnemonic::Ret => "ret",
            Mnemonic::Break => "break",
            Mnemonic::Nop => "nop",

            Mnemonic::FArith { op, k } => match (op, k) {
                (FAlu::Add, FKind::F32) => "addf",
                (FAlu::Add, FKind::F64) => "addd",
                (FAlu::Sub, FKind::F32) => "subf",
                (FAlu::Sub, FKind::F64) => "subd",
                (FAlu::Mul, FKind::F32) => "mulf",
                (FAlu::Mul, FKind::F64) => "muld",
                (FAlu::Div, FKind::F32) => "divf",
                (FAlu::Div, FKind::F64) => "divd",
                (FAlu::Min, FKind::F32) => "fmin",
                (FAlu::Min, FKind::F64) => "dmin",
                (FAlu::Max, FKind::F32) => "fmax",
                (FAlu::Max, FKind::F64) => "dmax",
            },
            Mnemonic::Fma { op, k } => match (op, k) {
                (FmaOp::Add, FKind::F32) => "fmaddf",
                (FmaOp::Add, FKind::F64) => "fmaddd",
                (FmaOp::Sub, FKind::F32) => "fmsubf",
                (FmaOp::Sub, FKind::F64) => "fmsubd",
                (FmaOp::NegAdd, FKind::F32) => "fnmaddf",
                (FmaOp::NegAdd, FKind::F64) => "fnmaddd",
                (FmaOp::NegSub, FKind::F32) => "fnmsubf",
                (FmaOp::NegSub, FKind::F64) => "fnmsubd",
            },
            Mnemonic::FSqrt(FKind::F32) => "sqrtf",
            Mnemonic::FSqrt(FKind::F64) => "sqrtd",
            Mnemonic::FRound { k, mode } => round_name(k, mode),
            Mnemonic::FAbs { k, negate } => match (negate, k) {
                (false, FKind::F32) => "absf",
                (false, FKind::F64) => "absd",
                (true, FKind::F32) => "negf",
                (true, FKind::F64) => "negd",
            },
            Mnemonic::FSet { cc, k } => match (cc, k) {
                (FCc::Eq, FKind::F32) => "cfeq",
                (FCc::Ne, FKind::F32) => "cfneq",
                (FCc::Gt, FKind::F32) => "cfgt",
                (FCc::Ge, FKind::F32) => "cfgteq",
                (FCc::Lt, FKind::F32) => "cflt",
                (FCc::Le, FKind::F32) => "cflteq",
                (FCc::NeUn, FKind::F32) => "cfnequn",
                (_, FKind::F32) => "cfnequn",
                (FCc::Eq, FKind::F64) => "cdeq",
                (FCc::Ne, FKind::F64) => "cdneq",
                (FCc::Gt, FKind::F64) => "cdgt",
                (FCc::Ge, FKind::F64) => "cdgteq",
                (FCc::Lt, FKind::F64) => "cdlt",
                (FCc::Le, FKind::F64) => "cdlteq",
                (_, FKind::F64) => "cdnequn",
            },
            Mnemonic::CvtFI { k, w } => match (k, w) {
                (FKind::F32, Width::B32) => "truncatef2is",
                (FKind::F64, Width::B32) => "truncated2is",
                (FKind::F32, _) => "truncatef2i",
                (FKind::F64, _) => "truncated2i",
            },
            Mnemonic::CvtQuad(FKind::F32) => "cq2f",
            Mnemonic::CvtQuad(FKind::F64) => "cq2d",
            Mnemonic::CvtIF { from, k, .. } => match (from, k) {
                (Width::B32, FKind::F32) => "ci2fs",
                (Width::B32, FKind::F64) => "ci2ds",
                (_, FKind::F32) => "ci2f",
                (_, FKind::F64) => "ci2d",
            },
            Mnemonic::CvtFF { from, .. } => match from {
                FKind::F32 => "cf2d",
                FKind::F64 => "cd2f",
            },
            Mnemonic::Bitcast(dir) => match dir {
                BitcastDir::Q2D => "fq2d",
                BitcastDir::D2Q => "fd2q",
                BitcastDir::I2F => "fi2f",
                BitcastDir::F2I => "ff2i",
            },
            Mnemonic::MovDZ => "movdz",
            Mnemonic::TruncQSlow(FKind::F32) => "truncatef2q",
            Mnemonic::TruncQSlow(FKind::F64) => "truncated2q",
            Mnemonic::Btd2i => "btd2i",
            Mnemonic::Bcd2i => "bcd2i",
            Mnemonic::VecExtract(w) => match w {
                Width::B8 => "umovb",
                Width::B16 => "umovh",
                Width::B32 => "umovi",
                Width::B64 => "umovq",
            },

            Mnemonic::AtomicRmw { op, w } => atomic_rmw_name(op, w),
            Mnemonic::AtomicRmwNot(w) => match w {
                Width::B8 => "atomicxchgclearb",
                Width::B16 => "atomicxchgclearh",
                Width::B32 => "atomicxchgcleari",
                Width::B64 => "atomicxchgclearq",
            },
            Mnemonic::AtomicLoad(w) => match w {
                Width::B8 => "atomicloadb",
                Width::B16 => "atomicloadh",
                Width::B32 => "atomicloadi",
                Width::B64 => "atomicloadq",
            },
            Mnemonic::AtomicCas { w, branch: true } => match w {
                Width::B8 => "batomicweakcasb",
                Width::B16 => "batomicweakcash",
                Width::B32 => "batomicweakcasi",
                Width::B64 => "batomicweakcasq",
            },
            Mnemonic::AtomicCas { w, branch: false } => match w {
                Width::B8 => "atomicweakcasb",
                Width::B16 => "atomicweakcash",
                Width::B32 => "atomicweakcasi",
                Width::B64 => "atomicweakcasq",
            },
            Mnemonic::LoadLinked(w) => match w {
                Width::B8 => "loadlinkacqb",
                Width::B16 => "loadlinkacqh",
                Width::B32 => "loadlinkacqi",
                Width::B64 => "loadlinkacqq",
            },
            Mnemonic::StoreCond(w) => match w {
                Width::B8 => "storecondrelb",
                Width::B16 => "storecondrelh",
                Width::B32 => "storecondreli",
                Width::B64 => "storecondrelq",
            },
            Mnemonic::Fence { full: true } => "memfence",
            Mnemonic::Fence { full: false } => "fence",
            Mnemonic::Pause => "pause",
            Mnemonic::TagCodePtr => "tagCodePtr",
            Mnemonic::TagReturnAddress => "tagReturnAddress",
            Mnemonic::UntagReturnAddress => "untagReturnAddress",
            Mnemonic::RemoveCodePtrTag => "removeCodePtrTag",
            Mnemonic::UntagArrayPtr => "untagArrayPtr",
            Mnemonic::RemoveArrayPtrTag => "removeArrayPtrTag",
        }
    }
}

const fn width_alu(w: Width, i: &'static str, q: &'static str) -> &'static str {
    match w {
        Width::B32 => i,
        _ => q,
    }
}

const fn int_cc_name(branch: bool, w: Width, cc: IntCc) -> &'static str {
    match (branch, w, cc) {
        (true, Width::B8, IntCc::Eq) => "bbeq",
        (true, Width::B8, IntCc::Ne) => "bbneq",
        (true, Width::B8, IntCc::Hi) => "bba",
        (true, Width::B8, IntCc::Hs) => "bbaeq",
        (true, Width::B8, IntCc::Lo) => "bbb",
        (true, Width::B8, IntCc::Ls) => "bbbeq",
        (true, Width::B8, IntCc::Gt) => "bbgt",
        (true, Width::B8, IntCc::Ge) => "bbgteq",
        (true, Width::B8, IntCc::Lt) => "bblt",
        (true, Width::B8, IntCc::Le) => "bblteq",
        (true, Width::B32, IntCc::Eq) => "bieq",
        (true, Width::B32, IntCc::Ne) => "bineq",
        (true, Width::B32, IntCc::Hi) => "bia",
        (true, Width::B32, IntCc::Hs) => "biaeq",
        (true, Width::B32, IntCc::Lo) => "bib",
        (true, Width::B32, IntCc::Ls) => "bibeq",
        (true, Width::B32, IntCc::Gt) => "bigt",
        (true, Width::B32, IntCc::Ge) => "bigteq",
        (true, Width::B32, IntCc::Lt) => "bilt",
        (true, Width::B32, IntCc::Le) => "bilteq",
        (true, _, IntCc::Eq) => "bqeq",
        (true, _, IntCc::Ne) => "bqneq",
        (true, _, IntCc::Hi) => "bqa",
        (true, _, IntCc::Hs) => "bqaeq",
        (true, _, IntCc::Lo) => "bqb",
        (true, _, IntCc::Ls) => "bqbeq",
        (true, _, IntCc::Gt) => "bqgt",
        (true, _, IntCc::Ge) => "bqgteq",
        (true, _, IntCc::Lt) => "bqlt",
        (true, _, IntCc::Le) => "bqlteq",
        (false, Width::B8, IntCc::Eq) => "cbeq",
        (false, Width::B8, IntCc::Ne) => "cbneq",
        (false, Width::B8, IntCc::Hi) => "cba",
        (false, Width::B8, IntCc::Hs) => "cbaeq",
        (false, Width::B8, IntCc::Lo) => "cbb",
        (false, Width::B8, IntCc::Ls) => "cbbeq",
        (false, Width::B8, IntCc::Gt) => "cbgt",
        (false, Width::B8, IntCc::Ge) => "cbgteq",
        (false, Width::B8, IntCc::Lt) => "cblt",
        (false, Width::B8, IntCc::Le) => "cblteq",
        (false, Width::B32, IntCc::Eq) => "cieq",
        (false, Width::B32, IntCc::Ne) => "cineq",
        (false, Width::B32, IntCc::Hi) => "cia",
        (false, Width::B32, IntCc::Hs) => "ciaeq",
        (false, Width::B32, IntCc::Lo) => "cib",
        (false, Width::B32, IntCc::Ls) => "cibeq",
        (false, Width::B32, IntCc::Gt) => "cigt",
        (false, Width::B32, IntCc::Ge) => "cigteq",
        (false, Width::B32, IntCc::Lt) => "cilt",
        (false, Width::B32, IntCc::Le) => "cilteq",
        (false, _, IntCc::Eq) => "cqeq",
        (false, _, IntCc::Ne) => "cqneq",
        (false, _, IntCc::Hi) => "cqa",
        (false, _, IntCc::Hs) => "cqaeq",
        (false, _, IntCc::Lo) => "cqb",
        (false, _, IntCc::Ls) => "cqbeq",
        (false, _, IntCc::Gt) => "cqgt",
        (false, _, IntCc::Ge) => "cqgteq",
        (false, _, IntCc::Lt) => "cqlt",
        (false, _, IntCc::Le) => "cqlteq",
    }
}

const fn test_name(branch: bool, w: Width, test: TestKind) -> &'static str {
    match (branch, w, test) {
        (false, Width::B8, TestKind::Sign) => "tbs",
        (false, Width::B8, TestKind::Zero) => "tbz",
        (false, Width::B8, TestKind::NonZero) => "tbnz",
        (false, Width::B32, TestKind::Sign) => "tis",
        (false, Width::B32, TestKind::Zero) => "tiz",
        (false, Width::B32, TestKind::NonZero) => "tinz",
        (false, _, TestKind::Sign) => "tqs",
        (false, _, TestKind::Zero) => "tqz",
        (false, _, TestKind::NonZero) => "tqnz",
        (true, Width::B8, TestKind::Sign) => "btbs",
        (true, Width::B8, TestKind::Zero) => "btbz",
        (true, Width::B8, TestKind::NonZero) => "btbnz",
        (true, Width::B32, TestKind::Sign) => "btis",
        (true, Width::B32, TestKind::Zero) => "btiz",
        (true, Width::B32, TestKind::NonZero) => "btinz",
        (true, _, TestKind::Sign) => "btqs",
        (true, _, TestKind::Zero) => "btqz",
        (true, _, TestKind::NonZero) => "btqnz",
    }
}

const fn op_branch_name(op: FlagAlu, w: Width, flag: PredFlag) -> &'static str {
    match (op, w, flag) {
        (FlagAlu::Add, Width::B32, PredFlag::O) => "baddio",
        (FlagAlu::Add, Width::B32, PredFlag::S) => "baddis",
        (FlagAlu::Add, Width::B32, PredFlag::Z) => "baddiz",
        (FlagAlu::Add, Width::B32, PredFlag::Nz) => "baddinz",
        (FlagAlu::Add, _, PredFlag::O) => "baddqo",
        (FlagAlu::Add, _, PredFlag::S) => "baddqs",
        (FlagAlu::Add, _, PredFlag::Z) => "baddqz",
        (FlagAlu::Add, _, PredFlag::Nz) => "baddqnz",
        (FlagAlu::Sub, Width::B32, PredFlag::O) => "bsubio",
        (FlagAlu::Sub, _, PredFlag::O) => "bsubqo",
        (FlagAlu::Sub, Width::B32, PredFlag::S) => "bsubis",
        (FlagAlu::Sub, _, PredFlag::S) => "bsubqs",
        (FlagAlu::Sub, Width::B32, PredFlag::Z) => "bsubiz",
        (FlagAlu::Sub, _, PredFlag::Z) => "bsubqz",
        (FlagAlu::Sub, Width::B32, PredFlag::Nz) => "bsubinz",
        (FlagAlu::Sub, _, PredFlag::Nz) => "bsubqnz",
        (FlagAlu::Mul, Width::B32, PredFlag::O) => "bmulio",
        (FlagAlu::Mul, _, PredFlag::O) => "bmulqo",
        (FlagAlu::Mul, Width::B32, PredFlag::S) => "bmulis",
        (FlagAlu::Mul, _, PredFlag::S) => "bmulqs",
        (FlagAlu::Mul, Width::B32, PredFlag::Z) => "bmuliz",
        (FlagAlu::Mul, _, PredFlag::Z) => "bmulqz",
        (FlagAlu::Mul, Width::B32, PredFlag::Nz) => "bmulinz",
        (FlagAlu::Mul, _, PredFlag::Nz) => "bmulqnz",
        (FlagAlu::Or, Width::B32, PredFlag::O) => "borio",
        (FlagAlu::Or, _, PredFlag::O) => "borqo",
        (FlagAlu::Or, Width::B32, PredFlag::S) => "boris",
        (FlagAlu::Or, _, PredFlag::S) => "borqs",
        (FlagAlu::Or, Width::B32, PredFlag::Z) => "boriz",
        (FlagAlu::Or, _, PredFlag::Z) => "borqz",
        (FlagAlu::Or, Width::B32, PredFlag::Nz) => "borinz",
        (FlagAlu::Or, _, PredFlag::Nz) => "borqnz",
    }
}

const fn round_name(k: FKind, mode: RoundMode) -> &'static str {
    match (k, mode) {
        (FKind::F32, RoundMode::Nearest) => "roundf",
        (FKind::F32, RoundMode::Down) => "floorf",
        (FKind::F32, RoundMode::Up) => "ceilf",
        (FKind::F32, RoundMode::Trunc) => "truncatef",
        (FKind::F64, RoundMode::Nearest) => "roundd",
        (FKind::F64, RoundMode::Down) => "floord",
        (FKind::F64, RoundMode::Up) => "ceild",
        (FKind::F64, RoundMode::Trunc) => "truncated",
    }
}

const fn atomic_rmw_name(op: AtomicOp, w: Width) -> &'static str {
    match (op, w) {
        (AtomicOp::Add, Width::B8) => "atomicxchgaddb",
        (AtomicOp::Add, Width::B16) => "atomicxchgaddh",
        (AtomicOp::Add, Width::B32) => "atomicxchgaddi",
        (AtomicOp::Add, Width::B64) => "atomicxchgaddq",
        (AtomicOp::Sub, Width::B8) => "atomicxchgsubb",
        (AtomicOp::Sub, Width::B16) => "atomicxchgsubh",
        (AtomicOp::Sub, Width::B32) => "atomicxchgsubi",
        (AtomicOp::Sub, Width::B64) => "atomicxchgsubq",
        (AtomicOp::Xchg, Width::B8) => "atomicxchgb",
        (AtomicOp::Xchg, Width::B16) => "atomicxchgh",
        (AtomicOp::Xchg, Width::B32) => "atomicxchgi",
        (AtomicOp::Xchg, Width::B64) => "atomicxchgq",
        (AtomicOp::Or, Width::B8) => "atomicxchgorb",
        (AtomicOp::Or, Width::B16) => "atomicxchgorh",
        (AtomicOp::Or, Width::B32) => "atomicxchgori",
        (AtomicOp::Or, Width::B64) => "atomicxchgorq",
        (AtomicOp::Xor, Width::B8) => "atomicxchgxorb",
        (AtomicOp::Xor, Width::B16) => "atomicxchgxorh",
        (AtomicOp::Xor, Width::B32) => "atomicxchgxori",
        (AtomicOp::Xor, Width::B64) => "atomicxchgxorq",
        (AtomicOp::And, Width::B8) => "atomicxchgclearb",
        (AtomicOp::And, Width::B16) => "atomicxchgclearh",
        (AtomicOp::And, Width::B32) => "atomicxchgcleari",
        (AtomicOp::And, Width::B64) => "atomicxchgclearq",
    }
}

impl std::fmt::Display for Mnemonic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

macro_rules! mnemonic_table {
    ($( $name:ident $spelling:literal => $value:expr ; )*) => {

        #[allow(non_upper_case_globals, non_snake_case)]
        pub mod mnem {
            use super::*;

            $( pub const $name: Mnemonic = $value; )*
        }

        impl Mnemonic {
            /// Parses a mnemonic spelling into its operation.
            ///
            /// # Errors
            ///
            /// [`ExpandError::UnknownMnemonic`] if `s` is not one of
            /// [`SUPPORTED_MNEMONICS`].
            #[allow(clippy::should_implement_trait, clippy::too_many_lines,
                    clippy::match_same_arms)]
            pub fn from_str(s: &str) -> Result<Self, ExpandError> {
                match s {
                    $( $spelling => Ok($value), )*
                    other => Err(ExpandError::UnknownMnemonic(other.to_string())),
                }
            }
        }

        /// Lists every mnemonic spelling both assemblers accept, in reference order.
        ///
        /// One spelling can share a [`Mnemonic`] value with another (see
        /// [`Mnemonic::as_str`]). This list defines the accepted spellings.
        pub const SUPPORTED_MNEMONICS: &[&str] = &[ $( $spelling, )* ];
    };
}

mnemonic_table! {
    addi "addi" => Mnemonic::Add(Width::B32);
    addp "addp" => Mnemonic::Add(Width::B64);
    addq "addq" => Mnemonic::Add(Width::B64);
    andi "andi" => Mnemonic::And(Width::B32);
    andp "andp" => Mnemonic::And(Width::B64);
    andq "andq" => Mnemonic::And(Width::B64);
    andf "andf" => Mnemonic::FBit { or: false, k: FKind::F32 };
    andd "andd" => Mnemonic::FBit { or: false, k: FKind::F64 };
    lshifti "lshifti" => Mnemonic::Shift { w: Width::B32, op: ShiftOp::Shl };
    lshiftp "lshiftp" => Mnemonic::Shift { w: Width::B64, op: ShiftOp::Shl };
    lshiftq "lshiftq" => Mnemonic::Shift { w: Width::B64, op: ShiftOp::Shl };
    muli "muli" => Mnemonic::Mul(Width::B32);
    mulp "mulp" => Mnemonic::Mul(Width::B64);
    mulq "mulq" => Mnemonic::Mul(Width::B64);
    negi "negi" => Mnemonic::Neg(Width::B32);
    negp "negp" => Mnemonic::Neg(Width::B64);
    negq "negq" => Mnemonic::Neg(Width::B64);
    noti "noti" => Mnemonic::Not(Width::B32);
    notq "notq" => Mnemonic::Not(Width::B64);
    bswapi "bswapi" => Mnemonic::Bswap(Width::B32);
    bswapq "bswapq" => Mnemonic::Bswap(Width::B64);
    ori "ori" => Mnemonic::Or(Width::B32);
    orp "orp" => Mnemonic::Or(Width::B64);
    orq "orq" => Mnemonic::Or(Width::B64);
    orh "orh" => Mnemonic::Or(Width::B16);
    orf "orf" => Mnemonic::FBit { or: true, k: FKind::F32 };
    ord "ord" => Mnemonic::FBit { or: true, k: FKind::F64 };
    rshifti "rshifti" => Mnemonic::Shift { w: Width::B32, op: ShiftOp::ShrSar };
    rshiftp "rshiftp" => Mnemonic::Shift { w: Width::B64, op: ShiftOp::ShrSar };
    rshiftq "rshiftq" => Mnemonic::Shift { w: Width::B64, op: ShiftOp::ShrSar };
    urshifti "urshifti" => Mnemonic::Shift { w: Width::B32, op: ShiftOp::Shr };
    urshiftp "urshiftp" => Mnemonic::Shift { w: Width::B64, op: ShiftOp::Shr };
    urshiftq "urshiftq" => Mnemonic::Shift { w: Width::B64, op: ShiftOp::Shr };
    lrotatei "lrotatei" => Mnemonic::Shift { w: Width::B32, op: ShiftOp::Rotl };
    lrotateq "lrotateq" => Mnemonic::Shift { w: Width::B64, op: ShiftOp::Rotl };
    rrotatei "rrotatei" => Mnemonic::Shift { w: Width::B32, op: ShiftOp::Rotr };
    rrotateq "rrotateq" => Mnemonic::Shift { w: Width::B64, op: ShiftOp::Rotr };
    subi "subi" => Mnemonic::Sub(Width::B32);
    subp "subp" => Mnemonic::Sub(Width::B64);
    subq "subq" => Mnemonic::Sub(Width::B64);
    xori "xori" => Mnemonic::Xor(Width::B32);
    xorp "xorp" => Mnemonic::Xor(Width::B64);
    xorq "xorq" => Mnemonic::Xor(Width::B64);
    adcq "adcq" => Mnemonic::Adc;
    sbcq "sbcq" => Mnemonic::Sbb;
    umulhq "umulhq" => Mnemonic::MulHigh { signed: false };
    smulhq "smulhq" => Mnemonic::MulHigh { signed: true };
    smulli "smulli" => Mnemonic::MulWide { signed: true };
    umulli "umulli" => Mnemonic::MulWide { signed: false };
    addqs "addqs" => Mnemonic::AluS { op: AluOp::Add, w: Width::B64 };
    subqs "subqs" => Mnemonic::AluS { op: AluOp::Sub, w: Width::B64 };
    addlshiftp "addlshiftp" => Mnemonic::AddShifted;
    addis "addis" => Mnemonic::RiscAluS { op: AluOp::Add, w: Width::B32 };
    subis "subis" => Mnemonic::RiscAluS { op: AluOp::Sub, w: Width::B32 };
    oris "oris" => Mnemonic::RiscAluS { op: AluOp::Or, w: Width::B32 };
    addps "addps" => Mnemonic::RiscAluS { op: AluOp::Add, w: Width::B64 };
    divi "divi" => Mnemonic::Div { signed: false, w: Width::B32 };
    divis "divis" => Mnemonic::Div { signed: true, w: Width::B32 };
    divq "divq" => Mnemonic::Div { signed: false, w: Width::B64 };
    divqs "divqs" => Mnemonic::Div { signed: true, w: Width::B64 };
    remi "remi" => Mnemonic::Rem { signed: false, w: Width::B32 };
    remis "remis" => Mnemonic::Rem { signed: true, w: Width::B32 };
    remq "remq" => Mnemonic::Rem { signed: false, w: Width::B64 };
    remqs "remqs" => Mnemonic::Rem { signed: true, w: Width::B64 };
    cdqi "cdqi" => Mnemonic::Cqo { quad: false };
    cqoq "cqoq" => Mnemonic::Cqo { quad: true };
    idivi "idivi" => Mnemonic::DivMod1 { signed: true, w: Width::B32 };
    udivi "udivi" => Mnemonic::DivMod1 { signed: false, w: Width::B32 };
    idivq "idivq" => Mnemonic::DivMod1 { signed: true, w: Width::B64 };
    udivq "udivq" => Mnemonic::DivMod1 { signed: false, w: Width::B64 };
    slt "slt" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Lt };
    sltu "sltu" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Lo };
    movz "movz" => Mnemonic::Cmov { zero: true };
    movn "movn" => Mnemonic::Cmov { zero: false };
    cmov "cmov" => Mnemonic::Cmov { zero: false };
    cmovz "cmovz" => Mnemonic::Cmov { zero: true };
    bfiq "bfiq" => Mnemonic::Bfi;
    leai "leai" => Mnemonic::Lea { w: Width::B32, form: LeaForm::Plain };
    leap "leap" => Mnemonic::Lea { w: Width::B64, form: LeaForm::Plain };
    pcrtoaddr "pcrtoaddr" => Mnemonic::Lea { w: Width::B64, form: LeaForm::PcRel };
    globaladdr "globaladdr" => Mnemonic::Lea { w: Width::B64, form: LeaForm::Global };
    la "la" => Mnemonic::Lea { w: Width::B64, form: LeaForm::La };
    loadi "loadi" => Mnemonic::Load(Width::B32);
    atomicloadi "atomicloadi" => Mnemonic::AtomicLoad(Width::B32);
    loadp "loadp" => Mnemonic::Load(Width::B64);
    loadq "loadq" => Mnemonic::Load(Width::B64);
    atomicloadq "atomicloadq" => Mnemonic::AtomicLoad(Width::B64);
    storei "storei" => Mnemonic::Store(Width::B32);
    storep "storep" => Mnemonic::Store(Width::B64);
    storeq "storeq" => Mnemonic::Store(Width::B64);
    storeh "storeh" => Mnemonic::Store(Width::B16);
    storeb "storeb" => Mnemonic::Store(Width::B8);
    loadis "loadis" => Mnemonic::Extend { from: Width::B32, to: Width::B64, sx: Sx::Sign };
    loadb "loadb" => Mnemonic::Extend { from: Width::B8, to: Width::B32, sx: Sx::Zero };
    atomicloadb "atomicloadb" => Mnemonic::AtomicLoad(Width::B8);
    loadbsi "loadbsi" => Mnemonic::Extend { from: Width::B8, to: Width::B32, sx: Sx::Sign };
    loadbsq "loadbsq" => Mnemonic::Extend { from: Width::B8, to: Width::B64, sx: Sx::Sign };
    loadh "loadh" => Mnemonic::Extend { from: Width::B16, to: Width::B32, sx: Sx::Zero };
    atomicloadh "atomicloadh" => Mnemonic::AtomicLoad(Width::B16);
    loadhsi "loadhsi" => Mnemonic::Extend { from: Width::B16, to: Width::B32, sx: Sx::Sign };
    loadhsq "loadhsq" => Mnemonic::Extend { from: Width::B16, to: Width::B64, sx: Sx::Sign };
    transferi "transferi" => Mnemonic::Transfer(Width::B32);
    transferq "transferq" => Mnemonic::Transfer(Width::B64);
    transferp "transferp" => Mnemonic::Transfer(Width::B64);
    sxi2q "sxi2q" => Mnemonic::Extend { from: Width::B32, to: Width::B64, sx: Sx::Sign };
    zxi2q "zxi2q" => Mnemonic::MovZero32;
    sxb2i "sxb2i" => Mnemonic::Extend { from: Width::B8, to: Width::B32, sx: Sx::Sign };
    sxh2i "sxh2i" => Mnemonic::Extend { from: Width::B16, to: Width::B32, sx: Sx::Sign };
    sxb2q "sxb2q" => Mnemonic::Extend { from: Width::B8, to: Width::B64, sx: Sx::Sign };
    sxb2p "sxb2p" => Mnemonic::Extend { from: Width::B8, to: Width::B64, sx: Sx::Sign };
    sxh2q "sxh2q" => Mnemonic::Extend { from: Width::B16, to: Width::B64, sx: Sx::Sign };
    zxb2i "zxb2i" => Mnemonic::Extend { from: Width::B8, to: Width::B32, sx: Sx::Zero };
    zxh2i "zxh2i" => Mnemonic::Extend { from: Width::B16, to: Width::B32, sx: Sx::Zero };
    zxb2q "zxb2q" => Mnemonic::Extend { from: Width::B8, to: Width::B64, sx: Sx::Zero };
    zxh2q "zxh2q" => Mnemonic::Extend { from: Width::B16, to: Width::B64, sx: Sx::Zero };
    loadf "loadf" => Mnemonic::FMove(FKind::F32);
    storef "storef" => Mnemonic::FMove(FKind::F32);
    loadd "loadd" => Mnemonic::FMove(FKind::F64);
    moved "moved" => Mnemonic::FMove(FKind::F64);
    stored "stored" => Mnemonic::FMove(FKind::F64);
    loadv "loadv" => Mnemonic::VMove { store: false };
    storev "storev" => Mnemonic::VMove { store: true };
    movev "movev" => Mnemonic::VMove { store: false };
    r#move "move" => Mnemonic::Move;
    pop "pop" => Mnemonic::Pop;
    push "push" => Mnemonic::Push;
    popv "popv" => Mnemonic::PopV;
    pushv "pushv" => Mnemonic::PushV;
    pushCalleeSaves "pushCalleeSaves" => Mnemonic::PushCalleeSaves;
    popCalleeSaves "popCalleeSaves" => Mnemonic::PopCalleeSaves;
    peek "peek" => Mnemonic::Peek;
    poke "poke" => Mnemonic::Poke;
    loadqinc "loadqinc" => Mnemonic::LoadQInc;
    loadpairq "loadpairq" => Mnemonic::LoadPair(PairW::B64);
    loadpairp "loadpairp" => Mnemonic::LoadPair(PairW::B64);
    loadpairi "loadpairi" => Mnemonic::LoadPair(PairW::B32);
    loadpaird "loadpaird" => Mnemonic::LoadPair(PairW::F64);
    loadpairv "loadpairv" => Mnemonic::LoadPair(PairW::V128);
    storepairq "storepairq" => Mnemonic::StorePair(PairW::B64);
    storepairp "storepairp" => Mnemonic::StorePair(PairW::B64);
    storepairi "storepairi" => Mnemonic::StorePair(PairW::B32);
    storepaird "storepaird" => Mnemonic::StorePair(PairW::F64);
    storepairv "storepairv" => Mnemonic::StorePair(PairW::V128);
    addf "addf" => Mnemonic::FArith { op: FAlu::Add, k: FKind::F32 };
    addd "addd" => Mnemonic::FArith { op: FAlu::Add, k: FKind::F64 };
    divf "divf" => Mnemonic::FArith { op: FAlu::Div, k: FKind::F32 };
    divd "divd" => Mnemonic::FArith { op: FAlu::Div, k: FKind::F64 };
    subf "subf" => Mnemonic::FArith { op: FAlu::Sub, k: FKind::F32 };
    subd "subd" => Mnemonic::FArith { op: FAlu::Sub, k: FKind::F64 };
    mulf "mulf" => Mnemonic::FArith { op: FAlu::Mul, k: FKind::F32 };
    muld "muld" => Mnemonic::FArith { op: FAlu::Mul, k: FKind::F64 };
    fmin "fmin" => Mnemonic::FArith { op: FAlu::Min, k: FKind::F32 };
    fmax "fmax" => Mnemonic::FArith { op: FAlu::Max, k: FKind::F32 };
    dmin "dmin" => Mnemonic::FArith { op: FAlu::Min, k: FKind::F64 };
    dmax "dmax" => Mnemonic::FArith { op: FAlu::Max, k: FKind::F64 };
    fmaddf "fmaddf" => Mnemonic::Fma { op: FmaOp::Add, k: FKind::F32 };
    fmaddd "fmaddd" => Mnemonic::Fma { op: FmaOp::Add, k: FKind::F64 };
    fmsubf "fmsubf" => Mnemonic::Fma { op: FmaOp::Sub, k: FKind::F32 };
    fmsubd "fmsubd" => Mnemonic::Fma { op: FmaOp::Sub, k: FKind::F64 };
    fnmaddf "fnmaddf" => Mnemonic::Fma { op: FmaOp::NegAdd, k: FKind::F32 };
    fnmaddd "fnmaddd" => Mnemonic::Fma { op: FmaOp::NegAdd, k: FKind::F64 };
    fnmsubf "fnmsubf" => Mnemonic::Fma { op: FmaOp::NegSub, k: FKind::F32 };
    fnmsubd "fnmsubd" => Mnemonic::Fma { op: FmaOp::NegSub, k: FKind::F64 };
    sqrtf "sqrtf" => Mnemonic::FSqrt(FKind::F32);
    sqrtd "sqrtd" => Mnemonic::FSqrt(FKind::F64);
    roundf "roundf" => Mnemonic::FRound { k: FKind::F32, mode: RoundMode::Nearest };
    floorf "floorf" => Mnemonic::FRound { k: FKind::F32, mode: RoundMode::Down };
    ceilf "ceilf" => Mnemonic::FRound { k: FKind::F32, mode: RoundMode::Up };
    truncatef "truncatef" => Mnemonic::FRound { k: FKind::F32, mode: RoundMode::Trunc };
    roundd "roundd" => Mnemonic::FRound { k: FKind::F64, mode: RoundMode::Nearest };
    floord "floord" => Mnemonic::FRound { k: FKind::F64, mode: RoundMode::Down };
    ceild "ceild" => Mnemonic::FRound { k: FKind::F64, mode: RoundMode::Up };
    truncated "truncated" => Mnemonic::FRound { k: FKind::F64, mode: RoundMode::Trunc };
    truncatef2is "truncatef2is" => Mnemonic::CvtFI { k: FKind::F32, w: Width::B32 };
    truncated2is "truncated2is" => Mnemonic::CvtFI { k: FKind::F64, w: Width::B32 };
    truncatef2i "truncatef2i" => Mnemonic::CvtFI { k: FKind::F32, w: Width::B64 };
    truncatef2qs "truncatef2qs" => Mnemonic::CvtFI { k: FKind::F32, w: Width::B64 };
    truncated2i "truncated2i" => Mnemonic::CvtFI { k: FKind::F64, w: Width::B64 };
    truncated2qs "truncated2qs" => Mnemonic::CvtFI { k: FKind::F64, w: Width::B64 };
    truncatef2q "truncatef2q" => Mnemonic::TruncQSlow(FKind::F32);
    truncated2q "truncated2q" => Mnemonic::TruncQSlow(FKind::F64);
    ci2d "ci2d" => Mnemonic::CvtIF { signed: true, from: Width::B64, k: FKind::F64 };
    ci2ds "ci2ds" => Mnemonic::CvtIF { signed: true, from: Width::B32, k: FKind::F64 };
    ci2f "ci2f" => Mnemonic::CvtIF { signed: true, from: Width::B64, k: FKind::F32 };
    cq2fs "cq2fs" => Mnemonic::CvtIF { signed: true, from: Width::B64, k: FKind::F32 };
    ci2fs "ci2fs" => Mnemonic::CvtIF { signed: true, from: Width::B32, k: FKind::F32 };
    cq2d "cq2d" => Mnemonic::CvtQuad(FKind::F64);
    cq2f "cq2f" => Mnemonic::CvtQuad(FKind::F32);
    cq2ds "cq2ds" => Mnemonic::CvtIF { signed: true, from: Width::B64, k: FKind::F64 };
    cd2f "cd2f" => Mnemonic::CvtFF { from: FKind::F64, to: FKind::F32 };
    cf2d "cf2d" => Mnemonic::CvtFF { from: FKind::F32, to: FKind::F64 };
    fq2d "fq2d" => Mnemonic::Bitcast(BitcastDir::Q2D);
    fd2q "fd2q" => Mnemonic::Bitcast(BitcastDir::D2Q);
    fi2f "fi2f" => Mnemonic::Bitcast(BitcastDir::I2F);
    ff2i "ff2i" => Mnemonic::Bitcast(BitcastDir::F2I);
    btd2i "btd2i" => Mnemonic::Btd2i;
    td2i "td2i" => Mnemonic::CvtFI { k: FKind::F64, w: Width::B64 };
    bcd2i "bcd2i" => Mnemonic::Bcd2i;
    movdz "movdz" => Mnemonic::MovDZ;
    absf "absf" => Mnemonic::FAbs { k: FKind::F32, negate: false };
    absd "absd" => Mnemonic::FAbs { k: FKind::F64, negate: false };
    negf "negf" => Mnemonic::FAbs { k: FKind::F32, negate: true };
    negd "negd" => Mnemonic::FAbs { k: FKind::F64, negate: true };
    umovb "umovb" => Mnemonic::VecExtract(Width::B8);
    umovh "umovh" => Mnemonic::VecExtract(Width::B16);
    umovi "umovi" => Mnemonic::VecExtract(Width::B32);
    umovq "umovq" => Mnemonic::VecExtract(Width::B64);
    bieq "bieq" => Mnemonic::IntBranch { w: Width::B32, cc: IntCc::Eq };
    bineq "bineq" => Mnemonic::IntBranch { w: Width::B32, cc: IntCc::Ne };
    bia "bia" => Mnemonic::IntBranch { w: Width::B32, cc: IntCc::Hi };
    biaeq "biaeq" => Mnemonic::IntBranch { w: Width::B32, cc: IntCc::Hs };
    bib "bib" => Mnemonic::IntBranch { w: Width::B32, cc: IntCc::Lo };
    bibeq "bibeq" => Mnemonic::IntBranch { w: Width::B32, cc: IntCc::Ls };
    bigt "bigt" => Mnemonic::IntBranch { w: Width::B32, cc: IntCc::Gt };
    bigteq "bigteq" => Mnemonic::IntBranch { w: Width::B32, cc: IntCc::Ge };
    bilt "bilt" => Mnemonic::IntBranch { w: Width::B32, cc: IntCc::Lt };
    bilteq "bilteq" => Mnemonic::IntBranch { w: Width::B32, cc: IntCc::Le };
    bpeq "bpeq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Eq };
    bpneq "bpneq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Ne };
    bpa "bpa" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Hi };
    bpaeq "bpaeq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Hs };
    bpb "bpb" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Lo };
    bpbeq "bpbeq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Ls };
    bpgt "bpgt" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Gt };
    bpgteq "bpgteq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Ge };
    bplt "bplt" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Lt };
    bplteq "bplteq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Le };
    bqeq "bqeq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Eq };
    bqneq "bqneq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Ne };
    bqa "bqa" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Hi };
    bqaeq "bqaeq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Hs };
    bqb "bqb" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Lo };
    bqbeq "bqbeq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Ls };
    bqgt "bqgt" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Gt };
    bqgteq "bqgteq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Ge };
    bqlt "bqlt" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Lt };
    bqlteq "bqlteq" => Mnemonic::IntBranch { w: Width::B64, cc: IntCc::Le };
    bbeq "bbeq" => Mnemonic::IntBranch { w: Width::B8, cc: IntCc::Eq };
    bbneq "bbneq" => Mnemonic::IntBranch { w: Width::B8, cc: IntCc::Ne };
    bba "bba" => Mnemonic::IntBranch { w: Width::B8, cc: IntCc::Hi };
    bbaeq "bbaeq" => Mnemonic::IntBranch { w: Width::B8, cc: IntCc::Hs };
    bbb "bbb" => Mnemonic::IntBranch { w: Width::B8, cc: IntCc::Lo };
    bbbeq "bbbeq" => Mnemonic::IntBranch { w: Width::B8, cc: IntCc::Ls };
    bbgt "bbgt" => Mnemonic::IntBranch { w: Width::B8, cc: IntCc::Gt };
    bbgteq "bbgteq" => Mnemonic::IntBranch { w: Width::B8, cc: IntCc::Ge };
    bblt "bblt" => Mnemonic::IntBranch { w: Width::B8, cc: IntCc::Lt };
    bblteq "bblteq" => Mnemonic::IntBranch { w: Width::B8, cc: IntCc::Le };
    btis "btis" => Mnemonic::TestBranch { w: Width::B32, test: TestKind::Sign };
    btiz "btiz" => Mnemonic::TestBranch { w: Width::B32, test: TestKind::Zero };
    btinz "btinz" => Mnemonic::TestBranch { w: Width::B32, test: TestKind::NonZero };
    btps "btps" => Mnemonic::TestBranch { w: Width::B64, test: TestKind::Sign };
    btpz "btpz" => Mnemonic::TestBranch { w: Width::B64, test: TestKind::Zero };
    btpnz "btpnz" => Mnemonic::TestBranch { w: Width::B64, test: TestKind::NonZero };
    btqs "btqs" => Mnemonic::TestBranch { w: Width::B64, test: TestKind::Sign };
    btqz "btqz" => Mnemonic::TestBranch { w: Width::B64, test: TestKind::Zero };
    btqnz "btqnz" => Mnemonic::TestBranch { w: Width::B64, test: TestKind::NonZero };
    btbs "btbs" => Mnemonic::TestBranch { w: Width::B8, test: TestKind::Sign };
    btbz "btbz" => Mnemonic::TestBranch { w: Width::B8, test: TestKind::Zero };
    btbnz "btbnz" => Mnemonic::TestBranch { w: Width::B8, test: TestKind::NonZero };
    baddio "baddio" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B32, flag: PredFlag::O };
    baddis "baddis" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B32, flag: PredFlag::S };
    baddiz "baddiz" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B32, flag: PredFlag::Z };
    baddinz "baddinz" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B32, flag: PredFlag::Nz };
    baddpo "baddpo" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B64, flag: PredFlag::O };
    baddps "baddps" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B64, flag: PredFlag::S };
    baddpz "baddpz" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B64, flag: PredFlag::Z };
    baddpnz "baddpnz" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B64, flag: PredFlag::Nz };
    baddqo "baddqo" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B64, flag: PredFlag::O };
    baddqs "baddqs" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B64, flag: PredFlag::S };
    baddqz "baddqz" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B64, flag: PredFlag::Z };
    baddqnz "baddqnz" => Mnemonic::OpBranch { op: FlagAlu::Add, w: Width::B64, flag: PredFlag::Nz };
    bsubio "bsubio" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B32, flag: PredFlag::O };
    bsubis "bsubis" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B32, flag: PredFlag::S };
    bsubiz "bsubiz" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B32, flag: PredFlag::Z };
    bsubinz "bsubinz" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B32, flag: PredFlag::Nz };
    bmulio "bmulio" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B32, flag: PredFlag::O };
    bmulis "bmulis" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B32, flag: PredFlag::S };
    bmuliz "bmuliz" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B32, flag: PredFlag::Z };
    bmulinz "bmulinz" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B32, flag: PredFlag::Nz };
    borio "borio" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B32, flag: PredFlag::O };
    boris "boris" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B32, flag: PredFlag::S };
    boriz "boriz" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B32, flag: PredFlag::Z };
    borinz "borinz" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B32, flag: PredFlag::Nz };
    bsubqo "bsubqo" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B64, flag: PredFlag::O };
    bsubqs "bsubqs" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B64, flag: PredFlag::S };
    bsubqz "bsubqz" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B64, flag: PredFlag::Z };
    bsubqnz "bsubqnz" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B64, flag: PredFlag::Nz };
    bsubpo "bsubpo" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B64, flag: PredFlag::O };
    bsubps "bsubps" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B64, flag: PredFlag::S };
    bsubpz "bsubpz" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B64, flag: PredFlag::Z };
    bsubpnz "bsubpnz" => Mnemonic::OpBranch { op: FlagAlu::Sub, w: Width::B64, flag: PredFlag::Nz };
    bmulqo "bmulqo" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B64, flag: PredFlag::O };
    bmulqs "bmulqs" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B64, flag: PredFlag::S };
    bmulqz "bmulqz" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B64, flag: PredFlag::Z };
    bmulqnz "bmulqnz" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B64, flag: PredFlag::Nz };
    bmulpo "bmulpo" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B64, flag: PredFlag::O };
    bmulps "bmulps" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B64, flag: PredFlag::S };
    bmulpz "bmulpz" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B64, flag: PredFlag::Z };
    bmulpnz "bmulpnz" => Mnemonic::OpBranch { op: FlagAlu::Mul, w: Width::B64, flag: PredFlag::Nz };
    borqo "borqo" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B64, flag: PredFlag::O };
    borqs "borqs" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B64, flag: PredFlag::S };
    borqz "borqz" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B64, flag: PredFlag::Z };
    borqnz "borqnz" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B64, flag: PredFlag::Nz };
    borpo "borpo" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B64, flag: PredFlag::O };
    borps "borps" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B64, flag: PredFlag::S };
    borpz "borpz" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B64, flag: PredFlag::Z };
    borpnz "borpnz" => Mnemonic::OpBranch { op: FlagAlu::Or, w: Width::B64, flag: PredFlag::Nz };
    bdeq "bdeq" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::Eq };
    bdneq "bdneq" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::Ne };
    bdgt "bdgt" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::Gt };
    bdgteq "bdgteq" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::Ge };
    bdlt "bdlt" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::Lt };
    bdlteq "bdlteq" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::Le };
    bdequn "bdequn" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::EqUn };
    bdnequn "bdnequn" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::NeUn };
    bdgtun "bdgtun" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::GtUn };
    bdgtequn "bdgtequn" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::GeUn };
    bdltun "bdltun" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::LtUn };
    bdltequn "bdltequn" => Mnemonic::BranchF { k: FKind::F64, cc: FCc::LeUn };
    bfeq "bfeq" => Mnemonic::BranchF { k: FKind::F32, cc: FCc::Eq };
    bfgt "bfgt" => Mnemonic::BranchF { k: FKind::F32, cc: FCc::Gt };
    bfgteq "bfgteq" => Mnemonic::BranchF { k: FKind::F32, cc: FCc::Ge };
    bflt "bflt" => Mnemonic::BranchF { k: FKind::F32, cc: FCc::Lt };
    bfgtun "bfgtun" => Mnemonic::BranchF { k: FKind::F32, cc: FCc::GtUn };
    bfgtequn "bfgtequn" => Mnemonic::BranchF { k: FKind::F32, cc: FCc::GeUn };
    bfltun "bfltun" => Mnemonic::BranchF { k: FKind::F32, cc: FCc::LtUn };
    bfltequn "bfltequn" => Mnemonic::BranchF { k: FKind::F32, cc: FCc::LeUn };
    jmp "jmp" => Mnemonic::Jmp;
    call "call" => Mnemonic::Call;
    ret "ret" => Mnemonic::Ret;
    r#break "break" => Mnemonic::Break;
    nop "nop" => Mnemonic::Nop;
    bo "bo" => Mnemonic::FlagBranch(PredFlag::O);
    bs "bs" => Mnemonic::FlagBranch(PredFlag::S);
    bz "bz" => Mnemonic::FlagBranch(PredFlag::Z);
    bnz "bnz" => Mnemonic::FlagBranch(PredFlag::Nz);
    cieq "cieq" => Mnemonic::IntSet { w: Width::B32, cc: IntCc::Eq };
    cineq "cineq" => Mnemonic::IntSet { w: Width::B32, cc: IntCc::Ne };
    cia "cia" => Mnemonic::IntSet { w: Width::B32, cc: IntCc::Hi };
    ciaeq "ciaeq" => Mnemonic::IntSet { w: Width::B32, cc: IntCc::Hs };
    cib "cib" => Mnemonic::IntSet { w: Width::B32, cc: IntCc::Lo };
    cibeq "cibeq" => Mnemonic::IntSet { w: Width::B32, cc: IntCc::Ls };
    cigt "cigt" => Mnemonic::IntSet { w: Width::B32, cc: IntCc::Gt };
    cigteq "cigteq" => Mnemonic::IntSet { w: Width::B32, cc: IntCc::Ge };
    cilt "cilt" => Mnemonic::IntSet { w: Width::B32, cc: IntCc::Lt };
    cilteq "cilteq" => Mnemonic::IntSet { w: Width::B32, cc: IntCc::Le };
    cbeq "cbeq" => Mnemonic::IntSet { w: Width::B8, cc: IntCc::Eq };
    cbneq "cbneq" => Mnemonic::IntSet { w: Width::B8, cc: IntCc::Ne };
    cba "cba" => Mnemonic::IntSet { w: Width::B8, cc: IntCc::Hi };
    cbaeq "cbaeq" => Mnemonic::IntSet { w: Width::B8, cc: IntCc::Hs };
    cbb "cbb" => Mnemonic::IntSet { w: Width::B8, cc: IntCc::Lo };
    cbbeq "cbbeq" => Mnemonic::IntSet { w: Width::B8, cc: IntCc::Ls };
    cbgt "cbgt" => Mnemonic::IntSet { w: Width::B8, cc: IntCc::Gt };
    cbgteq "cbgteq" => Mnemonic::IntSet { w: Width::B8, cc: IntCc::Ge };
    cblt "cblt" => Mnemonic::IntSet { w: Width::B8, cc: IntCc::Lt };
    cblteq "cblteq" => Mnemonic::IntSet { w: Width::B8, cc: IntCc::Le };
    cpeq "cpeq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Eq };
    cpneq "cpneq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Ne };
    cpa "cpa" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Hi };
    cpaeq "cpaeq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Hs };
    cpb "cpb" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Lo };
    cpbeq "cpbeq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Ls };
    cpgt "cpgt" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Gt };
    cpgteq "cpgteq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Ge };
    cplt "cplt" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Lt };
    cplteq "cplteq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Le };
    cqeq "cqeq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Eq };
    cqneq "cqneq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Ne };
    cqa "cqa" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Hi };
    cqaeq "cqaeq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Hs };
    cqb "cqb" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Lo };
    cqbeq "cqbeq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Ls };
    cqgt "cqgt" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Gt };
    cqgteq "cqgteq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Ge };
    cqlt "cqlt" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Lt };
    cqlteq "cqlteq" => Mnemonic::IntSet { w: Width::B64, cc: IntCc::Le };
    tis "tis" => Mnemonic::TestSet { w: Width::B32, test: TestKind::Sign };
    tiz "tiz" => Mnemonic::TestSet { w: Width::B32, test: TestKind::Zero };
    tinz "tinz" => Mnemonic::TestSet { w: Width::B32, test: TestKind::NonZero };
    tps "tps" => Mnemonic::TestSet { w: Width::B64, test: TestKind::Sign };
    tpz "tpz" => Mnemonic::TestSet { w: Width::B64, test: TestKind::Zero };
    tpnz "tpnz" => Mnemonic::TestSet { w: Width::B64, test: TestKind::NonZero };
    tqs "tqs" => Mnemonic::TestSet { w: Width::B64, test: TestKind::Sign };
    tqz "tqz" => Mnemonic::TestSet { w: Width::B64, test: TestKind::Zero };
    tqnz "tqnz" => Mnemonic::TestSet { w: Width::B64, test: TestKind::NonZero };
    tbs "tbs" => Mnemonic::TestSet { w: Width::B8, test: TestKind::Sign };
    tbz "tbz" => Mnemonic::TestSet { w: Width::B8, test: TestKind::Zero };
    tbnz "tbnz" => Mnemonic::TestSet { w: Width::B8, test: TestKind::NonZero };
    cfeq "cfeq" => Mnemonic::FSet { k: FKind::F32, cc: FCc::Eq };
    cfneq "cfneq" => Mnemonic::FSet { k: FKind::F32, cc: FCc::Ne };
    cfnequn "cfnequn" => Mnemonic::FSet { k: FKind::F32, cc: FCc::NeUn };
    cfgt "cfgt" => Mnemonic::FSet { k: FKind::F32, cc: FCc::Gt };
    cfgteq "cfgteq" => Mnemonic::FSet { k: FKind::F32, cc: FCc::Ge };
    cflt "cflt" => Mnemonic::FSet { k: FKind::F32, cc: FCc::Lt };
    cflteq "cflteq" => Mnemonic::FSet { k: FKind::F32, cc: FCc::Le };
    cdeq "cdeq" => Mnemonic::FSet { k: FKind::F64, cc: FCc::Eq };
    cdneq "cdneq" => Mnemonic::FSet { k: FKind::F64, cc: FCc::Ne };
    cdnequn "cdnequn" => Mnemonic::FSet { k: FKind::F64, cc: FCc::NeUn };
    cdgt "cdgt" => Mnemonic::FSet { k: FKind::F64, cc: FCc::Gt };
    cdgteq "cdgteq" => Mnemonic::FSet { k: FKind::F64, cc: FCc::Ge };
    cdlt "cdlt" => Mnemonic::FSet { k: FKind::F64, cc: FCc::Lt };
    cdlteq "cdlteq" => Mnemonic::FSet { k: FKind::F64, cc: FCc::Le };
    popcnti "popcnti" => Mnemonic::Popcnt(Width::B32);
    popcntq "popcntq" => Mnemonic::Popcnt(Width::B64);
    tzcnti "tzcnti" => Mnemonic::BitCount { w: Width::B32, trailing: true };
    tzcntq "tzcntq" => Mnemonic::BitCount { w: Width::B64, trailing: true };
    lzcnti "lzcnti" => Mnemonic::BitCount { w: Width::B32, trailing: false };
    lzcntq "lzcntq" => Mnemonic::BitCount { w: Width::B64, trailing: false };
    memfence "memfence" => Mnemonic::Fence { full: true };
    fence "fence" => Mnemonic::Fence { full: false };
    pause "pause" => Mnemonic::Pause;
    tls_loadb "tls_loadb" => Mnemonic::TlsLoad(Width::B8);
    tls_loadh "tls_loadh" => Mnemonic::TlsLoad(Width::B16);
    tls_loadi "tls_loadi" => Mnemonic::TlsLoad(Width::B32);
    tls_loadp "tls_loadp" => Mnemonic::TlsLoad(Width::B64);
    tls_loadq "tls_loadq" => Mnemonic::TlsLoad(Width::B64);
    tls_storeb "tls_storeb" => Mnemonic::TlsStore(Width::B8);
    tls_storeh "tls_storeh" => Mnemonic::TlsStore(Width::B16);
    tls_storei "tls_storei" => Mnemonic::TlsStore(Width::B32);
    tls_storep "tls_storep" => Mnemonic::TlsStore(Width::B64);
    tls_storeq "tls_storeq" => Mnemonic::TlsStore(Width::B64);
    tls_leap "tls_leap" => Mnemonic::TlsLea;
    atomicxchgaddb "atomicxchgaddb" => Mnemonic::AtomicRmw { op: AtomicOp::Add, w: Width::B8 };
    atomicxchgaddh "atomicxchgaddh" => Mnemonic::AtomicRmw { op: AtomicOp::Add, w: Width::B16 };
    atomicxchgaddi "atomicxchgaddi" => Mnemonic::AtomicRmw { op: AtomicOp::Add, w: Width::B32 };
    atomicxchgaddq "atomicxchgaddq" => Mnemonic::AtomicRmw { op: AtomicOp::Add, w: Width::B64 };
    atomicxchgsubb "atomicxchgsubb" => Mnemonic::AtomicRmw { op: AtomicOp::Sub, w: Width::B8 };
    atomicxchgsubh "atomicxchgsubh" => Mnemonic::AtomicRmw { op: AtomicOp::Sub, w: Width::B16 };
    atomicxchgsubi "atomicxchgsubi" => Mnemonic::AtomicRmw { op: AtomicOp::Sub, w: Width::B32 };
    atomicxchgsubq "atomicxchgsubq" => Mnemonic::AtomicRmw { op: AtomicOp::Sub, w: Width::B64 };
    atomicxchgb "atomicxchgb" => Mnemonic::AtomicRmw { op: AtomicOp::Xchg, w: Width::B8 };
    atomicxchgh "atomicxchgh" => Mnemonic::AtomicRmw { op: AtomicOp::Xchg, w: Width::B16 };
    atomicxchgi "atomicxchgi" => Mnemonic::AtomicRmw { op: AtomicOp::Xchg, w: Width::B32 };
    atomicxchgq "atomicxchgq" => Mnemonic::AtomicRmw { op: AtomicOp::Xchg, w: Width::B64 };
    atomicxchgclearb "atomicxchgclearb" => Mnemonic::AtomicRmwNot(Width::B8);
    atomicxchgclearh "atomicxchgclearh" => Mnemonic::AtomicRmwNot(Width::B16);
    atomicxchgcleari "atomicxchgcleari" => Mnemonic::AtomicRmwNot(Width::B32);
    atomicxchgclearq "atomicxchgclearq" => Mnemonic::AtomicRmwNot(Width::B64);
    atomicxchgorb "atomicxchgorb" => Mnemonic::AtomicRmw { op: AtomicOp::Or, w: Width::B8 };
    atomicxchgorh "atomicxchgorh" => Mnemonic::AtomicRmw { op: AtomicOp::Or, w: Width::B16 };
    atomicxchgori "atomicxchgori" => Mnemonic::AtomicRmw { op: AtomicOp::Or, w: Width::B32 };
    atomicxchgorq "atomicxchgorq" => Mnemonic::AtomicRmw { op: AtomicOp::Or, w: Width::B64 };
    atomicxchgxorb "atomicxchgxorb" => Mnemonic::AtomicRmw { op: AtomicOp::Xor, w: Width::B8 };
    atomicxchgxorh "atomicxchgxorh" => Mnemonic::AtomicRmw { op: AtomicOp::Xor, w: Width::B16 };
    atomicxchgxori "atomicxchgxori" => Mnemonic::AtomicRmw { op: AtomicOp::Xor, w: Width::B32 };
    atomicxchgxorq "atomicxchgxorq" => Mnemonic::AtomicRmw { op: AtomicOp::Xor, w: Width::B64 };
    batomicweakcasb "batomicweakcasb" => Mnemonic::AtomicCas { w: Width::B8, branch: true };
    batomicweakcash "batomicweakcash" => Mnemonic::AtomicCas { w: Width::B16, branch: true };
    batomicweakcasi "batomicweakcasi" => Mnemonic::AtomicCas { w: Width::B32, branch: true };
    batomicweakcasq "batomicweakcasq" => Mnemonic::AtomicCas { w: Width::B64, branch: true };
    atomicweakcasb "atomicweakcasb" => Mnemonic::AtomicCas { w: Width::B8, branch: false };
    atomicweakcash "atomicweakcash" => Mnemonic::AtomicCas { w: Width::B16, branch: false };
    atomicweakcasi "atomicweakcasi" => Mnemonic::AtomicCas { w: Width::B32, branch: false };
    atomicweakcasq "atomicweakcasq" => Mnemonic::AtomicCas { w: Width::B64, branch: false };
    loadlinkacqb "loadlinkacqb" => Mnemonic::LoadLinked(Width::B8);
    loadlinkacqh "loadlinkacqh" => Mnemonic::LoadLinked(Width::B16);
    loadlinkacqi "loadlinkacqi" => Mnemonic::LoadLinked(Width::B32);
    loadlinkacqq "loadlinkacqq" => Mnemonic::LoadLinked(Width::B64);
    storecondrelb "storecondrelb" => Mnemonic::StoreCond(Width::B8);
    storecondrelh "storecondrelh" => Mnemonic::StoreCond(Width::B16);
    storecondreli "storecondreli" => Mnemonic::StoreCond(Width::B32);
    storecondrelq "storecondrelq" => Mnemonic::StoreCond(Width::B64);
    tagCodePtr "tagCodePtr" => Mnemonic::TagCodePtr;
    tagReturnAddress "tagReturnAddress" => Mnemonic::TagReturnAddress;
    untagReturnAddress "untagReturnAddress" => Mnemonic::UntagReturnAddress;
    removeCodePtrTag "removeCodePtrTag" => Mnemonic::RemoveCodePtrTag;
    untagArrayPtr "untagArrayPtr" => Mnemonic::UntagArrayPtr;
    removeArrayPtrTag "removeArrayPtrTag" => Mnemonic::RemoveArrayPtrTag;
}
