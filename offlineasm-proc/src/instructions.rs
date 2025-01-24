use std::{collections::HashSet, sync::LazyLock};

use offlineasm_def::for_each_instruction;
use syn::parse::ParseStream;
/* 
#[rustfmt::skip]
static MACRO_INSTRUCTIONS: &[&str] = &[

"emit",
"addi",
"andi",
"andf",
"andd",
"lshifti",
"lshiftp",
"lshiftq",
"muli",
"negi",
"negp",
"negq",
"noti",
"ori",
"orf",
"ord",
"orh",
"rshifti",
"urshifti",
"rshiftp",
"urshiftp",
"rshiftq",
"urshiftq",
"lrotatei",
"lrotateq",
"rrotatei",
"rrotateq",
"subi",
"xori",
"load2ia",
"loadi",
"loadis",
"loadb",
"loadbsi",
"loadbsq",
"loadh",
"loadhsi",
"loadhsq",
"store2ia",
"storei",
"storeh",
"storeb",
"loadf",
"loadd",
"loadv",
"moved",
"storef",
"stored",
"storev",
"addf",
"addd",
"divf",
"divd",
"subf",
"subd",
"mulf",
"muld",
"sqrtf",
"sqrtd",
"floorf",
"floord",
"roundf",
"roundd",
"truncatef",
"truncated",
"truncatef2i",
"truncatef2q",
"truncated2q",
"truncated2i",
"truncatef2is",
"truncated2is",
"truncatef2qs",
"truncated2qs",
"ci2d",
"ci2ds",
"ci2f",
"ci2fs",
"cq2f",
"cq2fs",
"cq2d",
"cq2ds",
"cd2f",
"cf2d",
"fii2d", // usage: fii2d <gpr with least significant bits>, <gpr with most significant bits>, <fpr>
"fd2ii", // usage: fd2ii <fpr>, <gpr with least significant bits>, <gpr with most significant bits>
"fq2d",
"fd2q",
"bdeq",
"bdneq",
"bdgt",
"bdgteq",
"bdlt",
"bdlteq",
"bdequn",
"bdnequn",
"bdgtun",
"bdgtequn",
"bdltun",
"bdltequn",
"bfeq",
"bfgt",
"bflt",
"bfgtun",
"bfgtequn",
"bfltun",
"bfltequn",
"btd2i",
"td2i",
"bcd2i",
"movdz",
"pop",
"popv",
"push",
"pushv",
"mov",
"sxi2q",
"zxi2q",
"sxb2i",
"sxh2i",
"sxb2q",
"sxh2q",
"nop",
"bieq",
"bineq",
"bia",
"biaeq",
"bib",
"bibeq",
"bigt",
"bigteq",
"bilt",
"bilteq",
"bbeq",
"bbneq",
"bba",
"bbaeq",
"bbb",
"bbbeq",
"bbgt",
"bbgteq",
"bblt",
"bblteq",
"btis",
"btiz",
"btinz",
"btbs",
"btbz",
"btbnz",
"jmp",
"baddio",
"baddis",
"baddiz",
"baddinz",
"bsubio",
"bsubis",
"bsubiz",
"bsubinz",
"bmulio",
"bmulis",
"bmuliz",
"bmulinz",
"borio",
"boris",
"boriz",
"borinz",
"break",
"call",
"ret",
"cbeq",
"cbneq",
"cba",
"cbaeq",
"cbb",
"cbbeq",
"cbgt",
"cbgteq",
"cblt",
"cblteq",
"cieq",
"cineq",
"cia",
"ciaeq",
"cib",
"cibeq",
"cigt",
"cigteq",
"cilt",
"cilteq",
"tis",
"tiz",
"tinz",
"tbs",
"tbz",
"tbnz",
"tps",
"tpz",
"tpnz",
"peek",
"poke",
"bpeq",
"bpneq",
"bpa",
"bpaeq",
"bpb",
"bpbeq",
"bpgt",
"bpgteq",
"bplt",
"bplteq",
"addp",
"mulp",
"andp",
"orp",
"subp",
"xorp",
"loadp",
"cpeq",
"cpneq",
"cpa",
"cpaeq",
"cpb",
"cpbeq",
"cpgt",
"cpgteq",
"cplt",
"cplteq",
"storep",
"btps",
"btpz",
"btpnz",
"baddpo",
"baddps",
"baddpz",
"baddpnz",
"tqs",
"tqz",
"tqnz",
"bqeq",
"bqneq",
"bqa",
"bqaeq",
"bqb",
"bqbeq",
"bqgt",
"bqgteq",
"bqlt",
"bqlteq",
"addq",
"mulq",
"andq",
"orq",
"subq",
"xorq",
"loadq",
"cqeq",
"cqneq",
"cqa",
"cqaeq",
"cqb",
"cqbeq",
"cqgt",
"cqgteq",
"cqlt",
"cqlteq",
"storeq",
"btqs",
"btqz",
"btqnz",
"baddqo",
"baddqs",
"baddqz",
"baddqnz",
"bo",
"bs",
"bz",
"bnz",
"leai",
"leap",
"memfence",
"tagCodePtr",
"tagReturnAddress",
"untagReturnAddress",
"removeCodePtrTag",
"untagArrayPtr",
"removeArrayPtrTag",
"tzcnti",
"tzcntq",
"lzcnti",
"lzcntq",
"absf",
"absd",
"negf",
"negd",
"ceilf",
"ceild",
"cfeq",
"cdeq",
"cfneq",
"cfnequn",
"cdneq",
"cdnequn",
"cflt",
"cdlt",
"cflteq",
"cdlteq",
"cfgt",
"cdgt",
"cfgteq",
"cdgteq",
"fi2f",
"ff2i",
"tls_loadp",
"tls_storep",
];

pub static X86_INSTRUCTIONS: &[&str] = &[
    "cdqi",
     "idivi",
     "udivi",
     "cqoq",
     "idivq",
     "udivq",
     "notq",
     "atomicxchgaddb",
     "atomicxchgaddh",
     "atomicxchgaddi",
     "atomicxchgaddq",
     "atomicxchgsubb",
     "atomicxchgsubh",
     "atomicxchgsubi",
     "atomicxchgsubq",
     "atomicxchgb",
     "atomicxchgh",
     "atomicxchgi",
     "atomicxchgq",
     "batomicweakcasb",
     "batomicweakcash",
     "batomicweakcasi",
     "batomicweakcasq",
     "atomicweakcasb",
     "atomicweakcash",
     "atomicweakcasi",
     "atomicweakcasq",
     "atomicloadb",
     "atomicloadh",
     "atomicloadi",
     "atomicloadq",
     "fence",
];

pub static ARM_INSTRUCTIONS: &[&str] = &[
    "adci",
     "bcs",
     "clrbp",
     "mvlbl",
     "globaladdr",
     "sbci",
     "moveii",
     "loadlinkb",
     "loadlinkh",
     "loadlinki",
     "loadlink2i",
     "storecondb",
     "storecondh",
     "storecondi",
     "storecond2i",
     "writefence",
];  

pub static ARM64_INSTRUCTIONS: &[&str] = &[
    "bfiq", // Bit field insert <source reg> <last bit written> <width immediate> <dest reg>
    "pcrtoaddr",   // Address from PC relative offset - adr instruction
    "globaladdr",
    "notq",
    "loadqinc",
    "loadlinkacqb",
    "loadlinkacqh",
    "loadlinkacqi",
    "loadlinkacqq",
    "storecondrelb",
    "storecondrelh",
    "storecondreli",
    "storecondrelq",
    "fence",
    // They are available only if Atomic LSE is supported.
    "atomicxchgaddb",
    "atomicxchgaddh",
    "atomicxchgaddi",
    "atomicxchgaddq",
    "atomicxchgclearb",
    "atomicxchgclearh",
    "atomicxchgcleari",
    "atomicxchgclearq",
    "atomicxchgorb",
    "atomicxchgorh",
    "atomicxchgori",
    "atomicxchgorq",
    "atomicxchgxorb",
    "atomicxchgxorh",
    "atomicxchgxori",
    "atomicxchgxorq",
    "atomicxchgb",
    "atomicxchgh",
    "atomicxchgi",
    "atomicxchgq",
    "atomicweakcasb",
    "atomicweakcash",
    "atomicweakcasi",
    "atomicweakcasq",
    "atomicloadb",
    "atomicloadh",
    "atomicloadi",
    "atomicloadq",
    "loadpairq",
    "loadpairi",
    "storepairq",
    "storepairi",
    "loadpaird",
    "storepaird",
];

pub static RISC_INSTRUCTIONS: &[&str] = &[
    "smulli",  // Multiply two 32-bit words and produce a 64-bit word
    "umulli",  // Multiply two 32-bit words and produce a 64-bit word
    "addis",   // Add integers and set a flag.
    "subis",   // Same, but for subtraction.
    "oris",    // Same, but for bitwise or.
    "addps",   // addis but for pointers.
    "divi",
    "divis",
    "divq",
    "divqs",
    "remi",
    "remis",
    "remq",
    "remqs"
];

pub static MIPS_INSTRUCTIONS: &[&str] = &[
    "la",
    "movz",
    "movn",
    "setcallreg",
    "slt",
    "sltu",
    "pichdr"
];

pub static RUST_INSTRUCTIONS: &[&str] = &[
    "rloopCrash",
    "rloopDo",
];*/

macro_rules! def_instructions {
    ($(($target:ident => $($instruction:ident)*))*) => {
        $(pub static $target: &[&str] = &[
            $(stringify!($instruction)),*
        ];)*
    };
}

for_each_instruction!(def_instructions);

pub static INSTRUCTIONS: LazyLock<Vec<&str>> = LazyLock::new(|| {
    let mut instructions = Vec::new();
    instructions.extend(MACRO_INSTRUCTIONS);
    instructions.extend(X86_INSTRUCTIONS);
    instructions.extend(ARM_INSTRUCTIONS);
    instructions.extend(ARM64_INSTRUCTIONS);
    instructions.extend(RISC_INSTRUCTIONS);
    instructions.extend(MIPS_INSTRUCTIONS);
    instructions.extend(RUST_INSTRUCTIONS);
    instructions
});

pub static INSTRUCTION_SET: LazyLock<HashSet<&str>> = LazyLock::new(|| {
    INSTRUCTIONS.iter().copied().collect()
});

pub fn is_branch(instruction: &str) -> bool {
    instruction.starts_with("b")
}   

pub fn has_fall_through(instruction: &str) -> bool {
    instruction != "jmp" && instruction != "ret"
}

pub fn is_power_of_two(value: isize) -> bool {
    if value == 0 {
        return false;
    }
    (value & (value - 1)) == 0
}

macro_rules! def_keywords {
    ($(($target:ident => $($keyword:ident)*))*) => {
        pub mod kw {
            $($(
                syn::custom_keyword!($keyword);
            )*)*
        }
    };
}

syn::custom_keyword!(beaeqwqe);

for_each_instruction!(def_keywords);


pub fn peek_instruction(input: &ParseStream) -> bool {
    let mut result = false;
    macro_rules! peek_keyword {
        ($(($target:ident => $($keyword:ident)*))*) => {
            $(
                result |= $(
                    input.peek(kw::$keyword)
                )|*;
            )*
        };
    }
    
    for_each_instruction!(peek_keyword);

    result
}