#![allow(non_camel_case_types)]

/// - `emit <op>...`
/// 
/// Emits raw operands as bytes to the assembly.
pub struct emit;

/// - `addi <lhs> <rhs> <dst>`
/// - `addi <lhs> <dst>`
/// 
/// 32-bit integer addition.
pub struct addi;

/// - `andi <lhs> <rhs> <dst>`
/// - `andi <lhs> <dst>`
/// 
/// 32-bit integer bitwise AND.
pub struct andi;

/// - `andf <lhs> <rhs> <dst>`
/// - `andf <lhs> <dst>`
/// 
/// 32-bit floating point AND.
pub struct andf;

/// - `andd <lhs> <rhs> <dst>`
/// - `andd <lhs> <dst>`
/// 
/// 64-bit floating point AND.
pub struct andd;

/// - `lshifti <lhs> <rhs> <dst>`
/// - `lshifti <lhs> <dst>`
/// 
/// 32-bit integer left shift.
pub struct lshifti;

/// - `lshiftp <lhs> <rhs> <dst>`
/// - `lshiftp <lhs> <dst>`
/// 
/// Pointer left shift.
pub struct lshiftp;

/// - `lshiftq <lhs> <rhs> <dst>`
/// - `lshiftq <lhs> <dst>`
/// 
/// 64-bit integer left shift.
pub struct lshiftq;

/// - `muli <lhs> <rhs> <dst>`
/// - `muli <lhs> <dst>`
/// 
/// 32-bit integer multiplication.
pub struct muli;

/// - `negi <lhs> <dst>`
/// 
/// 32-bit integer negation.
pub struct negi;

/// - `negp <lhs> <dst>`
/// 
/// Pointer negation.
pub struct negp;

/// - `negq <lhs> <dst>`
/// 
/// 64-bit integer negation.
pub struct negq;

/// - `noti <lhs> <dst>`
/// 
/// 32-bit integer NOT.
pub struct noti;

/// - `ori <lhs> <rhs> <dst>`
/// - `ori <lhs> <dst>`
/// 
/// 32-bit integer OR.
pub struct ori;

/// - `urshifti <lhs> <rhs> <dst>`
/// - `urshifti <lhs> <dst>`
/// 
/// 32-bit integer unsigned right shift.
pub struct urshifti;

/// - `rshiftp <lhs> <rhs> <dst>`
/// - `rshiftp <lhs> <dst>`
/// 
/// Pointer right shift.
pub struct rshiftp;

/// - `urshiftp <lhs> <rhs> <dst>`
/// - `urshiftp <lhs> <dst>`
/// 
/// Pointer unsigned right shift.
pub struct urshiftp;

/// - `rshiftq <lhs> <rhs> <dst>`
/// - `rshiftq <lhs> <dst>`
/// 
/// 64-bit integer right shift.
pub struct rshiftq;

/// - `rrotateq <lhs> <rhs> <dst>`
/// - `rrotateq <lhs> <dst>`
/// 
/// 64-bit integer right rotate.
pub struct rrotateq;

/// - `subi <lhs> <rhs> <dst>`
/// - `subi <lhs> <dst>`
/// 
/// 32-bit integer subtraction.
pub struct subi;

/// - `xori <lhs> <rhs> <dst>`
/// - `xori <lhs> <dst>`
/// 
/// 32-bit integer XOR.
pub struct xori;

/// - `load2i <src> <dst0> <dst1>`
/// 
/// Loads dual 32-bit integers from the source operand.
pub struct load2ia;

/// - `loadi <src> <dst>`
/// 
/// Loads a 32-bit integer from the source operand.
pub struct loadi;

/// - `loadis <src> <dst>`
/// 
/// Loads a 32-bit integer from the source operand with sign extension to 64-bit.
pub struct loadis;

/// - `loadb <src> <dst>`
/// 
/// Loads a 8-bit integer from the source operand.
pub struct loadb;

/// - `loadbsi <src> <dst>`
/// 
/// Loads a 8-bit integer from the source operand with sign extension to 32-bit.
pub struct loadbsi;

/// - `loadbsq <src> <dst>`
/// 
/// Loads a 8-bit integer from the source operand with sign extension to 64-bit.
pub struct loadbsq;

/// - `loadh <src> <dst>`
/// 
/// Loads a 16-bit integer from the source operand.
pub struct loadh;

/// - `loadhsi <src> <dst>`
/// 
/// Loads a 16-bit integer from the source operand with sign extension to 32-bit.
pub struct loadhsi;

/// - `loadhsq <src> <dst>`
/// 
/// Loads a 16-bit integer from the source operand with sign extension to 64-bit.
pub struct loadhsq;

/// - `store2ia <src0> <src1> <dst>`
/// 
/// Stores dual 32-bit integers to the destination operand.
pub struct store2ia;

/// - `storei <src> <dst>`
/// 
/// Stores a 32-bit integer to the destination operand.
pub struct storei;

/// - `storeh <src> <dst>`
/// 
/// Stores a 16-bit integer to the destination operand.
pub struct storeh;

/// - `storeb <src> <dst>`
/// 
/// Stores a 8-bit integer to the destination operand.
pub struct storeb;

/// - `loadf <src> <dst>`
/// 
/// Loads a 32-bit floating point number from the source operand.
pub struct loadf;

/// - `loadd <src> <dst>`
/// 
/// Loads a 64-bit floating point number from the source operand.
pub struct loadd;

/// - `loadv <src> <dst>`
/// 
/// Loads a 128-bit vector from the source operand.
pub struct loadv;

/// - `moved <src> <dst>`
/// 
/// Moves a 64-bit floating point number from the source operand to the destination operand.
pub struct moved;

/// - `storef <src> <dst>`
/// 
/// Stores a 32-bit floating point number to the destination operand.
pub struct storef;

/// - `stored <src> <dst>`
/// 
/// Stores a 64-bit floating point number to the destination operand.
pub struct stored;

/// - `storev <src> <dst>`
/// 
/// Stores a 128-bit vector to the destination operand.
pub struct storev;

/// - `addf <lhs> <rhs> <dst>`
/// - `addf <lhs> <dst>`
/// 
/// 32-bit floating point addition.
pub struct addf;

/// - `addd <lhs> <rhs> <dst>`
/// - `addd <lhs> <dst>`
/// 
/// 64-bit floating point addition.
pub struct addd;

/// - `divf <lhs> <rhs> <dst>`
/// - `divf <lhs> <dst>`
/// 
/// 32-bit floating point division.
pub struct divf;

/// - `divd <lhs> <rhs> <dst>`
/// - `divd <lhs> <dst>`
/// 
/// 64-bit floating point division.
pub struct divd;

/// - `subf <lhs> <rhs> <dst>`
/// - `subf <lhs> <dst>`
/// 
/// 32-bit floating point subtraction.
pub struct subf;

/// - `subd <lhs> <rhs> <dst>`
/// - `subd <lhs> <dst>`
/// 
/// 64-bit floating point subtraction.
pub struct subd;

/// - `mulf <lhs> <rhs> <dst>`
/// - `mulf <lhs> <dst>`
/// 
/// 32-bit floating point multiplication.
pub struct mulf;

/// - `muld <lhs> <rhs> <dst>`
/// - `muld <lhs> <dst>`
/// 
/// 64-bit floating point multiplication.
pub struct muld;

/// - `sqrtf <src> <dst>`
/// 
/// 32-bit floating point square root.
pub struct sqrtf;

/// - `sqrtd <src> <dst>`
/// 
/// 64-bit floating point square root.
pub struct sqrtd;

/// - `floorf <src> <dst>`
/// 
/// 32-bit floating point floor.
pub struct floorf;

/// - `floord <src> <dst>`
/// 
/// 64-bit floating point floor.
pub struct floord;

/// - `roundf <src> <dst>`
/// 
/// 32-bit floating point round.
pub struct roundf;

/// - `roundd <src> <dst>`
/// 
/// 64-bit floating point round.
pub struct roundd;

/// - `truncatef <src> <dst>`
/// 
/// 32-bit floating point truncate.
pub struct truncatef;

/// - `truncated <src> <dst>`
/// 
/// 64-bit floating point truncate.
pub struct truncated;

/// - `truncatef2i <src> <dst>`
/// 
/// 32-bit floating point truncate to 32-bit integer.
pub struct truncatef2i;

/// - `truncatef2q <src> <dst>`
/// 
/// 32-bit floating point truncate to 64-bit integer.
pub struct truncatef2q;

/// - `truncated2q <src> <dst>`
/// 
/// 64-bit floating point truncate to 64-bit integer.
pub struct truncated2q;

/// - `truncated2i <src> <dst>`
/// 
/// 64-bit floating point truncate to 32-bit integer.
pub struct truncated2i;

/// - `truncatef2is <src> <dst>`
/// 
/// 32-bit floating point truncate to 32-bit integer with sign extension.
pub struct truncatef2is;

/// - `truncated2is <src> <dst>`
/// 
/// 64-bit floating point truncate to 32-bit integer with sign extension.
pub struct truncated2is;

/// - `truncatef2qs <src> <dst>`
/// 
/// 32-bit floating point truncate to 64-bit integer with sign extension.
pub struct truncatef2qs;

/// - `truncated2qs <src> <dst>`
/// 
/// 64-bit floating point truncate to 64-bit integer with sign extension.
pub struct truncated2qs;

/// - `ci2d <src> <dst>`
/// 
/// 32-bit integer truncate to 64-bit floating point.
pub struct ci2d;

/// - `ci2ds <src> <dst>`
/// 
/// 32-bit integer truncate to 64-bit floating point with sign extension.
pub struct ci2ds;

/// - `ci2f <src> <dst>`
/// 
/// 32-bit integer truncate to 32-bit floating point.
pub struct ci2f;

/// - `ci2fs <src> <dst>`
/// 
/// 32-bit integer truncate to 32-bit floating point with sign extension.
pub struct ci2fs;

/// - `cq2f <src> <dst>`
/// 
/// 64-bit integer truncate to 32-bit floating point.
pub struct cq2f;

/// - `cq2fs <src> <dst>`
/// 
/// 64-bit integer truncate to 32-bit floating point with sign extension.
pub struct cq2fs;

/// - `cq2d <src> <dst>`
/// 
/// 64-bit integer truncate to 64-bit floating point.
pub struct cq2d;

/// - `cq2ds <src> <dst>`
/// 
/// 64-bit integer truncate to 64-bit floating point with sign extension.
pub struct cq2ds;

/// - `cd2f <src> <dst>`
/// 
/// 64-bit floating point truncate to 32-bit floating point.
pub struct cd2f;

/// - `cf2d <src> <dst>`
/// 
/// 32-bit floating point truncate to 64-bit floating point.
pub struct cf2d;

/// - `fii2d <src> <dst>`
/// 
/// 32-bit floating point truncate to 64-bit integer.
pub struct fii2d;

/// - `fd2ii <src> <dst>`
/// 
/// 64-bit floating point truncate to 32-bit integer.
pub struct fd2ii;

/// - `fq2d <src> <dst>`
/// 
/// 64-bit floating point truncate to 64-bit floating point.
pub struct fq2d;

/// - `fd2q <src> <dst>`
/// 
/// 64-bit floating point truncate to 64-bit integer.
pub struct fd2q;

/// - `bdeq <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point numbers are equal.
pub struct bdeq;

/// - `bdneq <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point numbers are not equal.
pub struct bdneq;

/// - `bdgt <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point number is greater than the other.
pub struct bdgt;

/// - `bdgteq <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point number is greater than or equal to the other.
pub struct bdgteq;

/// - `bdlt <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point number is less than the other.
pub struct bdlt;

/// - `bdlteq <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point number is less than or equal to the other.
pub struct bdlteq;

/// - `bdequn <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point numbers are equal unordered.
pub struct bdequn;

/// - `bdnequn <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point numbers are not equal unordered.
pub struct bdnequn;

/// - `bdgtun <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point number is greater than the other unordered.
pub struct bdgtun;

/// - `bdgtequn <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point number is greater than or equal to the other unordered.
pub struct bdgtequn;

/// - `bdltun <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point number is less than the other unordered.
pub struct bdltun;

/// - `bdltequn <lhs> <rhs> <dst>`
/// 
/// Branch if double-precision floating point number is less than or equal to the other unordered.
pub struct bdltequn;

/// - `bfeq <lhs> <rhs> <dst>`
/// 
/// Branch if single-precision floating point numbers are equal.
pub struct bfeq;

/// - `bfgt <lhs> <rhs> <dst>`
/// 
/// Branch if single-precision floating point number is greater than the other.
pub struct bfgt;

/// - `bflt <lhs> <rhs> <dst>`
/// 
/// Branch if single-precision floating point number is less than the other.
pub struct bflt;

/// - `bfgtun <lhs> <rhs> <dst>`
/// 
/// Branch if single-precision floating point number is greater than the other unordered.
pub struct bfgtun;

/// - `bfgtequn <lhs> <rhs> <dst>`
/// 
/// Branch if single-precision floating point number is greater than or equal to the other unordered.
pub struct bfgtequn;

/// - `bfltun <lhs> <rhs> <dst>`
/// 
/// Branch if single-precision floating point number is less than the other unordered.
pub struct bfltun;

/// - `bfltequn <lhs> <rhs> <dst>`
/// 
/// Branch if single-precision floating point number is less than or equal to the other unordered.
pub struct bfltequn;
///
pub struct btd2i;
///  
pub struct td2i;
/// 
pub struct bcd2i;
/// - `movdz <dst>`
/// 
/// Zero the destination operand which is 64-bit floating point.
pub struct movdz;
/// - `pop <dst>...`
/// 
/// Pop values from SP into the destination operands.
pub struct pop;
/// - `popv <dst>...`
/// 
/// Pop values from SP into the destination operands which are vectors.
pub struct popv;
/// - `push <src>...`
/// 
/// Push values from the source operands onto the stack.
pub struct push;
/// - `pushv <src>...`
/// 
/// Push values from the source operands onto the stack which are vectors.
pub struct pushv;
/// - `mov <src> <dst>`
/// 
/// Move the source operand to the destination operand.
pub struct mov;
/// - `sxi2q <src> <dst>`
/// 
/// Sign extend 32-bit integer to 64-bit integer.
pub struct sxi2q;
/// - `zxi2q <src> <dst>`
/// 
/// Zero extend 32-bit integer to 64-bit integer.
pub struct zxi2q;
/// - `sxb2i <src> <dst>`
/// 
/// Sign extend 8-bit integer to 32-bit integer.
pub struct sxb2i;
/// - `sxh2i <src> <dst>`
/// 
/// Sign extend 16-bit integer to 32-bit integer.
pub struct sxh2i;
/// - `sxb2q <src> <dst>`
/// 
/// Sign extend 8-bit integer to 64-bit integer.
pub struct sxb2q;
/// - `sxh2q <src> <dst>`
/// 
/// Sign extend 16-bit integer to 64-bit integer.
pub struct sxh2q;
/// - `nop`
/// 
/// No operation.
pub struct nop;
/// - `bieq <lhs> <rhs> <dst>`
/// 
/// Branch if 32-bit integers are equal.
pub struct bieq;
/// - `bia <lhs> <rhs> <dst>`
/// 
/// Branch if 32-bit lhs is above rhs.
pub struct bia;
/// - `biaeq <lhs> <rhs> <dst>`
/// 
/// Branch if 32-bit lhs is above or equal to rhs.
pub struct biaeq;
/// - `bib <lhs> <rhs> <dst>`
/// 
/// Branch if 32-bit lhs is below rhs.
pub struct bib;
/// - `bibeq <lhs> <rhs> <dst>`
/// 
/// Branch if 32-bit lhs is below or equal to rhs.
pub struct bibeq;
/// - `bigt <lhs> <rhs> <dst>`
/// 
/// Branch if 32-bit lhs is greater than rhs.
pub struct bigt;
/// - `bigteq <lhs> <rhs> <dst>`
/// 
/// Branch if 32-bit lhs is greater than or equal to rhs.
pub struct bigteq;
/// - `bilt <lhs> <rhs> <dst>`
/// 
/// Branch if 32-bit lhs is less than rhs.
pub struct bilt;
/// - `bilteq <lhs> <rhs> <dst>`
/// 
/// Branch if 32-bit lhs is less than or equal to rhs.
pub struct bilteq;
/// - `bbeq <lhs> <rhs> <dst>`
/// 
/// Branch if 32-bit lhs is equal to rhs.
pub struct bbeq;
/// - `bbneq <lhs> <rhs> <dst>`
/// 
/// Branch if 8-bit lhs is not equal to rhs.
pub struct bbneq;
/// - `bba <lhs> <rhs> <dst>`
/// 
/// Branch if 8-bit lhs is above rhs.
pub struct bba;
/// - `bbaeq <lhs> <rhs> <dst>`
/// 
/// Branch if 8-bit lhs is above or equal to rhs.
pub struct bbaeq;
/// - `bbb <lhs> <rhs> <dst>`
/// 
/// Branch if 8-bit lhs is below rhs.
pub struct bbb;
/// - `bbbeq <lhs> <rhs> <dst>`
/// 
/// Branch if 8-bit lhs is below or equal to rhs.
pub struct bbbeq;
/// - `bbgt <lhs> <rhs> <dst>`
/// 
/// Branch if 8-bit lhs is greater than rhs.
pub struct bbgt;
/// - `bbgteq <lhs> <rhs> <dst>`
/// 
/// Branch if 8-bit lhs is greater than or equal to rhs.
pub struct bbgteq;
/// - `bblt <lhs> <rhs> <dst>`
/// 
/// Branch if 8-bit lhs is less than rhs.
pub struct bblt;
/// - `bblteq <lhs> <rhs> <dst>`
/// 
/// Branch if 8-bit lhs is less than or equal to rhs.
pub struct bblteq;
/// - `btis <src> <dst>`
/// 
/// Test if sign flag is set for 32-bit integer and jump to the destination operand.
pub struct btis;
/// - `btiz <src> <dst>`
/// 
/// Test if zero flag is set for 32-bit integer and jump to the destination operand.
pub struct btiz;
/// - `btinz <src> <dst>`
/// 
/// Test if zero flag is not set for 32-bit integer and jump to the destination operand.
pub struct btinz;
/// - `btbs <src> <dst>`
/// 
/// Test if sign flag is set for 8-bit integer and jump to the destination operand.
pub struct btbs;
/// - `btbz <src> <dst>`
/// 
/// Test if zero flag is set for 8-bit integer and jump to the destination operand.
pub struct btbz;
/// - `btbnz <src> <dst>`
/// 
/// Test if zero flag is not set for 8-bit integer and jump to the destination operand.
pub struct btbnz;
/// - `jmp <dst>`
/// 
/// Jump to the destination operand.
pub struct jmp;
/// - `baddio <lhs> <rhs> <dst>`
/// - `baddio <lhs> <rhs> <dst> <branchDst>`
/// 
/// Add 32-bit integers and jump to the destination operand if overflow flag is set.
pub struct baddio;
/// - `baddis <lhs> <rhs> <dst>`
/// - `baddis <lhs> <rhs> <dst> <branchDst>`
/// 
/// Add 32-bit integers and jump to the destination operand if sign flag is set.
pub struct baddis;
/// - `baddiz <lhs> <rhs> <dst>`
/// - `baddiz <lhs> <rhs> <dst> <branchDst>`
/// 
/// Add 32-bit integers and jump to the destination operand if zero flag is set.
pub struct baddiz;
/// - `baddinz <lhs> <rhs> <dst>`
/// - `baddinz <lhs> <rhs> <dst> <branchDst>`
/// 
/// Add 32-bit integers and jump to the destination operand if zero flag is not set.
pub struct baddinz;
/// - `bsubio <lhs> <rhs> <dst>`
/// - `bsubio <lhs> <rhs> <dst> <branchDst>`
/// 
/// Subtract 32-bit integers and jump to the destination operand if overflow flag is set.
pub struct bsubio;
/// - `bsubis <lhs> <rhs> <dst>`
/// - `bsubis <lhs> <rhs> <dst> <branchDst>`
/// 
/// Subtract 32-bit integers and jump to the destination operand if sign flag is set.
pub struct bsubis;
/// - `bsubiz <lhs> <rhs> <dst>`
/// - `bsubiz <lhs> <rhs> <dst> <branchDst>`
/// 
/// Subtract 32-bit integers and jump to the destination operand if zero flag is set.
pub struct bsubiz;
/// - `bsubinz <lhs> <rhs> <dst>`
/// - `bsubinz <lhs> <rhs> <dst> <branchDst>`
/// 
/// Subtract 32-bit integers and jump to the destination operand if zero flag is not set.
pub struct bsubinz;
/// - `bmulio <lhs> <rhs> <dst>`
/// - `bmulio <lhs> <rhs> <dst> <branchDst>`
/// 
/// Multiply 32-bit integers and jump to the destination operand if overflow flag is set.
pub struct bmulio;
/// - `bmulis <lhs> <rhs> <dst>`
/// - `bmulis <lhs> <rhs> <dst> <branchDst>`
/// 
/// Multiply 32-bit integers and jump to the destination operand if sign flag is set.
pub struct bmulis;
/// - `bmuliz <lhs> <rhs> <dst>`
/// - `bmuliz <lhs> <rhs> <dst> <branchDst>`
/// 
/// Multiply 32-bit integers and jump to the destination operand if zero flag is set.
pub struct bmuliz;
/// - `borio <lhs> <rhs> <dst>`
/// - `borio <lhs> <rhs> <dst> <branchDst>`
/// 
/// Or 32-bit integers and jump to the destination operand if overflow flag is set.
pub struct borio;
/// - `boris <lhs> <rhs> <dst>`
/// - `boris <lhs> <rhs> <dst> <branchDst>`
/// 
/// Or 32-bit integers and jump to the destination operand if sign flag is set.
pub struct boris;
/// - `break`
/// 
/// Debugger breakpoint.
pub struct r#break;
/// - `call <dst>`
/// 
/// Call the destination operand.
pub struct call;
/// - `ret`
/// 
/// Return from a function.
pub struct ret;
/// - `cbeq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 8-bit integers are equal.
pub struct cbeq;
/// - `cbneq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 8-bit integers are not equal.
pub struct cbneq;
/// - `cbaeq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 8-bit integers are above or equal.
pub struct cbaeq;
/// - `cbb <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 8-bit integers are below.
pub struct cbb;
/// - `cbbeq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 8-bit integers are below or equal.
pub struct cbbeq;
/// - `cbgt <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 8-bit integers are greater than.
pub struct cbgt;
/// - `cbgteq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 8-bit integers are greater than or equal.
pub struct cbgteq;
/// - `cblt <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 8-bit integers are less than.
pub struct cblt;
/// - `cblteq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 8-bit integers are less than or equal.
pub struct cblteq;
/// - `cieq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 32-bit integers are equal.
pub struct cieq;
/// - `cineq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 32-bit integers are not equal.
pub struct cineq;
/// - `cia <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 32-bit integers are above.
pub struct cia;
/// - `ciaeq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 32-bit integers are above or equal.
pub struct ciaeq;
/// - `cigt <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 32-bit integers are greater than.
pub struct cigt;
/// - `cigteq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 32-bit integers are greater than or equal.
pub struct cigteq;
/// - `cilt <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 32-bit integers are less than.
pub struct cilt;
/// - `cilteq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 32-bit integers are less than or equal.
pub struct cilteq;
/// - `tis <src> <dst>`
/// 
/// Test if sign flag is set for 32-bit integer and set the destination operand.
pub struct tis;
/// - `tiz <src> <dst>`
/// 
/// Test if zero flag is set for 32-bit integer and set the destination operand.
pub struct tiz;
/// - `tinz <src> <dst>`
/// 
/// Test if zero flag is not set for 32-bit integer and set the destination operand.
pub struct tinz;
/// - `tbs <src> <dst>`
/// 
/// Test if sign flag is set for 8-bit integer and set the destination operand.
pub struct tbs;
/// - `tbz <src> <dst>`
/// 
/// Test if zero flag is set for 8-bit integer and set the destination operand.
pub struct tbz;
/// - `tbnz <src> <dst>`
/// 
/// Test if zero flag is not set for 8-bit integer and set the destination operand. 
pub struct tbnz;
/// - `tps <src> <dst>`
/// 
/// Test if sign flag is set for pointer and set the destination operand.
pub struct tps;
/// - `tpz <src> <dst>`
/// 
/// Test if zero flag is set for pointer and set the destination operand.
pub struct tpz;
/// - `tpnz <src> <dst>`
/// 
/// Test if zero flag is not set for pointer and set the destination operand.
pub struct tpnz;
/// - `peek <src> <dst>`
/// 
/// Peek the source operand and set the destination operand.
pub struct peek;
/// - `poke <src> <dst>`
/// 
/// Poke the source operand and set the destination operand.
pub struct poke;
/// - `bpeq <lhs> <rhs> <dst>`
/// 
/// Branch if pointer sized integers are equal.
pub struct bpeq;
/// - `bpneq <lhs> <rhs> <dst>`
/// 
/// Branch if pointer sized integers are not equal.
pub struct bpneq;
/// - `bpa <lhs> <rhs> <dst>`
/// 
/// Branch if pointer sized integers are above.
pub struct bpa; 
/// - `bpaeq <lhs> <rhs> <dst>`
/// 
/// Branch if pointer sized integers are above or equal.
pub struct bpaeq;
/// - `bpb <lhs> <rhs> <dst>`
/// 
/// Branch if pointer sized integers are below.
pub struct bpb;
/// - `bpbeq <lhs> <rhs> <dst>`
/// 
/// Branch if pointer sized integers are below or equal.
pub struct bpbeq;
/// - `bpgt <lhs> <rhs> <dst>`
/// 
/// Branch if pointer sized integers are greater than.
pub struct bpgt;
/// - `bpgt <lhs> <rhs> <dst>`
/// 
/// Branch if pointer sized integers are greater than or equal.
pub struct bpgteq;
/// - `bplt <lhs> <rhs> <dst>`
/// 
/// Branch if pointer sized integers are less than.
pub struct bplt;
/// - `bplteq <lhs> <rhs> <dst>`
/// 
/// Branch if pointer sized integers are less than or equal.
pub struct bplteq;
/// - `addp <lhs> <rhs> <dst>`
/// - `addp <lhs> <dst>`
/// 
/// Add pointer sized integers and set the destination operand.
pub struct addp;
/// - `mulp <lhs> <rhs> <dst>`
/// - `mulp <lhs> <dst>`
/// 
/// Multiply pointer sized integers and set the destination operand.
pub struct mulp;
/// - `andp <lhs> <rhs> <dst>`
/// - `andp <lhs> <dst>`
/// 
/// And pointer sized integers and set the destination operand.
pub struct andp;
/// - `orp <lhs> <rhs> <dst>`
/// - `orp <lhs> <dst>`
/// 
/// Or pointer sized integers and set the destination operand.
pub struct orp;
/// - `subp <lhs> <rhs> <dst>`
/// - `subp <lhs> <dst>`
/// 
/// Subtract pointer sized integers and set the destination operand.
pub struct subp;
/// - `xorp <lhs> <rhs> <dst>`
/// - `xorp <lhs> <dst>`
/// 
/// Xor pointer sized integers and set the destination operand.
pub struct xorp;
/// - `loadp <src> <dst>`
/// 
/// Load pointer sized integer and set the destination operand.
pub struct loadp;
/// - `cpeq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if pointer sized integers are equal.
pub struct cpeq;
/// - `cpneq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if pointer sized integers are not equal.
pub struct cpneq;
/// - `cpa <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if pointer sized integers are above.
pub struct cpa;
/// - `cpaeq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if pointer sized integers are above or equal.
pub struct cpaeq;
/// - `cpb <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if pointer sized integers are below.
pub struct cpb;
/// - `cpbeq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if pointer sized integers are below or equal.
pub struct cpbeq;
/// - `cpgt <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if pointer sized integers are greater than.
pub struct cpgt;
/// - `cpgt <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if pointer sized integers are greater than or equal.
pub struct cpgteq;
/// - `storep <src> <dst>`
/// 
/// Store pointer sized integer and set the destination operand.
pub struct storep;
/// - `btps <src> <branchDst>`
/// - `btps <lhs> <rhs> <branchDst>`
/// 
/// Branch if pointer sized integers sign flag is set.
pub struct btps;
/// - `btpz <src> <branchDst>`
/// - `btpz <lhs> <rhs> <branchDst>`
/// 
/// Branch if pointer sized integers zero flag is set.
pub struct btpz;
/// - `btpnz <lhs> <rhs> <branchDst>`
/// - `btpnz <lhs> <branchDst>` 
/// 
/// Branch if pointer sized integers zero flag is not set.
pub struct btpnz;
/// - `baddpo <lhs> <rhs> <dst> <branchDst>`
/// - `baddpo <lhs> <dst> <branchDst>`
/// 
/// Add pointer sized integers and jump to the destination operand if overflow flag is set.
pub struct baddpo;
/// - `baddps <lhs> <rhs> <dst> <branchDst>`
/// - `baddps <lhs> <dst> <branchDst>`
/// 
/// Add pointer sized integers and jump to the destination operand if sign flag is set.
pub struct baddps;
/// - `baddpz <lhs> <rhs> <dst> <branchDst>`
/// - `baddpz <lhs> <dst> <branchDst>`
/// 
/// Add pointer sized integers and jump to the destination operand if zero flag is set.
pub struct baddpz;
/// - `baddpnz <lhs> <rhs> <dst> <branchDst>`
/// - `baddpnz <lhs> <dst> <branchDst>`
/// 
/// Add pointer sized integers and jump to the destination operand if zero flag is not set.
pub struct baddpnz;
/// - `tqs <src> <dst>`
/// - `tqs <lhs> <rhs> <dst>`
/// 
/// Test if sign flag is set for 64-bit integers and set the destination operand.
pub struct tqs;
/// - `tqz <src> <dst>`
/// - `tqz <lhs> <rhs> <dst>`
/// 
/// Test if zero flag is set for 64-bit integers and set the destination operand.
pub struct tqz;
/// - `tqnz <src> <dst>`
/// - `tqnz <lhs> <rhs> <dst>`
/// 
/// Test if zero flag is not set for 64-bit integers and set the destination operand.
pub struct tqnz;
/// - `bqeq <lhs> <rhs> <dst>`
/// 
/// Branch if 64-bit integers are equal.
pub struct bqeq;
/// - `bqneq <lhs> <rhs> <dst>`
/// 
/// Branch if 64-bit integers are not equal.
pub struct bqneq;
/// - `bqa <lhs> <rhs> <dst>`
/// 
/// Branch if 64-bit integers are above.    
pub struct bqa;
/// - `bqaeq <lhs> <rhs> <dst>`
/// 
/// Branch if 64-bit integers are above or equal.
pub struct bqaeq;
/// - `bqb <lhs> <rhs> <dst>`
/// 
/// Branch if 64-bit integers are below.
pub struct bqb;
/// - `bqbeq <lhs> <rhs> <dst>`
/// 
/// Branch if 64-bit integers are below or equal.
pub struct bqbeq;
/// - `bqgt <lhs> <rhs> <dst>`
/// 
/// Branch if 64-bit integers are greater than.
pub struct bqgt;
/// - `bqgteq <lhs> <rhs> <dst>`
/// 
/// Branch if 64-bit integers are greater than or equal.
pub struct bqgteq;
/// - `bqlt <lhs> <rhs> <dst>`
/// 
/// Branch if 64-bit integers are less than.
pub struct bqlt;
/// - `bqlteq <lhs> <rhs> <dst>`
/// 
/// Branch if 64-bit integers are less than or equal.
pub struct bqlteq;
/// - `addq <lhs> <rhs> <dst>`
/// - `addq <lhs> <dst>`
/// 
/// Add 64-bit integers and set the destination operand.
pub struct addq;
/// - `mulq <lhs> <rhs> <dst>`
/// - `mulq <lhs> <dst>`
/// 
/// Multiply 64-bit integers and set the destination operand.
pub struct mulq;
/// - `andq <lhs> <rhs> <dst>`
/// - `andq <lhs> <dst>`
/// 
/// And 64-bit integers and set the destination operand.
pub struct andq;
/// - `orq <lhs> <rhs> <dst>`   
/// - `orq <lhs> <dst>`
/// 
/// Or 64-bit integers and set the destination operand.
pub struct orq;
/// - `subq <lhs> <rhs> <dst>`
/// - `subq <lhs> <dst>`
/// 
/// Subtract 64-bit integers and set the destination operand.
pub struct subq;
/// - `xorq <lhs> <rhs> <dst>`
/// - `xorq <lhs> <dst>`
/// 
/// Xor 64-bit integers and set the destination operand.
pub struct xorq;
/// - `loadq <src> <dst>`
/// 
/// Load 64-bit integer and set the destination operand.
pub struct loadq;
/// - `cqeq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 64-bit integers are equal.
pub struct cqeq;
/// - `cqa <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 64-bit integers are above.
pub struct cqa;
/// - `cqaeq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 64-bit integers are above or equal.
pub struct cqaeq;
/// - `cqb <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 64-bit integers are below.
pub struct cqb;
/// - `cqbeq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 64-bit integers are below or equal.
pub struct cqbeq;
/// - `cqgt <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 64-bit integers are greater than.
pub struct cqgt;
/// - `cqgteq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 64-bit integers are greater than or equal.
    pub struct cqgteq;
/// - `cqlt <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 64-bit integers are less than.
pub struct cqlt;
/// - `cqlteq <lhs> <rhs> <dst>`
/// 
/// Test and set <dst> if 64-bit integers are less than or equal.
pub struct cqlteq;
/// - `storeq <src> <dst>`
/// 
/// Store 64-bit integer and set the destination operand.
pub struct storeq;
/// - `btqs <src> <branchDst>`
/// - `btqs <lhs> <rhs> <branchDst>`
/// 
/// Branch if 64-bit integers sign flag is set.
pub struct btqs;    
/// - `baddqs <lhs> <rhs> <dst> <branchDst>`
/// - `baddqs <lhs> <dst> <branchDst>`
/// 
/// Add 64-bit integers and jump to the destination operand if overflow flag is set.
pub struct baddqs;
/// - `baddqz <lhs> <rhs> <dst> <branchDst>`
/// - `baddqz <lhs> <dst> <branchDst>`
/// 
/// Add 64-bit integers and jump to the destination operand if zero flag is set.
pub struct baddqz;
/// - `baddqnz <lhs> <rhs> <dst> <branchDst>`
/// - `baddqnz <lhs> <dst> <branchDst>`
/// 
/// Add 64-bit integers and jump to the destination operand if zero flag is not set.
pub struct baddqnz;
/// - `bo <branchDst>`
/// 
/// Branch if overflow flag is set.
pub struct bo;
/// - `bs <branchDst>`
/// 
/// Branch if sign flag is set.
pub struct bs;
/// - `bz <branchDst>`
/// 
/// Branch if zero flag is set.
pub struct bz;
/// - `bnz <branchDst>`
/// 
/// Branch if zero flag is not set.
pub struct bnz;
/// - `leai <src> <dst>`
/// 
/// Load effective 32-bit address.
pub struct leai;
/// - `leap <src> <dst>`
/// 
/// Load effective address.
pub struct leap;
    /// - `memfence`
    /// 
/// Memory fence.
pub struct memfence;
/// - `tagCodePtr`
/// 
/// Tag code pointer.
pub struct tagCodePtr;
/// - `tagReturnAddress`
/// 
/// Tag return address.
pub struct tagReturnAddress;
/// - `untagReturnAddress`
/// 
/// Untag return address.
pub struct untagReturnAddress;
/// - `removeCodePtrTag`
/// 
/// Remove code pointer tag.
pub struct removeCodePtrTag;
/// - `untagArrayPtr`
/// 
/// Untag array pointer.
pub struct untagArrayPtr;

/// 
pub struct tzcnti;
pub struct tzcntq;
pub struct lzcnti;
pub struct lzcntq;
pub struct absf;
pub struct absd;
pub struct negf;
pub struct negd;
pub struct ceilf;
pub struct ceild;
pub struct cfeq;
pub struct cdeq;
pub struct cfneq;
pub struct cfnequn;
pub struct cdneq;
pub struct cdnequn;
pub struct cflt;
pub struct cdlt;
pub struct cflteq;
pub struct cdlteq;
pub struct cfgt;
pub struct cdgt;
pub struct cfgteq;
pub struct cdgteq;
pub struct fi2f;
pub struct ff2i;
pub struct tls_loadp;
pub struct tls_storep;
pub struct cdqi;
pub struct idivi;
pub struct udivi;
pub struct cqoq;
pub struct idivq;
pub struct udivq;
pub struct notq;
pub struct atomicxchgaddb;
pub struct atomicxchgaddh;
pub struct atomicxchgaddi;
pub struct atomicxchgaddq;
pub struct atomicxchgsubb;
pub struct atomicxchgsubh;
pub struct atomicxchgsubi;
pub struct atomicxchgsubq;
pub struct atomicxchgb;
pub struct atomicxchgh;
pub struct atomicxchgi;
pub struct atomicxchgq;
pub struct batomicweakcasb;
pub struct batomicweakcash;
pub struct batomicweakcasi;
pub struct batomicweakcasq;
pub struct atomicweakcasb;
pub struct atomicweakcash;
pub struct atomicweakcasi;
pub struct atomicweakcasq;
pub struct atomicloadb;
pub struct atomicloadh;
pub struct atomicloadi;
pub struct atomicloadq;
pub struct fence;
pub struct adci;
pub struct bcs;
pub struct clrbp;
pub struct mvlbl;
pub struct globaladdr;
pub struct sbci;
pub struct moveii;
pub struct loadlinkb;
pub struct loadlinkh;
pub struct loadlinki;
pub struct loadlink2i;
pub struct storecondb;
pub struct storecondh;
pub struct storecondi;
pub struct storecond2i;
pub struct writefence;
pub struct bfiq;
pub struct pcrtoaddr;
pub struct loadqinc;
pub struct loadlinkacqb;
pub struct loadlinkacqh;
pub struct loadlinkacqi;
pub struct loadlinkacqq;
pub struct storecondrelb;
pub struct storecondrelh;
pub struct storecondreli;
pub struct storecondrelq;

pub struct atomicxchgclearb;
pub struct atomicxchgclearh;
pub struct atomicxchgcleari;
pub struct atomicxchgclearq;
pub struct atomicxchgorb;
pub struct atomicxchgorh;
pub struct atomicxchgori;
pub struct atomicxchgorq;
pub struct atomicxchgxorb;
pub struct atomicxchgxorh;
pub struct atomicxchgxori;
pub struct atomicxchgxorq;

pub struct loadpairq;
pub struct loadpairi;
pub struct storepairq;
pub struct storepairi;
pub struct loadpaird;
pub struct storepaird;
pub struct smulli;
pub struct umulli;
pub struct addis;
pub struct subis;
pub struct oris;
pub struct addps;
pub struct divi;
pub struct divis;
pub struct divq;
pub struct divqs;
pub struct remi;
pub struct remis;
pub struct remq;
pub struct remqs;
pub struct la;
pub struct movz;
pub struct movn;
pub struct setcallreg;
pub struct slt;
pub struct sltu;
pub struct pichdr;
pub struct rloopCrash;
pub struct rloopDo;

pub struct bineq;