//! RISC-V 64 helpers both backends share.
//!
//! Loading a constant is the one RISC-V sequence whose shape is not decided
//! by the lowering itself: an assembler expands the `li` pseudo-instruction
//! with its own algorithm, which differs between assemblers and versions.
//! Both backends expand constants with [`li`] instead, so offlineasm prints
//! exactly the instructions onlineasm encodes.

/// One instruction of a constant load into `rd`. The first step reads
/// `zero` (or nothing, for `lui`); every later step reads and writes `rd`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LiStep {
    /// `lui rd, imm20`: the 20-bit field, `0..=0xfffff`.
    Lui(i64),
    /// `addi rd, rs, imm12`.
    Addi(i64),
    /// `addiw rd, rd, imm12`. Only ever follows a `lui`.
    Addiw(i64),
    /// `slli rd, rd, shamt`.
    Slli(u32),
    /// `srli rd, rd, shamt`.
    Srli(u32),
}

fn fits(v: i64, bits: u32) -> bool {
    let shift = 64 - bits;
    (v << shift) >> shift == v
}

fn sext12(v: i64) -> i64 {
    (v << 52) >> 52
}

/// LLVM's `RISCVMatInt::generateInstSeqImpl` for the base RV64 ISA.
fn seq(val: i64, out: &mut Vec<LiStep>) {
    if fits(val, 32) {
        let hi20 = ((val + 0x800) >> 12) & 0xf_ffff;
        let lo12 = sext12(val);
        if hi20 != 0 {
            out.push(LiStep::Lui(hi20));
        }
        if lo12 != 0 || hi20 == 0 {
            out.push(if hi20 != 0 {
                LiStep::Addiw(lo12)
            } else {
                LiStep::Addi(lo12)
            });
        }
        return;
    }
    // Peel the low 12 bits off as a final `addi`, and the trailing zeros
    // of what is left as a `slli`.
    let lo12 = sext12(val);
    let mut val = val.wrapping_sub(lo12);
    let mut shift = 0;
    if !fits(val, 32) {
        shift = val.trailing_zeros();
        val >>= shift;
        // Keep 12 of the zeros when that turns the rest into a `lui`.
        if shift > 12 && !fits(val, 12) && fits(((val as u64) << 12) as i64, 32) {
            shift -= 12;
            val = ((val as u64) << 12) as i64;
        }
    }
    seq(val, out);
    if shift != 0 {
        out.push(LiStep::Slli(shift));
    }
    if lo12 != 0 {
        out.push(LiStep::Addi(lo12));
    }
}

/// The instructions that load `val` into a register, following LLVM's
/// `RISCVMatInt::generateInstSeq` for the base RV64 ISA (no Zba/Zbb/Zbs).
pub fn li(val: i64) -> Vec<LiStep> {
    let mut out = Vec::new();
    seq(val, &mut out);

    // With nonzero low bits but trailing zeros, a shifted constant plus a
    // final `slli` may be shorter.
    if val & 0xfff != 0 && val & 1 == 0 && out.len() >= 2 {
        let zeros = val.trailing_zeros();
        let shifted = val >> zeros;
        let mut alt = Vec::new();
        seq(shifted, &mut alt);
        if alt.len() + 1 < out.len() || fits(shifted, 6) {
            alt.push(LiStep::Slli(zeros));
            out = alt;
        }
    }
    if out.len() <= 2 {
        return out;
    }

    // A positive constant may be shorter built with no leading zeros and a
    // final `srli`: first with the vacated low bits filled with ones, then
    // with zeros.
    if val > 0 {
        let zeros = val.leading_zeros();
        let ones = (1u64 << zeros) - 1;
        let shifted = ((val as u64) << zeros) | ones;
        for candidate in [shifted, shifted & !ones] {
            let mut alt = Vec::new();
            seq(candidate as i64, &mut alt);
            if alt.len() + 1 < out.len() {
                alt.push(LiStep::Srli(zeros));
                out = alt;
            }
        }
    }
    out
}
