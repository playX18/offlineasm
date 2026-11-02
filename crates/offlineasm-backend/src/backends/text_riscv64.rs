use super::text::{self, sym_text};
use super::LowerCtx;
use offlineasm_ir::{
    op_eq, Alu3, AluOp, AtomicOp, BitcastDir, Disp, Extern, FAlu, FArith3, FCc, FKind, FlagAlu,
    FmaOp, Fpr, Gpr, Inst, IntCc, Lbl, LeaSrc, Mem, Op, PairW, PredFlag, Reach, RoundMode, Scratch,
    ShiftCnt, ShiftOp, Sx, Target, TestKind, Width,
};

const SCRATCH: Scratch = offlineasm_ir::regs::RISCV64.scratch;
const G1: Gpr = SCRATCH.gpr;
const G2: Gpr = SCRATCH.gpr2;
/// FP scratch (`f31`).
const SF: Fpr = SCRATCH.fpr;
/// flags register (`x30`).
const FLAGS: Gpr = Gpr(30);
/// thread pointer (`x4` / `tp`).
const TP: Gpr = Gpr(4);
const T0: Gpr = Gpr(10);
const T2: Gpr = Gpr(12);

macro_rules! ins {
    ($ctx:expr, $($arg:tt)*) => {
        $ctx.emitter.puts(&format!($($arg)*))
    };
}

fn gpr(g: Gpr) -> String {
    format!("x{}", g.0)
}

fn fpr(r: Fpr) -> String {
    format!("f{}", r.0)
}

fn fhi(r: Fpr) -> Result<Fpr, String> {
    if r.0 > 30 {
        return Err(format!("riscv64: fpr{} has no pair high half", r.0));
    }
    Ok(Fpr(r.0 + 1))
}

fn fits12(v: i64) -> bool {
    (-2048..2048).contains(&v)
}

fn fits_d12(disp: i32) -> bool {
    (-2048..2048).contains(&disp)
}

fn fresh(ctx: &mut LowerCtx) -> String {
    text::synth_name(ctx, "l", 0)
}

fn bind(ctx: &mut LowerCtx, name: &str) {
    ctx.emitter.puts(&format!("{}:", name));
}

/// Load `v` into `dst` with the shared [`offlineasm_ir::riscv::li`]
/// expansion rather than the assembler's `li`, so onlineasm encodes the
/// same instructions.
fn mov_imm(ctx: &mut LowerCtx, dst: Gpr, v: i64) {
    use offlineasm_ir::riscv::LiStep;
    let d = gpr(dst);
    for (i, step) in offlineasm_ir::riscv::li(v).into_iter().enumerate() {
        let src = if i == 0 { "x0".to_string() } else { d.clone() };
        match step {
            LiStep::Lui(hi20) => ins!(ctx, "lui {}, {}", d, hi20),
            LiStep::Addi(lo) => ins!(ctx, "addi {}, {}, {}", d, src, lo),
            LiStep::Addiw(lo) => ins!(ctx, "addiw {}, {}, {}", d, d, lo),
            LiStep::Slli(n) => ins!(ctx, "slli {}, {}, {}", d, d, n),
            LiStep::Srli(n) => ins!(ctx, "srli {}, {}, {}", d, d, n),
        }
    }
}

fn mov_imm32(ctx: &mut LowerCtx, dst: Gpr, v: u32) {
    mov_imm(ctx, dst, i64::from(v));
}

fn mov_imm_sym(ctx: &mut LowerCtx, dst: Gpr, s: offlineasm_ir::SymId) -> Result<(), String> {
    let text = sym_text(ctx, s)?;
    ins!(ctx, "li {}, {}", gpr(dst), text);
    Ok(())
}

fn zero_upper32(ctx: &mut LowerCtx, d: Gpr) {
    ins!(ctx, "slli {}, {}, 32", gpr(d), gpr(d));
    ins!(ctx, "srli {}, {}, 32", gpr(d), gpr(d));
}

fn mov_imm_w(ctx: &mut LowerCtx, dst: Gpr, w: Width, v: i64) {
    if w == Width::B64 {
        mov_imm(ctx, dst, v);
    } else {
        mov_imm32(ctx, dst, v as u32);
    }
}

fn mov_reg(ctx: &mut LowerCtx, dst: Gpr, src: Gpr, w: Width) {
    if dst == src {
        return;
    }
    match w {
        Width::B64 => ins!(ctx, "addi {}, {}, 0", gpr(dst), gpr(src)),
        _ => ins!(ctx, "addiw {}, {}, 0", gpr(dst), gpr(src)),
    }
}

fn neg_reg(ctx: &mut LowerCtx, r: Gpr, w: Width) {
    if w == Width::B32 {
        ins!(ctx, "subw {}, x0, {}", gpr(r), gpr(r));
    } else {
        ins!(ctx, "sub {}, x0, {}", gpr(r), gpr(r));
    }
}

fn gpr_dst(mn: &str, op: &Op) -> Result<Gpr, String> {
    match op {
        Op::Gpr(g) => Ok(*g),
        _ => Err(format!("riscv64: `{}`: expected a GPR destination", mn)),
    }
}

fn lane_bits(w: Width) -> u32 {
    match w {
        Width::B8 => 8,
        Width::B16 => 16,
        Width::B32 => 32,
        Width::B64 => 64,
    }
}

fn lane_mask(w: Width) -> i64 {
    match w {
        Width::B8 => 0xFF,
        Width::B16 => 0xFFFF,
        Width::B32 => 0xFFFF_FFFF,
        Width::B64 => 0,
    }
}

fn load_op_gpr(ctx: &mut LowerCtx, mn: &str, op: &Op, w: Width, tmp: Gpr) -> Result<Gpr, String> {
    match op {
        Op::Gpr(g) => Ok(*g),
        Op::Imm(v) => {
            mov_imm_w(ctx, tmp, w, *v);
            Ok(tmp)
        }
        Op::Sym(s) => {
            mov_imm_sym(ctx, tmp, *s)?;
            Ok(tmp)
        }
        Op::Mem(a) => {
            e_load(ctx, mn, w, Sx::Zero, tmp, a)?;
            Ok(tmp)
        }
        _ => Err(format!(
            "riscv64: `{}`: expected a register, immediate, or memory operand",
            mn
        )),
    }
}

fn direct_addr(ctx: &LowerCtx, a: &Mem) -> Result<Option<String>, String> {
    let Some(base) = a.base else {
        return Ok(None);
    };
    if a.index.is_some() {
        return Ok(None);
    }
    match a.disp {
        Disp::Const(v) if fits_d12(v) => Ok(Some(format!("{}({})", v, gpr(base)))),
        Disp::Const(_) => Ok(None),
        Disp::Sym(s) => Ok(Some(format!("{}({})", sym_text(ctx, s)?, gpr(base)))),
        Disp::Label(_) | Disp::LabelFar(_) => Ok(None),
    }
}

/// Synthesize `base + disp + index * scale` into `tmp`.
fn addr_scratch(ctx: &mut LowerCtx, mn: &str, a: &Mem, tmp: Gpr) -> Result<(), String> {
    let (base, disp) = match a.base {
        Some(b) => (b, a.disp),
        None => {
            match a.disp {
                Disp::Const(v) => mov_imm(ctx, tmp, v as i64),
                Disp::Sym(s) => mov_imm_sym(ctx, tmp, s)?,
                Disp::Label(l) | Disp::LabelFar(l) => {
                    let text = text::label_text(ctx, Lbl::Bound(l))?;
                    ins!(ctx, "la {}, {}", gpr(tmp), text);
                }
            }
            (tmp, Disp::Const(0))
        }
    };
    match a.index {
        None => match disp {
            Disp::Const(v) if fits12(v as i64) => {
                ins!(ctx, "addi {}, {}, {}", gpr(tmp), gpr(base), v);
            }
            Disp::Const(v) => {
                mov_imm(ctx, tmp, v as i64);
                ins!(ctx, "add {}, {}, {}", gpr(tmp), gpr(tmp), gpr(base));
            }
            Disp::Sym(s) => {
                mov_imm_sym(ctx, tmp, s)?;
                ins!(ctx, "add {}, {}, {}", gpr(tmp), gpr(tmp), gpr(base));
            }
            Disp::Label(_) | Disp::LabelFar(_) => {
                return Err("riscv64: a label-addressed memory operand has no base".to_string())
            }
        },
        Some((idx, scale)) => {
            let sh: u32 = match scale {
                1 => 0,
                2 => 1,
                4 => 2,
                8 => 3,
                _ => {
                    return Err(format!("riscv64: `{}`: address scale out of range", mn));
                }
            };
            if sh == 0 {
                ins!(ctx, "add {}, {}, {}", gpr(tmp), gpr(base), gpr(idx));
            } else {
                ins!(ctx, "slli {}, {}, {}", gpr(tmp), gpr(idx), sh);
                ins!(ctx, "add {}, {}, {}", gpr(tmp), gpr(tmp), gpr(base));
            }
            match disp {
                Disp::Const(0) => {}
                Disp::Const(v) if fits12(v as i64) => {
                    ins!(ctx, "addi {}, {}, {}", gpr(tmp), gpr(tmp), v);
                }
                _ => {
                    return Err(format!(
                        "riscv64: `{}`: indexed address with a large displacement is unsupported",
                        mn
                    ));
                }
            }
        }
    }
    Ok(())
}

fn load_mnemonic(w: Width, sx: Sx) -> &'static str {
    match (w, sx) {
        (Width::B8, Sx::Zero) => "lbu",
        (Width::B8, Sx::Sign) => "lb",
        (Width::B16, Sx::Zero) => "lhu",
        (Width::B16, Sx::Sign) => "lh",
        (Width::B32, Sx::Zero) => "lwu",
        (Width::B32, Sx::Sign) => "lw",
        (Width::B64, _) => "ld",
    }
}

fn store_mnemonic(w: Width) -> &'static str {
    match w {
        Width::B8 => "sb",
        Width::B16 => "sh",
        Width::B32 => "sw",
        Width::B64 => "sd",
    }
}

fn e_load(ctx: &mut LowerCtx, mn: &str, w: Width, sx: Sx, dst: Gpr, a: &Mem) -> Result<(), String> {
    let op = load_mnemonic(w, sx);
    if let Some(addr) = direct_addr(ctx, a)? {
        ins!(ctx, "{} {}, {}", op, gpr(dst), addr);
        return Ok(());
    }
    addr_scratch(ctx, mn, a, G1)?;
    ins!(ctx, "{} {}, 0(x{})", op, gpr(dst), G1.0);
    Ok(())
}

fn e_store(ctx: &mut LowerCtx, mn: &str, w: Width, src: &Op, a: &Mem) -> Result<(), String> {
    let op = store_mnemonic(w);
    let direct = direct_addr(ctx, a)?;
    match src {
        Op::Gpr(g) => {
            if let Some(addr) = direct {
                ins!(ctx, "{} {}, {}", op, gpr(*g), addr);
                return Ok(());
            }

            let s = if *g == G1 {
                mov_reg(ctx, G2, G1, Width::B64);
                addr_scratch(ctx, mn, a, G1)?;
                G2
            } else {
                addr_scratch(ctx, mn, a, G1)?;
                *g
            };
            ins!(ctx, "{} {}, 0(x{})", op, gpr(s), G1.0);
            Ok(())
        }
        Op::Imm(v) => {
            if let Some(addr) = direct {
                mov_imm_w(ctx, G1, w, *v);
                ins!(ctx, "{} {}, {}", op, gpr(G1), addr);
                return Ok(());
            }
            mov_imm_w(ctx, G1, w, *v);
            addr_scratch(ctx, mn, a, G2)?;
            ins!(ctx, "{} {}, 0(x{})", op, gpr(G1), G2.0);
            Ok(())
        }
        Op::Sym(s) => {
            if let Some(addr) = direct {
                mov_imm_sym(ctx, G1, *s)?;
                ins!(ctx, "{} {}, {}", op, gpr(G1), addr);
                return Ok(());
            }
            mov_imm_sym(ctx, G1, *s)?;
            addr_scratch(ctx, mn, a, G2)?;
            ins!(ctx, "{} {}, 0(x{})", op, gpr(G1), G2.0);
            Ok(())
        }
        _ => Err(format!(
            "riscv64: `{}`: store needs a register, immediate, or symbolic source",
            mn
        )),
    }
}

fn e_loadf(ctx: &mut LowerCtx, mn: &str, k: FKind, dst: Fpr, a: &Mem) -> Result<(), String> {
    let op = match k {
        FKind::F32 => "flw",
        FKind::F64 => "fld",
    };
    if let Some(addr) = direct_addr(ctx, a)? {
        ins!(ctx, "{} {}, {}", op, fpr(dst), addr);
        return Ok(());
    }
    addr_scratch(ctx, mn, a, G1)?;
    ins!(ctx, "{} {}, 0(x{})", op, fpr(dst), G1.0);
    Ok(())
}

fn e_storef(ctx: &mut LowerCtx, mn: &str, k: FKind, src: Fpr, a: &Mem) -> Result<(), String> {
    let op = match k {
        FKind::F32 => "fsw",
        FKind::F64 => "fsd",
    };
    if let Some(addr) = direct_addr(ctx, a)? {
        ins!(ctx, "{} {}, {}", op, fpr(src), addr);
        return Ok(());
    }
    addr_scratch(ctx, mn, a, G1)?;
    ins!(ctx, "{} {}, 0(x{})", op, fpr(src), G1.0);
    Ok(())
}

fn e_loadv(ctx: &mut LowerCtx, mn: &str, dst: Fpr, a: &Mem) -> Result<(), String> {
    let hi = fhi(dst)?;
    let hi_disp = a
        .disp
        .const_or_zero()
        .checked_add(8)
        .ok_or_else(|| format!("riscv64: `{}`: vector address overflow", mn))?;
    if a.index.is_none()
        && a.base.is_some()
        && fits_d12(a.disp.const_or_zero())
        && fits_d12(hi_disp)
    {
        let b = a.base_reg();
        ins!(
            ctx,
            "fld {}, {}(x{})",
            fpr(dst),
            a.disp.const_or_zero(),
            b.0
        );
        ins!(ctx, "fld {}, {}(x{})", fpr(hi), hi_disp, b.0);
        return Ok(());
    }
    addr_scratch(ctx, mn, a, G1)?;
    ins!(ctx, "fld {}, 0(x{})", fpr(dst), G1.0);
    ins!(ctx, "fld {}, 8(x{})", fpr(hi), G1.0);
    Ok(())
}

fn e_storev(ctx: &mut LowerCtx, mn: &str, src: Fpr, a: &Mem) -> Result<(), String> {
    let hi = fhi(src)?;
    let hi_disp = a
        .disp
        .const_or_zero()
        .checked_add(8)
        .ok_or_else(|| format!("riscv64: `{}`: vector address overflow", mn))?;
    if a.index.is_none()
        && a.base.is_some()
        && fits_d12(a.disp.const_or_zero())
        && fits_d12(hi_disp)
    {
        let b = a.base_reg();
        ins!(
            ctx,
            "fsd {}, {}(x{})",
            fpr(src),
            a.disp.const_or_zero(),
            b.0
        );
        ins!(ctx, "fsd {}, {}(x{})", fpr(hi), hi_disp, b.0);
        return Ok(());
    }
    // Park the high lane in the FP scratch while the address folds.
    if hi != SF {
        ins!(ctx, "fmv.d {}, {}", fpr(SF), fpr(hi));
    }
    addr_scratch(ctx, mn, a, G1)?;
    ins!(ctx, "fsd {}, 0(x{})", fpr(src), G1.0);
    ins!(ctx, "fsd {}, 8(x{})", fpr(SF), G1.0);
    Ok(())
}

fn e_vmov(ctx: &mut LowerCtx, dst: Fpr, src: Fpr) -> Result<(), String> {
    if dst == src {
        return Ok(());
    }
    let dhi = fhi(dst)?;
    let shi = fhi(src)?;
    ins!(ctx, "fmv.d {}, {}", fpr(dst), fpr(src));
    ins!(ctx, "fmv.d {}, {}", fpr(dhi), fpr(shi));
    Ok(())
}

fn e_vecextract(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    dst: Gpr,
    src: Fpr,
    lane: u8,
) -> Result<(), String> {
    let size: u32 = match w {
        Width::B8 => 1,
        Width::B16 => 2,
        Width::B32 => 4,
        Width::B64 => 8,
    };
    let lanes: u32 = 16 / size;
    if u32::from(lane) >= lanes {
        return Err(format!("riscv64: `{}`: lane out of range", mn));
    }
    let hi = fhi(src)?;
    if w == Width::B64 {
        let from = if lane == 0 { src } else { hi };
        ins!(ctx, "fmv.x.d {}, {}", gpr(dst), fpr(from));
        return Ok(());
    }
    // Sub-64 lanes spill the holding half through `sp` (balanced).
    let byte = u32::from(lane) * size;
    let (half, off) = if byte < 8 {
        (src, byte as i32)
    } else {
        (hi, (byte - 8) as i32)
    };
    ins!(ctx, "addi x2, x2, -8");
    ins!(ctx, "fsd {}, 0(x2)", fpr(half));
    let op = match w {
        Width::B8 => "lbu",
        Width::B16 => "lhu",
        Width::B32 => "lw",
        Width::B64 => "ld",
    };
    ins!(ctx, "{} {}, {}(x2)", op, gpr(dst), off);
    ins!(ctx, "addi x2, x2, 8");
    Ok(())
}

fn e_mov(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    dst: &Op,
    src: &Op,
    patch: bool,
) -> Result<(), String> {
    let _ = patch;
    match (src, dst) {
        (Op::Imm(v), Op::Gpr(d)) => {
            mov_imm_w(ctx, *d, w, *v);
            Ok(())
        }
        (Op::Sym(s), Op::Gpr(d)) => {
            mov_imm_sym(ctx, *d, *s)?;
            if w == Width::B32 {
                zero_upper32(ctx, *d);
            }
            Ok(())
        }
        (Op::Gpr(s), Op::Gpr(d)) => {
            match w {
                Width::B64 => mov_reg(ctx, *d, *s, Width::B64),
                Width::B32 => {
                    // A 32-bit move zeroes the upper half, even when the
                    // source and destination are the same register.
                    ins!(ctx, "slli {}, {}, 32", gpr(*d), gpr(*s));
                    ins!(ctx, "srli {}, {}, 32", gpr(*d), gpr(*d));
                }
                Width::B8 | Width::B16 => {
                    if s != d {
                        let (sh, n) = if w == Width::B8 { (56, 8) } else { (48, 16) };
                        ins!(ctx, "slli {}, {}, {}", gpr(G1), gpr(*s), sh);
                        ins!(ctx, "srli {}, {}, {}", gpr(G1), gpr(G1), sh);
                        ins!(ctx, "srli {}, {}, {}", gpr(*d), gpr(*d), n);
                        ins!(ctx, "slli {}, {}, {}", gpr(*d), gpr(*d), n);
                        ins!(ctx, "or {}, {}, {}", gpr(*d), gpr(*d), gpr(G1));
                    }
                }
            }
            Ok(())
        }
        (Op::Label(l), Op::Gpr(d)) => {
            let name = text::label_text(ctx, *l)?;
            // `lla`: the direct PC-relative address (`auipc` + `addi`), as x86-64
            // and AArch64 print, never a GOT load.
            ins!(ctx, "lla {}, {}", gpr(*d), name);
            match w {
                Width::B64 => {}
                Width::B32 => zero_upper32(ctx, *d),
                _ => mov_reg(ctx, *d, *d, w),
            }
            Ok(())
        }
        (Op::Mem(a), Op::Gpr(d)) => e_load(ctx, mn, w, Sx::Zero, *d, a),
        (Op::Gpr(s), Op::Mem(a)) => e_store(ctx, mn, w, &Op::Gpr(*s), a),
        (Op::Imm(v), Op::Mem(a)) => e_store(ctx, mn, w, &Op::Imm(*v), a),
        (Op::Sym(s), Op::Mem(a)) => e_store(ctx, mn, w, &Op::Sym(*s), a),
        _ => Err(format!("riscv64: `{}`: unsupported mov operand pair", mn)),
    }
}

fn e_movzero32(ctx: &mut LowerCtx, mn: &str, dst: &Op, src: &Op) -> Result<(), String> {
    match (dst, src) {
        (Op::Gpr(d), Op::Gpr(s)) => {
            ins!(ctx, "slli {}, {}, 32", gpr(*d), gpr(*s));
            ins!(ctx, "srli {}, {}, 32", gpr(*d), gpr(*d));
            Ok(())
        }
        (Op::Gpr(d), Op::Mem(a)) => e_load(ctx, mn, Width::B32, Sx::Zero, *d, a),
        (Op::Mem(a), Op::Gpr(s)) => e_store(ctx, mn, Width::B32, &Op::Gpr(*s), a),
        _ => Err(format!(
            "riscv64: `{}`: movzero32 needs register/memory operands",
            mn
        )),
    }
}

fn e_bswap(ctx: &mut LowerCtx, mn: &str, w: Width, dst: &Op, src: &Op) -> Result<(), String> {
    let (d, s) = match (dst, src) {
        (Op::Gpr(d), Op::Gpr(s)) => (*d, *s),
        _ => {
            return Err(format!(
                "riscv64: `{}`: bswap needs general-purpose registers",
                mn
            ));
        }
    };
    let (mask1, mask2) = match w {
        Width::B32 => (0x00FF_00FFi64, 0x0000_FFFFi64),
        Width::B64 => (
            0x00FF_00FF_00FF_00FFu64 as i64,
            0x0000_FFFF_0000_FFFFu64 as i64,
        ),
        _ => {
            return Err(format!("riscv64: `{}`: bswap needs a 32/64-bit width", mn));
        }
    };
    if d != s {
        ins!(ctx, "add {}, {}, x0", gpr(d), gpr(s));
    }
    // Byte swap inside each 16-bit half.
    mov_imm(ctx, G1, mask1);
    ins!(ctx, "and {}, {}, {}", gpr(G2), gpr(d), gpr(G1));
    ins!(ctx, "slli {}, {}, 8", gpr(G2), gpr(G2));
    ins!(ctx, "srli {}, {}, 8", gpr(G1), gpr(d));
    mov_imm(ctx, d, mask1);
    ins!(ctx, "and {}, {}, {}", gpr(d), gpr(G1), gpr(d));
    ins!(ctx, "or {}, {}, {}", gpr(d), gpr(d), gpr(G2));
    // Then the 16-bit halves.
    mov_imm(ctx, G1, mask2);
    ins!(ctx, "and {}, {}, {}", gpr(G2), gpr(d), gpr(G1));
    ins!(ctx, "slli {}, {}, 16", gpr(G2), gpr(G2));
    ins!(ctx, "srli {}, {}, 16", gpr(G1), gpr(d));
    mov_imm(ctx, d, mask2);
    ins!(ctx, "and {}, {}, {}", gpr(d), gpr(G1), gpr(d));
    ins!(ctx, "or {}, {}, {}", gpr(d), gpr(d), gpr(G2));
    if w == Width::B64 {
        ins!(ctx, "slli {}, {}, 32", gpr(G1), gpr(d));
        ins!(ctx, "srli {}, {}, 32", gpr(d), gpr(d));
        ins!(ctx, "or {}, {}, {}", gpr(d), gpr(d), gpr(G1));
    }
    Ok(())
}

fn e_lea(ctx: &mut LowerCtx, mn: &str, w: Width, dst: Gpr, src: &LeaSrc) -> Result<(), String> {
    match src {
        LeaSrc::Mem(a) => {
            let needs_tmp =
                a.index.is_none() && !fits12(a.disp.const_or_zero() as i64) && a.base == Some(dst);
            if needs_tmp {
                addr_scratch(ctx, mn, a, G1)?;
                mov_reg(ctx, dst, G1, Width::B64);
            } else {
                addr_scratch(ctx, mn, a, dst)?;
            }
        }
        LeaSrc::Label(l) => {
            let name = text::label_text(ctx, *l)?;
            // `lla`: the direct PC-relative address (`auipc` + `addi`).
            ins!(ctx, "lla {}, {}", gpr(dst), name);
        }
        LeaSrc::Extern(e) => e_extern_address(ctx, dst, *e)?,
    }
    if w == Width::B32 {
        zero_upper32(ctx, dst);
    }
    Ok(())
}

/// Materializes extern `e`'s address into `dst`: `lla` (`auipc` + `addi`)
/// for a near extern, `lga` (`auipc` + `ld` of its GOT entry) for a far one.
fn e_extern_address(ctx: &mut LowerCtx, dst: Gpr, e: Extern) -> Result<(), String> {
    let sym = text::extern_text(ctx, e.id)?;
    match e.reach {
        Reach::Near => ins!(ctx, "lla {}, {}", gpr(dst), sym),
        Reach::Far => ins!(ctx, "lga {}, {}", gpr(dst), sym),
    }
    Ok(())
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AluKind {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
}

impl AluKind {
    fn mnemonic(self) -> &'static str {
        match self {
            AluKind::Add => "add",
            AluKind::Sub => "sub",
            AluKind::Mul => "mul",
            AluKind::And => "and",
            AluKind::Or => "or",
            AluKind::Xor => "xor",
        }
    }

    fn imm_mnemonic(self) -> &'static str {
        match self {
            AluKind::Add | AluKind::Sub => "addi",
            AluKind::And => "andi",
            AluKind::Or => "ori",
            AluKind::Xor => "xori",
            AluKind::Mul => "addi",
        }
    }
}

fn alu_args(alu: &Alu3) -> Vec<Op> {
    if op_eq(&alu.lhs, &alu.dst) {
        vec![alu.rhs, alu.dst]
    } else {
        vec![alu.lhs, alu.rhs, alu.dst]
    }
}

fn alu_rr(ctx: &mut LowerCtx, k: AluKind, w: Width, dst: Gpr, lhs: Gpr, rhs: Gpr) {
    ins!(
        ctx,
        "{} {}, {}, {}",
        k.mnemonic(),
        gpr(dst),
        gpr(lhs),
        gpr(rhs)
    );
    if w == Width::B32 {
        zero_upper32(ctx, dst);
    }
}

fn alu_narrow_merge(ctx: &mut LowerCtx, w: Width, dst: Gpr) {
    let n = if w == Width::B8 { 8 } else { 16 };
    ins!(ctx, "slli {}, {}, {}", gpr(G1), gpr(G1), 64 - n);
    ins!(ctx, "srli {}, {}, {}", gpr(G1), gpr(G1), 64 - n);
    ins!(ctx, "srli {}, {}, {}", gpr(dst), gpr(dst), n);
    ins!(ctx, "slli {}, {}, {}", gpr(dst), gpr(dst), n);
    ins!(ctx, "or {}, {}, {}", gpr(dst), gpr(dst), gpr(G1));
}

fn alu_narrow(
    ctx: &mut LowerCtx,
    mn: &str,
    k: AluKind,
    w: Width,
    dst: Gpr,
    rhs: Gpr,
) -> Result<(), String> {
    if dst == G1 {
        return Err(format!(
            "riscv64: `{}`: narrow ALU aliased the scratch register",
            mn
        ));
    }
    ins!(
        ctx,
        "{} {}, {}, {}",
        k.mnemonic(),
        gpr(G1),
        gpr(dst),
        gpr(rhs)
    );
    alu_narrow_merge(ctx, w, dst);
    Ok(())
}

fn alu_reg(
    ctx: &mut LowerCtx,
    mn: &str,
    k: AluKind,
    w: Width,
    dst: Gpr,
    rhs: &Op,
) -> Result<(), String> {
    let narrow = w == Width::B8 || w == Width::B16;
    match rhs {
        Op::Gpr(s) => {
            if narrow {
                alu_narrow(ctx, mn, k, w, dst, *s)?;
            } else {
                alu_rr(ctx, k, w, dst, dst, *s);
            }
            Ok(())
        }
        Op::Mem(a) => {
            let lw = if w == Width::B64 { w } else { Width::B32 };
            e_load(ctx, mn, lw, Sx::Zero, G1, a)?;
            if narrow {
                alu_narrow(ctx, mn, k, w, dst, G1)?;
            } else {
                alu_rr(ctx, k, w, dst, dst, G1);
            }
            Ok(())
        }
        Op::Imm(v) => alu_imm(ctx, mn, k, w, dst, *v),
        Op::Sym(s) => {
            mov_imm_sym(ctx, G1, *s)?;
            if narrow {
                alu_narrow(ctx, mn, k, w, dst, G1)?;
            } else {
                alu_rr(ctx, k, w, dst, dst, G1);
            }
            Ok(())
        }
        _ => Err(format!(
            "riscv64: `{}`: ALU needs a register, memory, or immediate source",
            mn
        )),
    }
}

fn alu_imm(
    ctx: &mut LowerCtx,
    mn: &str,
    k: AluKind,
    w: Width,
    dst: Gpr,
    v: i64,
) -> Result<(), String> {
    let narrow = w == Width::B8 || w == Width::B16;
    if fits12(v) && k != AluKind::Mul {
        let imm = if k == AluKind::Sub { -v } else { v };
        if narrow {
            ins!(
                ctx,
                "{} {}, {}, {}",
                k.imm_mnemonic(),
                gpr(G1),
                gpr(dst),
                imm
            );
            alu_narrow_merge(ctx, w, dst);
            return Ok(());
        }
        ins!(
            ctx,
            "{} {}, {}, {}",
            k.imm_mnemonic(),
            gpr(dst),
            gpr(dst),
            imm
        );
        if w == Width::B32 {
            zero_upper32(ctx, dst);
        }
        return Ok(());
    }
    let lw = if w == Width::B64 { w } else { Width::B32 };
    mov_imm_w(ctx, G1, lw, v);
    if narrow {
        alu_narrow(ctx, mn, k, w, dst, G1)
    } else {
        alu_rr(ctx, k, w, dst, dst, G1);
        Ok(())
    }
}

fn alu_mem_dst(
    ctx: &mut LowerCtx,
    mn: &str,
    k: AluKind,
    w: Width,
    a: &Mem,
    rhs: &Op,
) -> Result<(), String> {
    let lw = if w == Width::B64 { w } else { Width::B32 };
    e_load(ctx, mn, lw, Sx::Zero, G1, a)?;
    alu_mem_rhs(ctx, mn, k, w, rhs)?;
    e_store(ctx, mn, w, &Op::Gpr(G1), a)
}

/// 3-op memory-destination ALU: `lhs` into scratch, fold `rhs`, store.
fn alu_mem_dst3(
    ctx: &mut LowerCtx,
    mn: &str,
    k: AluKind,
    w: Width,
    a: &Mem,
    lhs: &Op,
    rhs: &Op,
) -> Result<(), String> {
    let lw = if w == Width::B64 { w } else { Width::B32 };
    match lhs {
        Op::Gpr(g) => mov_reg(ctx, G1, *g, lw),
        Op::Imm(v) => mov_imm_w(ctx, G1, lw, *v),
        Op::Sym(s) => mov_imm_sym(ctx, G1, *s)?,
        Op::Mem(l) => e_load(ctx, mn, lw, Sx::Zero, G1, l)?,
        _ => {
            return Err(format!(
                "riscv64: `{}`: ALU needs a register, memory, or immediate source",
                mn
            ));
        }
    }
    alu_mem_rhs(ctx, mn, k, w, rhs)?;
    e_store(ctx, mn, w, &Op::Gpr(G1), a)
}

fn alu_mem_rhs(ctx: &mut LowerCtx, mn: &str, k: AluKind, w: Width, rhs: &Op) -> Result<(), String> {
    match rhs {
        Op::Gpr(s) => {
            ins!(
                ctx,
                "{} {}, {}, {}",
                k.mnemonic(),
                gpr(G1),
                gpr(G1),
                gpr(*s)
            );
            if w == Width::B8 || w == Width::B16 {
                // The cell is reloaded fresh, so no upper-bit preservation is
                // needed. Truncate the folded lane.
                let sh = if w == Width::B8 { 56 } else { 48 };
                ins!(ctx, "slli {}, {}, {}", gpr(G1), gpr(G1), sh);
                ins!(ctx, "srli {}, {}, {}", gpr(G1), gpr(G1), sh);
            } else if w == Width::B32 {
                zero_upper32(ctx, G1);
            }
            Ok(())
        }
        Op::Imm(v) => match k {
            AluKind::Add | AluKind::Sub => {
                let (add, mag) = if *v < 0 {
                    (k != AluKind::Add, v.wrapping_neg())
                } else {
                    (k == AluKind::Add, *v)
                };
                if !fits12(mag) {
                    return Err(format!(
                        "riscv64: `{}`: memory-destination ALU needs a register or 12-bit \
                         immediate rhs",
                        mn
                    ));
                }
                let imm = if add { mag } else { -mag };
                ins!(ctx, "addi {}, {}, {}", gpr(G1), gpr(G1), imm);
                if w == Width::B32 {
                    zero_upper32(ctx, G1);
                }
                Ok(())
            }
            _ => Err(format!(
                "riscv64: `{}`: memory-destination ALU needs a register or add/sub rhs",
                mn
            )),
        },
        Op::Sym(s) => {
            mov_imm_sym(ctx, G2, *s)?;
            ins!(
                ctx,
                "{} {}, {}, {}",
                k.mnemonic(),
                gpr(G1),
                gpr(G1),
                gpr(G2)
            );
            Ok(())
        }
        _ => Err(format!(
            "riscv64: `{}`: memory-destination ALU needs a register or immediate rhs",
            mn
        )),
    }
}

fn op_n(ctx: &mut LowerCtx, mn: &str, k: AluKind, w: Width, ops: &[Op]) -> Result<(), String> {
    if ops.len() != 2 && ops.len() != 3 {
        return Err(format!(
            "riscv64: `{}`: expected 2 or 3 operands, got {}",
            mn,
            ops.len()
        ));
    }
    if ops.len() == 2 {
        if let Op::Mem(a) = &ops[1] {
            return alu_mem_dst(ctx, mn, k, w, a, &ops[0]);
        }
        let dst = gpr_dst(mn, &ops[1])?;
        return alu_reg(ctx, mn, k, w, dst, &ops[0]);
    }
    if let Op::Mem(a) = &ops[2] {
        return alu_mem_dst3(ctx, mn, k, w, a, &ops[0], &ops[1]);
    }
    let dst = gpr_dst(mn, &ops[2])?;
    if op_eq(&ops[0], &ops[2]) {
        return alu_reg(ctx, mn, k, w, dst, &ops[1]);
    }
    if op_eq(&ops[1], &ops[2]) {
        if k == AluKind::Sub {
            if w == Width::B8 || w == Width::B16 {
                // `dst = lhs - dst`: the old dst survives on the stack while
                // scratch folds the subtraction.
                let n = if w == Width::B8 { 8 } else { 16 };
                ins!(ctx, "addi x2, x2, -8");
                ins!(ctx, "sd {}, 0(x2)", gpr(dst));
                ins!(ctx, "addi {}, {}, 0", gpr(G1), gpr(dst));
                neg_reg(ctx, G1, Width::B64);
                match &ops[0] {
                    Op::Gpr(g) => mov_reg(ctx, dst, *g, w),
                    Op::Imm(v) => mov_imm_w(ctx, dst, w, *v),
                    Op::Sym(s) => mov_imm_sym(ctx, dst, *s)?,
                    Op::Mem(a) => e_load(ctx, mn, Width::B32, Sx::Zero, dst, a)?,
                    _ => {
                        return Err(format!(
                            "riscv64: `{}`: ALU needs a register, memory, or immediate source",
                            mn
                        ));
                    }
                }
                ins!(ctx, "add {}, {}, {}", gpr(G1), gpr(dst), gpr(G1));
                ins!(ctx, "slli {}, {}, {}", gpr(G1), gpr(G1), 64 - n);
                ins!(ctx, "srli {}, {}, {}", gpr(G1), gpr(G1), 64 - n);
                ins!(ctx, "ld {}, 0(x2)", gpr(dst));
                ins!(ctx, "addi x2, x2, 8");
                ins!(ctx, "srli {}, {}, {}", gpr(dst), gpr(dst), n);
                ins!(ctx, "slli {}, {}, {}", gpr(dst), gpr(dst), n);
                ins!(ctx, "or {}, {}, {}", gpr(dst), gpr(dst), gpr(G1));
                return Ok(());
            }
            // `dst = lhs - dst`: negate the old dst in scratch, move lhs to
            // dst, then add.
            mov_reg(ctx, G1, dst, w);
            neg_reg(ctx, G1, w);
            match &ops[0] {
                Op::Gpr(g) => mov_reg(ctx, dst, *g, w),
                Op::Imm(v) => mov_imm_w(ctx, dst, w, *v),
                Op::Sym(s) => mov_imm_sym(ctx, dst, *s)?,
                Op::Mem(a) => {
                    let lw = if w == Width::B64 { w } else { Width::B32 };
                    e_load(ctx, mn, lw, Sx::Zero, dst, a)?;
                }
                _ => {
                    return Err(format!(
                        "riscv64: `{}`: ALU needs a register, memory, or immediate source",
                        mn
                    ));
                }
            }
            if w == Width::B32 {
                zero_upper32(ctx, G1);
            }
            return alu_reg(ctx, mn, AluKind::Add, w, dst, &Op::Gpr(G1));
        }
        if matches!(
            k,
            AluKind::Add | AluKind::Mul | AluKind::And | AluKind::Or | AluKind::Xor
        ) {
            return alu_reg(ctx, mn, k, w, dst, &ops[0]);
        }
        return Err(format!(
            "riscv64: `{}`: aliased operands need a commutative op",
            mn
        ));
    }
    // Disjoint register operands fold into RISC-V's native three-operand
    // encoding: `dst = lhs OP rhs` in one instruction.
    if (w == Width::B64 || w == Width::B32)
        && matches!((&ops[0], &ops[1]), (Op::Gpr(_), Op::Gpr(_)))
    {
        if let (Op::Gpr(l), Op::Gpr(r)) = (&ops[0], &ops[1]) {
            ins!(
                ctx,
                "{} {}, {}, {}",
                k.mnemonic(),
                gpr(dst),
                gpr(*l),
                gpr(*r)
            );
            if w == Width::B32 {
                zero_upper32(ctx, dst);
            }
            return Ok(());
        }
    }
    // Otherwise move `lhs` to `dst` first (memory lhs goes through scratch).
    let lw = if w == Width::B64 { w } else { Width::B32 };
    match &ops[0] {
        Op::Gpr(g) => mov_reg(ctx, dst, *g, lw),
        Op::Imm(v) => mov_imm_w(ctx, dst, lw, *v),
        Op::Sym(s) => mov_imm_sym(ctx, dst, *s)?,
        Op::Mem(a) => e_load(ctx, mn, lw, Sx::Zero, dst, a)?,
        _ => {
            return Err(format!(
                "riscv64: `{}`: ALU needs a register, memory, or immediate source",
                mn
            ));
        }
    }
    alu_reg(ctx, mn, k, w, dst, &ops[1])
}

/// `Not` / `Neg`.
fn e_not_neg(ctx: &mut LowerCtx, mn: &str, w: Width, dst: &Op, neg: bool) -> Result<(), String> {
    let d = gpr_dst(mn, dst)?;
    if neg {
        if w == Width::B32 {
            ins!(ctx, "subw {}, x0, {}", gpr(d), gpr(d));
            zero_upper32(ctx, d);
        } else {
            ins!(ctx, "sub {}, x0, {}", gpr(d), gpr(d));
        }
        return Ok(());
    }
    if w == Width::B8 || w == Width::B16 {
        let n = if w == Width::B8 { 8 } else { 16 };
        // The complemented lane builds in a scratch register the reload of
        // `d` does not overwrite (`atomicxchgclear*` complements in `G1`).
        let t = if d == G1 { G2 } else { G1 };
        ins!(ctx, "addi x2, x2, -8");
        ins!(ctx, "sd {}, 0(x2)", gpr(d));
        ins!(ctx, "xori {}, {}, -1", gpr(t), gpr(d));
        ins!(ctx, "slli {}, {}, {}", gpr(t), gpr(t), 64 - n);
        ins!(ctx, "srli {}, {}, {}", gpr(t), gpr(t), 64 - n);
        ins!(ctx, "ld {}, 0(x2)", gpr(d));
        ins!(ctx, "addi x2, x2, 8");
        ins!(ctx, "srli {}, {}, {}", gpr(d), gpr(d), n);
        ins!(ctx, "slli {}, {}, {}", gpr(d), gpr(d), n);
        ins!(ctx, "or {}, {}, {}", gpr(d), gpr(d), gpr(t));
    } else {
        ins!(ctx, "xori {}, {}, -1", gpr(d), gpr(d));
        if w == Width::B32 {
            zero_upper32(ctx, d);
        }
    }
    Ok(())
}

/// `MulImm`: `dst = lhs * imm`.
fn e_mulimm(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    dst: Gpr,
    lhs: Gpr,
    v: i64,
) -> Result<(), String> {
    // Power-of-two multipliers become shifts.
    if v > 0 && (v as u64).is_power_of_two() {
        let sh = (v as u64).trailing_zeros() as i64;
        if dst != lhs {
            mov_reg(ctx, dst, lhs, w);
        }
        if w == Width::B32 {
            ins!(ctx, "slliw {}, {}, {}", gpr(dst), gpr(dst), sh);
            return Ok(());
        }
        return e_shift(ctx, mn, w, ShiftOp::Shl, dst, &ShiftCnt::Imm(sh));
    }
    let lw = if w == Width::B64 { w } else { Width::B32 };
    mov_imm_w(ctx, G1, lw, v);
    if w == Width::B8 || w == Width::B16 {
        alu_narrow(ctx, mn, AluKind::Mul, w, dst, G1)
    } else {
        alu_rr(ctx, AluKind::Mul, w, dst, lhs, G1);
        Ok(())
    }
}

/// The `w` suffix of a shift mnemonic (`""` for `B64`, `"w"` for `B32`).
fn w32(w: Width) -> &'static str {
    if w == Width::B32 {
        "w"
    } else {
        ""
    }
}

/// Rotate left by an already-masked, nonzero immediate.
fn rotl_imm(ctx: &mut LowerCtx, mn: &str, w: Width, dst: Gpr, r: i64) -> Result<(), String> {
    if r == 0 {
        return Ok(());
    }
    if dst == G1 {
        return Err(format!(
            "riscv64: `{}`: rotate aliased the scratch register",
            mn
        ));
    }
    let bits: i64 = if w == Width::B32 { 32 } else { 64 };
    ins!(ctx, "slli{} {}, {}, {}", w32(w), gpr(G1), gpr(dst), r);
    ins!(
        ctx,
        "srli{} {}, {}, {}",
        w32(w),
        gpr(dst),
        gpr(dst),
        bits - r
    );
    ins!(ctx, "or {}, {}, {}", gpr(dst), gpr(dst), gpr(G1));
    if w == Width::B32 {
        zero_upper32(ctx, dst);
    }
    Ok(())
}

/// Rotate by a register count (left when `left`).
fn rot_reg(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    dst: Gpr,
    cnt: Gpr,
    left: bool,
) -> Result<(), String> {
    let bits: i64 = if w == Width::B32 { 32 } else { 64 };
    if dst == G1 || cnt == G1 {
        return Err(format!(
            "riscv64: `{}`: rotate aliased the scratch register",
            mn
        ));
    }
    ins!(ctx, "sub {}, x0, {}", gpr(G1), gpr(cnt));
    ins!(ctx, "addi {}, {}, {}", gpr(G1), gpr(G1), bits);
    let (a, b) = if left { ("srl", "sll") } else { ("sll", "srl") };
    ins!(
        ctx,
        "{}{} {}, {}, {}",
        a,
        w32(w),
        gpr(G1),
        gpr(dst),
        gpr(G1)
    );
    ins!(
        ctx,
        "{}{} {}, {}, {}",
        b,
        w32(w),
        gpr(dst),
        gpr(dst),
        gpr(cnt)
    );
    ins!(ctx, "or {}, {}, {}", gpr(dst), gpr(dst), gpr(G1));
    if w == Width::B32 {
        zero_upper32(ctx, dst);
    }
    Ok(())
}

fn lane_rot_reg(ctx: &mut LowerCtx, n: i64, dst: Gpr, cnt: Gpr, left: bool) -> Result<(), String> {
    ins!(ctx, "addi {}, x0, {}", gpr(G1), n);
    ins!(ctx, "remu {}, {}, {}", gpr(G1), gpr(cnt), gpr(G1));
    let done = fresh(ctx);
    ins!(ctx, "beq {}, x0, {}", gpr(G1), done);
    ins!(ctx, "addi x2, x2, -24");
    ins!(ctx, "sd {}, 16(x2)", gpr(dst));
    ins!(ctx, "sd {}, 8(x2)", gpr(dst));
    ins!(ctx, "sd {}, 0(x2)", gpr(G1));
    let (shift_in, shift_out) = if left { ("sll", "srl") } else { ("srl", "sll") };
    ins!(ctx, "ld {}, 16(x2)", gpr(dst));
    ins!(ctx, "ld {}, 0(x2)", gpr(G1));
    ins!(ctx, "{} {}, {}, {}", shift_in, gpr(dst), gpr(dst), gpr(G1));
    ins!(ctx, "sd {}, 16(x2)", gpr(dst));
    ins!(ctx, "ld {}, 8(x2)", gpr(dst));
    ins!(ctx, "ld {}, 0(x2)", gpr(G1));
    ins!(ctx, "sub {}, x0, {}", gpr(G1), gpr(G1));
    ins!(ctx, "addi {}, {}, {}", gpr(G1), gpr(G1), n);
    ins!(ctx, "{} {}, {}, {}", shift_out, gpr(dst), gpr(dst), gpr(G1));
    ins!(ctx, "ld {}, 16(x2)", gpr(G1));
    ins!(ctx, "or {}, {}, {}", gpr(dst), gpr(dst), gpr(G1));
    ins!(ctx, "addi x2, x2, 24");
    bind(ctx, &done);
    Ok(())
}

/// The `.s`/`.d` suffix of a scalar FP instruction.
fn fp_suffix(k: FKind) -> &'static str {
    match k {
        FKind::F32 => "s",
        FKind::F64 => "d",
    }
}

/// FP source into an FPR: FPRs pass through, memory loads into the FP
/// scratch, immediates materialize through the GPR scratch and a move.
fn fp_src(ctx: &mut LowerCtx, mn: &str, k: FKind, op: &Op) -> Result<Fpr, String> {
    match op {
        Op::Fpr(f) => Ok(*f),
        Op::Mem(a) => {
            e_loadf(ctx, mn, k, SF, a)?;
            Ok(SF)
        }
        Op::Imm(v) => {
            mov_imm(ctx, G1, *v);
            match k {
                FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", fpr(SF), gpr(G1)),
                FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", fpr(SF), gpr(G1)),
            }
            Ok(SF)
        }
        Op::Sym(s) => {
            mov_imm_sym(ctx, G1, *s)?;
            match k {
                FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", fpr(SF), gpr(G1)),
                FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", fpr(SF), gpr(G1)),
            }
            Ok(SF)
        }
        _ => Err(format!(
            "riscv64: `{}`: float operand needs an FPR, memory, or immediate",
            mn
        )),
    }
}

/// Move one FP register to another.
fn rv_fmov(ctx: &mut LowerCtx, k: FKind, dst: Fpr, src: Fpr) {
    if dst == src {
        return;
    }
    match k {
        FKind::F32 => ins!(ctx, "fmv.s {}, {}", fpr(dst), fpr(src)),
        FKind::F64 => ins!(ctx, "fmv.d {}, {}", fpr(dst), fpr(src)),
    }
}

/// Materialize a memory or immediate operand into a chosen FP register.
fn rv_stage(ctx: &mut LowerCtx, mn: &str, k: FKind, dst: Fpr, src: &Op) -> Result<(), String> {
    match src {
        Op::Fpr(f) => rv_fmov(ctx, k, dst, *f),
        Op::Mem(a) => e_loadf(ctx, mn, k, dst, a)?,
        Op::Imm(v) => {
            mov_imm(ctx, G1, *v);
            match k {
                FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", fpr(dst), gpr(G1)),
                FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", fpr(dst), gpr(G1)),
            }
        }
        Op::Sym(s) => {
            mov_imm_sym(ctx, G1, *s)?;
            match k {
                FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", fpr(dst), gpr(G1)),
                FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", fpr(dst), gpr(G1)),
            }
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: float operand needs an FPR, memory, or immediate",
                mn
            ));
        }
    }
    Ok(())
}

/// `FArith`: `dst = dst OP lhs`, or the native three-operand form.
fn e_farith(
    ctx: &mut LowerCtx,
    mn: &str,
    op: FAlu,
    k: FKind,
    arith: &FArith3,
) -> Result<(), String> {
    let d = arith.dst;
    let (n, m) = match &arith.rhs {
        Some(rhs) => {
            // `rhs` stages into the scratch FPR whenever it is memory, an
            // immediate, or the destination. That leaves `dst` free to
            // receive a staged `lhs`.
            let m = match rhs {
                Op::Fpr(f) if *f != arith.dst => *f,
                Op::Fpr(f) => {
                    rv_fmov(ctx, k, SF, *f);
                    SF
                }
                other => {
                    rv_stage(ctx, mn, k, SF, other)?;
                    SF
                }
            };
            let n = match &arith.lhs {
                Op::Fpr(f) => *f,
                other => {
                    rv_stage(ctx, mn, k, arith.dst, other)?;
                    arith.dst
                }
            };
            (n, m)
        }
        None => (d, fp_src(ctx, mn, k, &arith.lhs)?),
    };
    let sfx = fp_suffix(k);
    let name = match op {
        FAlu::Add => "fadd",
        FAlu::Sub => "fsub",
        FAlu::Mul => "fmul",
        FAlu::Div => "fdiv",
        FAlu::Min => "fmin",
        FAlu::Max => "fmax",
    };
    if matches!(op, FAlu::Min | FAlu::Max) {
        ins!(ctx, "{}.{} {}, {}, {}", name, sfx, fpr(d), fpr(n), fpr(m));
    } else {
        ins!(
            ctx,
            "{}.{} {}, {}, {}, dyn",
            name,
            sfx,
            fpr(d),
            fpr(n),
            fpr(m)
        );
    }
    Ok(())
}

/// `Fma`: `dst = op(a, b, c)`.
#[allow(clippy::too_many_arguments)]
fn e_fma(
    ctx: &mut LowerCtx,
    mn: &str,
    op: FmaOp,
    k: FKind,
    a: &Op,
    b: &Op,
    c: &Op,
    dst: Fpr,
) -> Result<(), String> {
    let ra = fp_src(ctx, mn, k, a)?;
    let rb = fp_src(ctx, mn, k, b)?;
    let rc = fp_src(ctx, mn, k, c)?;
    let sfx = fp_suffix(k);
    let name = match op {
        FmaOp::Add => "fmadd",
        FmaOp::Sub => "fmsub",
        FmaOp::NegAdd => "fnmsub",
        FmaOp::NegSub => "fnmadd",
    };
    ins!(
        ctx,
        "{}.{} {}, {}, {}, {}, dyn",
        name,
        sfx,
        fpr(dst),
        fpr(ra),
        fpr(rb),
        fpr(rc)
    );
    Ok(())
}

/// `FSqrt`.
fn e_fsqrt(ctx: &mut LowerCtx, mn: &str, k: FKind, dst: Fpr, src: &Op) -> Result<(), String> {
    let r = fp_src(ctx, mn, k, src)?;
    ins!(ctx, "fsqrt.{} {}, {}, dyn", fp_suffix(k), fpr(dst), fpr(r));
    Ok(())
}

/// `FAbs`/`FNeg` via sign injection.
fn e_fabsneg(
    ctx: &mut LowerCtx,
    mn: &str,
    k: FKind,
    dst: Fpr,
    src: &Op,
    negate: bool,
) -> Result<(), String> {
    let r = fp_src(ctx, mn, k, src)?;
    let op = if negate { "fsgnjn" } else { "fsgnjx" };
    ins!(
        ctx,
        "{}.{} {}, {}, {}",
        op,
        fp_suffix(k),
        fpr(dst),
        fpr(r),
        fpr(r)
    );
    Ok(())
}

/// `FBit`: `dst = dst AND/OR src` through GPRs (RISC-V has no integer ops
/// on FP registers).
fn e_fbit(
    ctx: &mut LowerCtx,
    mn: &str,
    or: bool,
    k: FKind,
    dst: Fpr,
    src: &Op,
) -> Result<(), String> {
    let r = fp_src(ctx, mn, k, src)?;
    let op = if or { "or" } else { "and" };
    match k {
        FKind::F64 => {
            ins!(ctx, "fmv.x.d {}, {}", gpr(G1), fpr(dst));
            ins!(ctx, "fmv.x.d {}, {}", gpr(G2), fpr(r));
            ins!(ctx, "{} {}, {}, {}", op, gpr(G1), gpr(G1), gpr(G2));
            ins!(ctx, "fmv.d.x {}, {}", fpr(dst), gpr(G1));
        }
        FKind::F32 => {
            ins!(ctx, "fmv.x.w {}, {}", gpr(G1), fpr(dst));
            ins!(ctx, "fmv.x.w {}, {}", gpr(G2), fpr(r));
            ins!(ctx, "{} {}, {}, {}", op, gpr(G1), gpr(G1), gpr(G2));
            ins!(ctx, "fmv.w.x {}, {}", fpr(dst), gpr(G1));
        }
    }
    Ok(())
}

/// `CvtFI`: truncating FP-to-int conversion with x86 saturation parity.
fn e_cvtfi(
    ctx: &mut LowerCtx,
    mn: &str,
    k: FKind,
    w: Width,
    dst: Gpr,
    src: &Op,
) -> Result<(), String> {
    let r = fp_src(ctx, mn, k, src)?;
    let sfx = fp_suffix(k);
    match w {
        Width::B32 => {
            ins!(ctx, "fcvt.w.{} {}, {}, rtz", sfx, gpr(dst), fpr(r));
            mov_imm(ctx, G1, i64::from(i32::MAX));
            let done = fresh(ctx);
            ins!(ctx, "bne {}, {}, {}", gpr(dst), gpr(G1), done);
            mov_imm(ctx, dst, i64::from(i32::MIN));
            bind(ctx, &done);
            zero_upper32(ctx, dst);
        }
        Width::B64 => {
            ins!(ctx, "fcvt.l.{} {}, {}, rtz", sfx, gpr(dst), fpr(r));
            mov_imm(ctx, G1, i64::MAX);
            let done = fresh(ctx);
            ins!(ctx, "bne {}, {}, {}", gpr(dst), gpr(G1), done);
            mov_imm(ctx, dst, i64::MIN);
            bind(ctx, &done);
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: float-to-int needs 32/64-bit widths",
                mn
            ));
        }
    }
    Ok(())
}

/// `CvtIF`: integer to float.
fn e_cvtif(
    ctx: &mut LowerCtx,
    mn: &str,
    signed: bool,
    from: Width,
    k: FKind,
    dst: Fpr,
    src: &Op,
) -> Result<(), String> {
    let s = load_op_gpr(ctx, mn, src, from, G1)?;
    // Sub-64 signed sides sign-extend first (loads zero-extend).
    let s = if signed {
        match from {
            Width::B64 | Width::B32 => s,
            Width::B8 => {
                ins!(ctx, "slli {}, {}, 56", gpr(G1), gpr(s));
                ins!(ctx, "srai {}, {}, 56", gpr(G1), gpr(G1));
                G1
            }
            Width::B16 => {
                ins!(ctx, "slli {}, {}, 48", gpr(G1), gpr(s));
                ins!(ctx, "srai {}, {}, 48", gpr(G1), gpr(G1));
                G1
            }
        }
    } else {
        s
    };
    let sfx = fp_suffix(k);
    let op = match (signed, matches!(from, Width::B64)) {
        (true, true) => format!("fcvt.{}.l", sfx),
        (true, false) => format!("fcvt.{}.w", sfx),
        (false, true) => format!("fcvt.{}.lu", sfx),
        (false, false) => format!("fcvt.{}.wu", sfx),
    };
    ins!(ctx, "{} {}, {}, dyn", op, fpr(dst), gpr(s));
    Ok(())
}

/// `CvtFF`: converts between `f32` and `f64`.
fn e_cvtff(
    ctx: &mut LowerCtx,
    mn: &str,
    from: FKind,
    to: FKind,
    dst: Fpr,
    src: &Op,
) -> Result<(), String> {
    let r = fp_src(ctx, mn, from, src)?;
    match (from, to) {
        (FKind::F32, FKind::F64) => {
            ins!(ctx, "fcvt.d.s {}, {}, dyn", fpr(dst), fpr(r));
        }
        (FKind::F64, FKind::F32) => {
            ins!(ctx, "fcvt.s.d {}, {}, dyn", fpr(dst), fpr(r));
        }
        _ => match src {
            Op::Fpr(f) => rv_fmov(ctx, to, dst, *f),
            _ => rv_fmov(ctx, to, dst, SF),
        },
    }
    Ok(())
}

/// `Bitcast` between GPR and FPR lanes.
fn e_bitcast(
    ctx: &mut LowerCtx,
    mn: &str,
    dir: BitcastDir,
    dst: &Op,
    src: &Op,
) -> Result<(), String> {
    match (dir, dst, src) {
        (BitcastDir::Q2D, Op::Fpr(d), Op::Gpr(s)) => {
            ins!(ctx, "fmv.d.x {}, {}", fpr(*d), gpr(*s));
        }
        (BitcastDir::D2Q, Op::Gpr(d), Op::Fpr(s)) => {
            ins!(ctx, "fmv.x.d {}, {}", gpr(*d), fpr(*s));
        }
        (BitcastDir::I2F, Op::Fpr(d), Op::Gpr(s)) => {
            ins!(ctx, "fmv.w.x {}, {}", fpr(*d), gpr(*s));
        }
        (BitcastDir::F2I, Op::Gpr(d), Op::Fpr(s)) => {
            ins!(ctx, "fmv.x.w {}, {}", gpr(*d), fpr(*s));
        }
        _ => {
            return Err(format!("riscv64: `{}`: unsupported bit-cast pair", mn));
        }
    }
    Ok(())
}

/// One `feq`/`flt`/`fle` into `dst`.
fn emit_fcmp(ctx: &mut LowerCtx, k: FKind, op: &str, dst: Gpr, l: Fpr, r: Fpr) {
    ins!(
        ctx,
        "{}.{} {}, {}, {}",
        op,
        fp_suffix(k),
        gpr(dst),
        fpr(l),
        fpr(r)
    );
}

/// Stages `fcmp` operands into FPRs. At most one side may spill.
fn fcmp_ops(
    ctx: &mut LowerCtx,
    mn: &str,
    k: FKind,
    lhs: &Op,
    rhs: &Op,
) -> Result<(Fpr, Fpr), String> {
    let spill = |op: &Op| !matches!(op, Op::Fpr(_));
    if spill(lhs) && spill(rhs) {
        return Err(format!(
            "riscv64: `{}`: float compare needs two live registers",
            mn
        ));
    }
    Ok((fp_src(ctx, mn, k, lhs)?, fp_src(ctx, mn, k, rhs)?))
}

/// `G2 = (operand is NaN)`.
fn emit_unordered_test(ctx: &mut LowerCtx, k: FKind, f: Fpr) {
    emit_fcmp(ctx, k, "feq", G2, f, f);
}

/// `BranchF`: float compare-and-branch.
#[allow(clippy::too_many_arguments)]
fn e_branchf(
    ctx: &mut LowerCtx,
    mn: &str,
    cc: FCc,
    k: FKind,
    lhs: &Op,
    rhs: &Op,
    target: &offlineasm_ir::Lbl,
    patch: bool,
) -> Result<(), String> {
    let t = text::label_text(ctx, *target)?;
    let unordered_either = |ctx: &mut LowerCtx, l: Fpr, r: Fpr| {
        emit_unordered_test(ctx, k, l);
        ins!(ctx, "beq {}, x0, {}", gpr(G2), t);
        emit_unordered_test(ctx, k, r);
        ins!(ctx, "beq {}, x0, {}", gpr(G2), t);
    };
    match cc {
        FCc::Eq => {
            let (l, r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
            emit_fcmp(ctx, k, "feq", G1, l, r);
            emit_cond_branch(ctx, false, G1, &t, patch);
        }
        FCc::Ne => {
            // Ordered not-equal: skip when either side is unordered, then
            // branch on inequality. Never patches (multi-branch).
            if patch {
                return Err(format!("riscv64: `{}`: not patchable", mn));
            }
            let (l, r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
            emit_fcmp(ctx, k, "feq", G1, l, l);
            let skip = fresh(ctx);
            ins!(ctx, "beq {}, x0, {}", gpr(G1), skip);
            emit_fcmp(ctx, k, "feq", G1, r, r);
            ins!(ctx, "beq {}, x0, {}", gpr(G1), skip);
            emit_fcmp(ctx, k, "feq", G1, l, r);
            ins!(ctx, "beq {}, x0, {}", gpr(G1), t);
            bind(ctx, &skip);
        }
        FCc::NeUn => {
            // `feq` writes 0 on unordered inputs, so one branch covers `NeUn`.
            let (l, r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
            emit_fcmp(ctx, k, "feq", G1, l, r);
            if patch {
                let skip = fresh(ctx);
                ins!(ctx, "bne {}, x0, {}", gpr(G1), skip);
                ins!(ctx, "j {}", t);
                bind(ctx, &skip);
                return Ok(());
            }
            ins!(ctx, "beq {}, x0, {}", gpr(G1), t);
        }
        FCc::Gt => {
            let (l, r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
            emit_fcmp(ctx, k, "flt", G1, r, l);
            emit_cond_branch(ctx, false, G1, &t, patch);
        }
        FCc::Ge => {
            let (l, r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
            emit_fcmp(ctx, k, "fle", G1, r, l);
            emit_cond_branch(ctx, false, G1, &t, patch);
        }
        FCc::Lt => {
            let (l, r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
            emit_fcmp(ctx, k, "flt", G1, l, r);
            emit_cond_branch(ctx, false, G1, &t, patch);
        }
        FCc::Le => {
            let (l, r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
            emit_fcmp(ctx, k, "fle", G1, l, r);
            emit_cond_branch(ctx, false, G1, &t, patch);
        }
        FCc::GtUn | FCc::LtUn => {
            if patch {
                return Err(format!("riscv64: `{}`: not patchable", mn));
            }
            let (l, r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
            emit_fcmp(ctx, k, "flt", G1, l, r);
            ins!(ctx, "bne {}, x0, {}", gpr(G1), t);
            unordered_either(ctx, l, r);
        }
        FCc::GeUn | FCc::LeUn => {
            if patch {
                return Err(format!("riscv64: `{}`: not patchable", mn));
            }
            let (l, r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
            emit_fcmp(ctx, k, "fle", G1, l, r);
            ins!(ctx, "bne {}, x0, {}", gpr(G1), t);
            unordered_either(ctx, l, r);
        }
        FCc::EqUn => {
            if patch {
                return Err(format!("riscv64: `{}`: not patchable", mn));
            }
            let (l, r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
            emit_fcmp(ctx, k, "feq", G1, l, r);
            ins!(ctx, "bne {}, x0, {}", gpr(G1), t);
            unordered_either(ctx, l, r);
        }
    }
    Ok(())
}

/// `FSet`: `dst = (lhs cc rhs)`.
fn e_fset(
    ctx: &mut LowerCtx,
    mn: &str,
    cc: FCc,
    k: FKind,
    dst: &Op,
    lhs: &Op,
    rhs: &Op,
) -> Result<(), String> {
    let (swap, negate, ordered_ne, op) = match cc {
        FCc::Eq => (false, false, false, "feq"),
        FCc::Ne => (false, false, true, "feq"),
        FCc::NeUn => (false, true, false, "feq"),
        FCc::Gt | FCc::Lt => (true, false, false, "flt"),
        FCc::Ge | FCc::Le => (true, false, false, "fle"),
        FCc::EqUn | FCc::GtUn | FCc::GeUn | FCc::LtUn | FCc::LeUn => {
            return Err(format!(
                "riscv64: `{}`: unordered set is only defined for eq/ne",
                mn
            ));
        }
    };
    let (mut l, mut r) = fcmp_ops(ctx, mn, k, lhs, rhs)?;
    if swap {
        std::mem::swap(&mut l, &mut r);
    }
    // The set value goes into scratch so a memory destination's store keeps
    // the address scratch free.
    emit_fcmp(ctx, k, op, G2, l, r);
    if ordered_ne {
        // `~eq & ordered(l) & ordered(r)`.
        emit_fcmp(ctx, k, "feq", G1, l, l);
        emit_fcmp(ctx, k, "feq", G2, r, r);
        ins!(ctx, "and {}, {}, {}", gpr(G1), gpr(G1), gpr(G2));
        emit_fcmp(ctx, k, "feq", G2, l, r);
        ins!(ctx, "xori {}, {}, 1", gpr(G2), gpr(G2));
        ins!(ctx, "and {}, {}, {}", gpr(G2), gpr(G2), gpr(G1));
    } else if negate {
        ins!(ctx, "xori {}, {}, 1", gpr(G2), gpr(G2));
    }
    match dst {
        Op::Gpr(d) => {
            mov_reg(ctx, *d, G2, Width::B64);
            Ok(())
        }
        Op::Mem(a) => e_store(ctx, mn, Width::B32, &Op::Gpr(G2), a),
        _ => Err(format!(
            "riscv64: `{}`: float set needs a register or memory destination",
            mn
        )),
    }
}

/// `FRound` via the 2^52 (2^23 for `F32`) exactness trick: values with
/// `|x| >= M` are already integral, so they take the fast path untouched.
fn e_fround(
    ctx: &mut LowerCtx,
    mn: &str,
    k: FKind,
    mode: RoundMode,
    dst: Fpr,
    src: &Op,
) -> Result<(), String> {
    let r = fp_src(ctx, mn, k, src)?;
    let d = fpr(dst);
    let s = fpr(SF);
    let sfx = fp_suffix(k);
    let (mbits, onebits) = match k {
        FKind::F64 => (
            0x4330_0000_0000_0000u64 as i64,
            0x3FF0_0000_0000_0000u64 as i64,
        ),
        FKind::F32 => (0x4B00_0000u64 as i64, 0x3F80_0000u64 as i64),
    };
    // Park the input bits in the second scratch GPR. `r` may be the scratch
    // FPR, which `s` reuses below.
    match k {
        FKind::F64 => ins!(ctx, "fmv.x.d {}, {}", gpr(G2), fpr(r)),
        FKind::F32 => ins!(ctx, "fmv.x.w {}, {}", gpr(G2), fpr(r)),
    }
    // `d = |x|` (also the `|x| >= M` check input).
    ins!(ctx, "fsgnjx.{} {}, {}, {}", sfx, d, fpr(r), fpr(r));
    // `s = M` (the exactness bound).
    mov_imm(ctx, G1, mbits);
    match k {
        FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", s, gpr(G1)),
        FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", s, gpr(G1)),
    }
    let done = fresh(ctx);
    ins!(ctx, "fle.{} {}, {}, {}", sfx, gpr(G1), s, d);
    let fast = fresh(ctx);
    ins!(ctx, "beq {}, x0, {}", gpr(G1), fast);
    // Fast path: `|x| >= M` means `x` is already integral. Restore the
    // signed original into `d`.
    match k {
        FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", d, gpr(G2)),
        FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", d, gpr(G2)),
    }
    ins!(ctx, "j {}", done);
    bind(ctx, &fast);
    match mode {
        RoundMode::Nearest => {
            // `m = copysign(M, x); d = x + m - m`.
            match k {
                FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", d, gpr(G2)),
                FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", d, gpr(G2)),
            }
            ins!(ctx, "fsgnj.{} {}, {}, {}", sfx, s, s, d);
            ins!(ctx, "fadd.{} {}, {}, {}, dyn", sfx, d, d, s);
            ins!(ctx, "fsub.{} {}, {}, {}, dyn", sfx, d, d, s);
        }
        RoundMode::Trunc => {
            // `d = (|x| + M) - M` (= nearest, exact).
            ins!(ctx, "fadd.{} {}, {}, {}, dyn", sfx, d, d, s);
            ins!(ctx, "fsub.{} {}, {}, {}, dyn", sfx, d, d, s);
            // Pull toward zero when the nearest integer overshot the
            // magnitude (`|x| < d`), then apply the sign of `x`.
            match k {
                FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", s, gpr(G2)),
                FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", s, gpr(G2)),
            }
            ins!(ctx, "fsgnjx.{} {}, {}, {}", sfx, s, s, s);
            ins!(ctx, "flt.{} {}, {}, {}", sfx, gpr(G1), s, d);
            match k {
                FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", s, gpr(G2)),
                FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", s, gpr(G2)),
            }
            ins!(ctx, "fsgnj.{} {}, {}, {}", sfx, d, d, s);
            mov_imm(ctx, G2, onebits);
            match k {
                FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", s, gpr(G2)),
                FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", s, gpr(G2)),
            }
            // `s = copysign(1.0, d)`: subtracting it moves `d` toward zero
            // for either sign.
            ins!(ctx, "fsgnj.{} {}, {}, {}", sfx, s, s, d);
            let no_adj = fresh(ctx);
            ins!(ctx, "beq {}, x0, {}", gpr(G1), no_adj);
            ins!(ctx, "fsub.{} {}, {}, {}, dyn", sfx, d, d, s);
            bind(ctx, &no_adj);
        }
        RoundMode::Down | RoundMode::Up => {
            // `d = (|x| + M) - M`, sign applied. Then step toward -/+inf
            // when `d` is not already `x`.
            ins!(ctx, "fadd.{} {}, {}, {}, dyn", sfx, d, d, s);
            ins!(ctx, "fsub.{} {}, {}, {}, dyn", sfx, d, d, s);
            match k {
                FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", s, gpr(G2)),
                FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", s, gpr(G2)),
            }
            ins!(ctx, "fsgnj.{} {}, {}, {}", sfx, d, d, s);
            // Down adjusts iff `x < d`. Up adjusts iff `d < x`.
            if mode == RoundMode::Down {
                ins!(ctx, "flt.{} {}, {}, {}", sfx, gpr(G1), s, d);
            } else {
                ins!(ctx, "flt.{} {}, {}, {}", sfx, gpr(G1), d, s);
            }
            mov_imm(ctx, G2, onebits);
            match k {
                FKind::F64 => ins!(ctx, "fmv.d.x {}, {}", s, gpr(G2)),
                FKind::F32 => ins!(ctx, "fmv.w.x {}, {}", s, gpr(G2)),
            }
            let no_adj = fresh(ctx);
            ins!(ctx, "beq {}, x0, {}", gpr(G1), no_adj);
            if mode == RoundMode::Down {
                ins!(ctx, "fsub.{} {}, {}, {}, dyn", sfx, d, d, s);
            } else {
                ins!(ctx, "fadd.{} {}, {}, {}, dyn", sfx, d, d, s);
            }
            bind(ctx, &no_adj);
        }
    }
    bind(ctx, &done);
    Ok(())
}

/// TLS: the thread pointer lives in `x4` (`tp`), read directly with no
/// system-register access.
///
/// Sub-word loads zero-extend (`lbu`/`lhu`/`lwu`), matching `loadb`/
/// `loadh`/`loadi`; sub-word stores write only the slot's low bytes.
fn e_tls(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    reg: Gpr,
    idx: i64,
    load: bool,
) -> Result<(), String> {
    let off = idx
        .checked_mul(8)
        .ok_or_else(|| format!("riscv64: `{}`: tls index overflow", mn))?;
    let direct = i32::try_from(off).is_ok_and(fits_d12);
    if load {
        let op = load_mnemonic(w, Sx::Zero);
        if direct {
            ins!(ctx, "{} {}, {}(x4)", op, gpr(reg), off);
        } else {
            mov_imm(ctx, G1, off);
            ins!(ctx, "add {}, {}, x4", gpr(G1), gpr(G1));
            ins!(ctx, "{} {}, 0(x{})", op, gpr(reg), G1.0);
        }
    } else if direct {
        ins!(ctx, "{} {}, {}(x4)", store_mnemonic(w), gpr(reg), off);
    } else {
        // Stash the value in the FP bucket while base + off folds.
        ins!(ctx, "fmv.d.x {}, {}", fpr(SF), gpr(reg));
        mov_imm(ctx, G1, off);
        ins!(ctx, "add {}, {}, x4", gpr(G1), gpr(G1));
        ins!(ctx, "fmv.x.d {}, {}", gpr(G2), fpr(SF));
        ins!(ctx, "{} {}, 0(x{})", store_mnemonic(w), gpr(G2), G1.0);
    }
    Ok(())
}

/// `tls_leap`: the address of the thread-local slot at `idx`.
fn e_tls_lea(ctx: &mut LowerCtx, mn: &str, reg: Gpr, idx: i64) -> Result<(), String> {
    let off = idx
        .checked_mul(8)
        .ok_or_else(|| format!("riscv64: `{}`: tls index overflow", mn))?;
    if off == 0 {
        if reg != TP {
            ins!(ctx, "addi {}, x4, 0", gpr(reg));
        }
    } else if i32::try_from(off).is_ok_and(fits_d12) {
        ins!(ctx, "addi {}, x4, {}", gpr(reg), off);
    } else {
        mov_imm(ctx, G1, off);
        ins!(ctx, "add {}, {}, x4", gpr(reg), gpr(G1));
    }
    Ok(())
}

/// Mask a lane in place (`andi` only fits the byte mask).
fn mask_lane(ctx: &mut LowerCtx, w: Width, r: Gpr) {
    if w == Width::B8 {
        ins!(ctx, "andi {}, {}, 255", gpr(r), gpr(r));
    } else {
        ins!(ctx, "slli {}, {}, 48", gpr(r), gpr(r));
        ins!(ctx, "srli {}, {}, 48", gpr(r), gpr(r));
    }
}

/// Atomic read-modify-write / exchange. `B32`/`B64` use native AMOs
/// (acquire-release). Sub-word widths loop `lr.w`/`sc.w` over the
/// containing word. The old value is written to `reg` (zero-extended for
/// sub-word widths).
fn e_rmw(
    ctx: &mut LowerCtx,
    mn: &str,
    op: AtomicOp,
    w: Width,
    a: &Op,
    b: &Op,
) -> Result<(), String> {
    let (mem, reg) = match (a, b) {
        (Op::Mem(m), Op::Gpr(r)) => (*m, *r),
        (Op::Gpr(r), Op::Mem(m)) => (*m, *r),
        _ => {
            return Err(format!(
                "riscv64: `{}`: atomic r/m needs one memory and one register operand",
                mn
            ));
        }
    };
    match w {
        Width::B32 | Width::B64 => {
            // The value register may be the expansion scratch register
            // (`atomicxchgclear*` complements its source there), which is
            // also the address temp: stage it before the address folds.
            let staged = reg == G1;
            if staged {
                ins!(ctx, "mv {}, {}", gpr(G2), gpr(reg));
            }
            addr_scratch(ctx, mn, &mem, G1)?;
            let (addr, val) = (gpr(G1), if staged { gpr(G2) } else { gpr(reg) });
            // `Sub` negates the addend in place, then adds.
            if op == AtomicOp::Sub {
                if w == Width::B64 {
                    ins!(ctx, "sub {}, x0, {}", val, val);
                } else {
                    ins!(ctx, "subw {}, x0, {}", val, val);
                }
            }
            let name = match op {
                AtomicOp::Add | AtomicOp::Sub => "amoadd",
                AtomicOp::Xchg => "amoswap",
                AtomicOp::And => "amoand",
                AtomicOp::Or => "amoor",
                AtomicOp::Xor => "amoxor",
            };
            let sfx = if w == Width::B32 { "w" } else { "d" };
            ins!(ctx, "{}.{}.aqrl {}, {}, ({})", name, sfx, val, val, addr);
            // The AMO leaves the old value in `val`. The IR puts it in
            // `reg`, so copy back when we staged the operand aside.
            if staged {
                ins!(ctx, "mv {}, {}", gpr(reg), gpr(G2));
            }
            Ok(())
        }
        Width::B8 | Width::B16 => {
            // Sub-word loop over the containing word. The aligned address
            // pins `G2` and everything else shares `FLAGS`/`G1` plus a
            // 32-byte frame: `[sp+0]` shift (loop invariant), `[sp+8]` the
            // parked source value, `[sp+16]` old word, `[sp+24]` staged new
            // lane.
            //
            // The source register is *not* used as a temp: `expand` routes
            // the complemented source of `atomicxchgclear*` through `G1`,
            // so `reg` may be `G1` itself rather than a user register.
            let lanemask: i64 = if w == Width::B8 { 0xFF } else { 0xFFFF };
            if reg == G2 {
                return Err(format!(
                    "riscv64: `{}`: atomic r/m needs a free scratch register",
                    mn
                ));
            }
            ins!(ctx, "addi x2, x2, -32");
            // Park the value before the address folds: `reg` is free from
            // here on, even when it aliases the address temp.
            ins!(ctx, "sd {}, 8(x2)", gpr(reg));
            addr_scratch(ctx, mn, &mem, G2)?;
            ins!(ctx, "andi {}, {}, 3", gpr(G1), gpr(G2));
            ins!(ctx, "slli {}, {}, 3", gpr(G1), gpr(G1));
            ins!(ctx, "sd {}, 0(x2)", gpr(G1));
            ins!(ctx, "andi {}, {}, -4", gpr(G2), gpr(G2));
            let again = fresh(ctx);
            bind(ctx, &again);
            ins!(ctx, "lr.w.aq {}, ({})", gpr(FLAGS), gpr(G2));
            ins!(ctx, "sd {}, 16(x2)", gpr(FLAGS));
            ins!(ctx, "ld {}, 0(x2)", gpr(G1));
            if op == AtomicOp::Xchg {
                ins!(ctx, "ld {}, 8(x2)", gpr(FLAGS));
                mask_lane(ctx, w, FLAGS);
                ins!(ctx, "sll {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G1));
                ins!(ctx, "sd {}, 24(x2)", gpr(FLAGS));
            } else {
                ins!(ctx, "srl {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G1));
                mask_lane(ctx, w, FLAGS);
                ins!(ctx, "ld {}, 8(x2)", gpr(G1));
                let arith = match op {
                    AtomicOp::Add => "add",
                    AtomicOp::Sub => "sub",
                    AtomicOp::Or => "or",
                    AtomicOp::Xor => "xor",
                    AtomicOp::And => "and",
                    AtomicOp::Xchg => "add",
                };
                ins!(ctx, "{} {}, {}, {}", arith, gpr(FLAGS), gpr(FLAGS), gpr(G1));
                mask_lane(ctx, w, FLAGS);
                ins!(ctx, "ld {}, 0(x2)", gpr(G1));
                ins!(ctx, "sll {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G1));
                ins!(ctx, "sd {}, 24(x2)", gpr(FLAGS));
            }
            // `m = mask << shift`, `new = (old & ~m) | staged`.
            mov_imm(ctx, FLAGS, lanemask);
            ins!(ctx, "sll {}, {}, {}", gpr(G1), gpr(FLAGS), gpr(G1));
            ins!(ctx, "xori {}, {}, -1", gpr(G1), gpr(G1));
            ins!(ctx, "ld {}, 16(x2)", gpr(FLAGS));
            ins!(ctx, "and {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G1));
            ins!(ctx, "ld {}, 24(x2)", gpr(G1));
            ins!(ctx, "or {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G1));
            // `sc.<w> rd, rs2, (rs1)`: the address is `rs1`, the stored word
            // is `rs2`.
            ins!(ctx, "sc.w.rl {}, {}, ({})", gpr(G1), gpr(FLAGS), gpr(G2));
            ins!(ctx, "bne {}, x0, {}", gpr(G1), again);
            // Old lane value (zero-extended) back into `reg`.
            // `G2` is free here (the loop is over) and `reg` must not be
            // used as its own shift temp.
            ins!(ctx, "ld {}, 0(x2)", gpr(G2));
            ins!(ctx, "ld {}, 16(x2)", gpr(reg));
            ins!(ctx, "srl {}, {}, {}", gpr(reg), gpr(reg), gpr(G2));
            mask_lane(ctx, w, reg);
            ins!(ctx, "addi x2, x2, 32");
            Ok(())
        }
    }
}

/// Leave the observed old lane in `dst` (x86 `cmpxchg`-over-`t0` parity).
fn emit_cas_old_value(ctx: &mut LowerCtx, w: Width, dst: Gpr) {
    match w {
        Width::B64 => mov_reg(ctx, dst, FLAGS, Width::B64),
        Width::B32 => {
            ins!(ctx, "slli {}, {}, 32", gpr(dst), gpr(FLAGS));
            ins!(ctx, "srli {}, {}, 32", gpr(dst), gpr(dst));
        }
        _ => {
            ins!(ctx, "ld {}, 16(x2)", gpr(dst));
            ins!(ctx, "ld {}, 0(x2)", gpr(G2));
            ins!(ctx, "srl {}, {}, {}", gpr(dst), gpr(dst), gpr(G2));
            mask_lane(ctx, w, dst);
        }
    }
}

/// `AtomicCas` with the expected value in the `t0` role. The weak
/// (`branch`) form jumps when the exchange fails.
fn e_cas(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    mem: &Mem,
    src: Gpr,
    branch: Option<&offlineasm_ir::Lbl>,
    patch: bool,
) -> Result<(), String> {
    let _ = patch;
    addr_scratch(ctx, mn, mem, G1)?;
    let again = fresh(ctx);
    let fail = fresh(ctx);
    let done = fresh(ctx);
    let subword = w == Width::B8 || w == Width::B16;
    let lanemask: i64 = if w == Width::B8 { 0xFF } else { 0xFFFF };
    if subword {
        ins!(ctx, "addi x2, x2, -32");
        ins!(ctx, "sd {}, 8(x2)", gpr(src));
        ins!(ctx, "andi {}, {}, 3", gpr(G2), gpr(G1));
        ins!(ctx, "slli {}, {}, 3", gpr(G2), gpr(G2));
        ins!(ctx, "sd {}, 0(x2)", gpr(G2));
        ins!(ctx, "andi {}, {}, -4", gpr(G1), gpr(G1));
    }
    bind(ctx, &again);
    match w {
        Width::B64 => ins!(ctx, "lr.d.aq {}, ({})", gpr(FLAGS), gpr(G1)),
        _ => ins!(ctx, "lr.w.aq {}, ({})", gpr(FLAGS), gpr(G1)),
    }
    if subword {
        ins!(ctx, "sd {}, 16(x2)", gpr(FLAGS));
    }
    // Compare (never mutating `t0` before `fail`).
    if w == Width::B64 {
        ins!(ctx, "bne {}, {}, {}", gpr(FLAGS), gpr(T0), fail);
    } else if w == Width::B32 {
        // Low-word equality via the masked difference.
        ins!(ctx, "slli {}, {}, 32", gpr(G2), gpr(FLAGS));
        ins!(ctx, "srli {}, {}, 32", gpr(G2), gpr(G2));
        ins!(ctx, "sub {}, {}, {}", gpr(G2), gpr(G2), gpr(T0));
        ins!(ctx, "slli {}, {}, 32", gpr(G2), gpr(G2));
        ins!(ctx, "srli {}, {}, 32", gpr(G2), gpr(G2));
        ins!(ctx, "bne {}, x0, {}", gpr(G2), fail);
    } else {
        // Lane equality via the masked shifted difference.
        ins!(ctx, "ld {}, 0(x2)", gpr(G2));
        ins!(ctx, "srl {}, {}, {}", gpr(G2), gpr(FLAGS), gpr(G2));
        ins!(ctx, "srl {}, {}, {}", gpr(FLAGS), gpr(T0), gpr(G2));
        ins!(ctx, "sub {}, {}, {}", gpr(G2), gpr(G2), gpr(FLAGS));
        mask_lane(ctx, w, G2);
        ins!(ctx, "bne {}, x0, {}", gpr(G2), fail);
        ins!(ctx, "ld {}, 16(x2)", gpr(FLAGS));
    }
    // Match: build the new word and store.
    if subword {
        ins!(ctx, "ld {}, 0(x2)", gpr(G2));
        ins!(ctx, "ld {}, 8(x2)", gpr(FLAGS));
        mask_lane(ctx, w, FLAGS);
        ins!(ctx, "sll {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G2));
        ins!(ctx, "sd {}, 8(x2)", gpr(FLAGS));
        mov_imm(ctx, FLAGS, lanemask);
        ins!(ctx, "sll {}, {}, {}", gpr(G2), gpr(FLAGS), gpr(G2));
        ins!(ctx, "xori {}, {}, -1", gpr(G2), gpr(G2));
        ins!(ctx, "ld {}, 16(x2)", gpr(FLAGS));
        ins!(ctx, "and {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G2));
        ins!(ctx, "ld {}, 8(x2)", gpr(G2));
        ins!(ctx, "or {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G2));
    }
    match w {
        // `sc.<w> rd, rs2, (rs1)`: `G1` holds the address, the second source
        // is the word to store.
        Width::B32 => ins!(ctx, "sc.w.rl {}, {}, ({})", gpr(G2), gpr(src), gpr(G1)),
        Width::B64 => ins!(ctx, "sc.d.rl {}, {}, ({})", gpr(G2), gpr(src), gpr(G1)),
        _ => ins!(ctx, "sc.w.rl {}, {}, ({})", gpr(G2), gpr(FLAGS), gpr(G1)),
    }
    ins!(ctx, "bne {}, x0, {}", gpr(G2), again);
    // Success: `t0` reads the old lane.
    emit_cas_old_value(ctx, w, T0);
    ins!(ctx, "j {}", done);
    bind(ctx, &fail);
    // Failure: `t0` reads the old lane (same shapes).
    emit_cas_old_value(ctx, w, T0);
    if let Some(target) = branch {
        let t = text::label_text(ctx, *target)?;
        ins!(ctx, "j {}", t);
    }
    bind(ctx, &done);
    if subword {
        ins!(ctx, "addi x2, x2, 32");
    }
    Ok(())
}

/// Exclusive load (`lr.w`/`lr.d`, acquire).
fn e_loadlinked(ctx: &mut LowerCtx, mn: &str, w: Width, mem: &Mem, dst: Gpr) -> Result<(), String> {
    addr_scratch(ctx, mn, mem, G1)?;
    match w {
        Width::B32 => ins!(ctx, "lr.w.aq {}, ({})", gpr(dst), gpr(G1)),
        Width::B64 => ins!(ctx, "lr.d.aq {}, ({})", gpr(dst), gpr(G1)),
        // Sub-word: the reservation covers the word. Extract the lane
        // zero-extended (the store-conditional side merges it back).
        Width::B8 | Width::B16 => {
            let sh = if w == Width::B8 { 3 } else { 4 };
            mov_reg(ctx, G2, G1, Width::B64);
            ins!(ctx, "andi {}, {}, 3", gpr(G2), gpr(G2));
            ins!(ctx, "slli {}, {}, {}", gpr(G2), gpr(G2), sh);
            ins!(ctx, "andi {}, {}, -4", gpr(dst), gpr(G1));
            ins!(ctx, "lr.w.aq {}, ({})", gpr(dst), gpr(dst));
            ins!(ctx, "srl {}, {}, {}", gpr(dst), gpr(dst), gpr(G2));
            mask_lane(ctx, w, dst);
        }
    }
    Ok(())
}

/// Exclusive store (`sc.w`/`sc.d`, release): status 0/1 in `status`.
fn e_storecond(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    status: Gpr,
    src: Gpr,
    mem: &Mem,
) -> Result<(), String> {
    addr_scratch(ctx, mn, mem, G1)?;
    match w {
        // `sc.<w> rd, rs2, (rs1)`: the address is `rs1`.
        Width::B32 => ins!(ctx, "sc.w.rl {}, {}, ({})", gpr(status), gpr(src), gpr(G1)),
        Width::B64 => ins!(ctx, "sc.d.rl {}, {}, ({})", gpr(status), gpr(src), gpr(G1)),
        Width::B8 | Width::B16 => {
            // Lane merge with retry.
            let lanemask: i64 = if w == Width::B8 { 0xFF } else { 0xFFFF };
            ins!(ctx, "addi x2, x2, -32");
            ins!(ctx, "sd {}, 8(x2)", gpr(src));
            ins!(ctx, "andi {}, {}, 3", gpr(status), gpr(G1));
            ins!(
                ctx,
                "slli {}, {}, {}",
                gpr(status),
                gpr(status),
                if w == Width::B8 { 3 } else { 4 }
            );
            ins!(ctx, "sd {}, 0(x2)", gpr(status));
            ins!(ctx, "andi {}, {}, -4", gpr(G1), gpr(G1));
            let again = fresh(ctx);
            bind(ctx, &again);
            ins!(ctx, "lr.w.aq {}, ({})", gpr(FLAGS), gpr(G1));
            // `new_lane = src & mask`, shifted into place.
            ins!(ctx, "ld {}, 8(x2)", gpr(status));
            mask_lane(ctx, w, status);
            ins!(ctx, "ld {}, 0(x2)", gpr(G2));
            ins!(ctx, "sll {}, {}, {}", gpr(status), gpr(status), gpr(G2));
            // `m = mask << shift`, `new = (old & ~m) | new_lane`.
            mov_imm(ctx, G2, lanemask);
            ins!(ctx, "ld {}, 0(x2)", gpr(src));
            ins!(ctx, "sll {}, {}, {}", gpr(G2), gpr(G2), gpr(src));
            ins!(ctx, "xori {}, {}, -1", gpr(G2), gpr(G2));
            ins!(ctx, "and {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G2));
            ins!(ctx, "or {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(status));
            ins!(
                ctx,
                "sc.w.rl {}, {}, ({})",
                gpr(status),
                gpr(FLAGS),
                gpr(G1)
            );
            ins!(ctx, "bne {}, x0, {}", gpr(status), again);
            ins!(ctx, "addi x2, x2, 32");
        }
    }
    Ok(())
}

/// Paired loads/stores (no `ldp` on RISC-V: two `ld`/`sd`).
fn e_pair(
    ctx: &mut LowerCtx,
    mn: &str,
    w: PairW,
    first: &Op,
    second: &Op,
    mem: &Mem,
    load: bool,
) -> Result<(), String> {
    let scale: i64 = match w {
        PairW::B32 => 4,
        PairW::B64 => 8,
        PairW::F64 => 8,
        PairW::V128 => 16,
    };
    let direct = mem.index.is_none()
        && mem.base.is_some()
        && fits_d12(mem.disp.const_or_zero())
        && fits_d12(mem.disp.const_or_zero().wrapping_add(scale as i32));
    let (breg, d0): (Gpr, i64) = if direct {
        (mem.base_reg(), mem.disp.const_or_zero() as i64)
    } else {
        addr_scratch(ctx, mn, mem, G1)?;
        (G1, 0)
    };
    let b = gpr(breg);
    let off2 = d0 + scale;
    if load {
        match (first, second) {
            (Op::Gpr(a), Op::Gpr(bb)) => match w {
                // `lw` sign-extends; `loadpairi`'s 32-bit halves are
                // zero-extended, matching `loadi` and the x64/text-x86
                // `loadpairi` lowerings.
                PairW::B32 => {
                    if *a == breg {
                        ins!(ctx, "lwu {}, {}({})", gpr(*bb), off2, b);
                        if *a != *bb {
                            ins!(ctx, "lwu {}, {}({})", gpr(*a), d0, b);
                        }
                    } else {
                        ins!(ctx, "lwu {}, {}({})", gpr(*a), d0, b);
                        ins!(ctx, "lwu {}, {}({})", gpr(*bb), off2, b);
                    }
                }
                PairW::B64 => {
                    // `breg` is the address's own base register in the
                    // `direct` case. If the first destination aliases it,
                    // loading into it first clobbers the address before the
                    // second half's load reads it. When `*a == *bb` the high
                    // half (`*bb`, loaded second) survives, so the low-half
                    // write into `*a` is skipped.
                    if *a == breg {
                        ins!(ctx, "ld {}, {}({})", gpr(*bb), off2, b);
                        if *a != *bb {
                            ins!(ctx, "ld {}, {}({})", gpr(*a), d0, b);
                        }
                    } else {
                        ins!(ctx, "ld {}, {}({})", gpr(*a), d0, b);
                        ins!(ctx, "ld {}, {}({})", gpr(*bb), off2, b);
                    }
                }
                _ => {
                    return Err(format!(
                        "riscv64: `{}`: integer pair needs 32/64-bit width",
                        mn
                    ));
                }
            },
            (Op::Fpr(a), Op::Fpr(bb)) if w == PairW::F64 => {
                ins!(ctx, "fld {}, {}({})", fpr(*a), d0, b);
                ins!(ctx, "fld {}, {}({})", fpr(*bb), off2, b);
            }
            (Op::Fpr(a), Op::Fpr(bb)) if w == PairW::V128 => {
                let hi = d0 + 16;
                if !fits_d12(d0 as i32) || !fits_d12(hi as i32) {
                    return Err(format!("riscv64: `{}`: pair address overflow", mn));
                }
                let ma = Mem {
                    base: Some(breg),
                    index: None,
                    disp: Disp::Const(d0 as i32),
                };
                let mb = Mem {
                    base: Some(breg),
                    index: None,
                    disp: Disp::Const(hi as i32),
                };
                e_loadv(ctx, mn, *a, &ma)?;
                e_loadv(ctx, mn, *bb, &mb)?;
            }
            _ => {
                return Err(format!(
                    "riscv64: `{}`: pair load needs two GPRs (or two FPRs for fp pairs)",
                    mn
                ));
            }
        }
        return Ok(());
    }
    match (first, second) {
        (Op::Gpr(a), Op::Gpr(bb)) => match w {
            PairW::B32 => {
                ins!(ctx, "sw {}, {}({})", gpr(*a), d0, b);
                ins!(ctx, "sw {}, {}({})", gpr(*bb), off2, b);
            }
            PairW::B64 => {
                ins!(ctx, "sd {}, {}({})", gpr(*a), d0, b);
                ins!(ctx, "sd {}, {}({})", gpr(*bb), off2, b);
            }
            _ => {
                return Err(format!(
                    "riscv64: `{}`: integer pair needs 32/64-bit width",
                    mn
                ));
            }
        },
        (Op::Fpr(a), Op::Fpr(bb)) if w == PairW::F64 => {
            ins!(ctx, "fsd {}, {}({})", fpr(*a), d0, b);
            ins!(ctx, "fsd {}, {}({})", fpr(*bb), off2, b);
        }
        (Op::Fpr(a), Op::Fpr(bb)) if w == PairW::V128 => {
            let hi = d0 + 16;
            if !fits_d12(d0 as i32) || !fits_d12(hi as i32) {
                return Err(format!("riscv64: `{}`: pair address overflow", mn));
            }
            let ma = Mem {
                base: Some(breg),
                index: None,
                disp: Disp::Const(d0 as i32),
            };
            let mb = Mem {
                base: Some(breg),
                index: None,
                disp: Disp::Const(hi as i32),
            };
            e_storev(ctx, mn, *a, &ma)?;
            e_storev(ctx, mn, *bb, &mb)?;
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: pair store needs two GPRs (or two FPRs for fp pairs)",
                mn
            ));
        }
    }
    Ok(())
}

//
// Dispatch.
//

/// Prints one instruction.
///
/// # Errors
///
/// Returns an error if `inst` uses an operand or width combination the
/// RISC-V 64 printer does not support.
pub fn emit(ctx: &mut LowerCtx, inst: &Inst) -> Result<(), String> {
    let mn = "riscv64";
    match inst {
        Inst::Mov { w, dst, src, patch } => e_mov(ctx, mn, *w, dst, src, *patch),
        Inst::Bind(l) => {
            let name = text::label_text(ctx, *l)?;
            bind(ctx, &name);
            Ok(())
        }
        Inst::MovZero32 { dst, src } => e_movzero32(ctx, mn, dst, src),
        Inst::Bswap { w, dst, src } => e_bswap(ctx, mn, *w, dst, src),
        Inst::Load {
            w,
            sx,
            dst,
            addr,
            acquire,
        } => {
            e_load(ctx, mn, *w, *sx, *dst, addr)?;
            if *acquire {
                // RVWMO acquire-load idiom: the load itself, then a
                // `fence r, rw` (the same barrier `Inst::Fence { full:
                // false }` prints); `lint:missing-acquire` looks for
                // exactly this `fence` mnemonic after the load.
                ins!(ctx, "fence r, rw");
            }
            Ok(())
        }
        Inst::Store { w, src, addr } => e_store(ctx, mn, *w, src, addr),
        Inst::LoadF { k, dst, addr } => e_loadf(ctx, mn, *k, *dst, addr),
        Inst::StoreF { k, src, addr } => e_storef(ctx, mn, *k, *src, addr),
        Inst::FMov { k, dst, src } => {
            rv_fmov(ctx, *k, *dst, *src);
            Ok(())
        }
        Inst::LoadV { dst, addr } => e_loadv(ctx, mn, *dst, addr),
        Inst::StoreV { src, addr } => e_storev(ctx, mn, *src, addr),
        Inst::VMov { dst, src } => e_vmov(ctx, *dst, *src),
        Inst::Lea { w, dst, src } => e_lea(ctx, mn, *w, *dst, src),
        Inst::Push { op } => e_push_pop(ctx, mn, op, true),
        Inst::Pop { op } => e_push_pop(ctx, mn, op, false),
        Inst::PushV { src } => e_push_pop_v(ctx, mn, &Op::Fpr(*src), true),
        Inst::PopV { dst } => e_push_pop_v(ctx, mn, &Op::Fpr(*dst), false),
        Inst::Peek { disp, dst } => {
            e_peek_poke(ctx, *disp, *dst, true);
            Ok(())
        }
        Inst::Poke { disp, src } => {
            e_peek_poke(ctx, *disp, *src, false);
            Ok(())
        }
        Inst::Add { w, op } => op_n(ctx, mn, AluKind::Add, *w, &alu_args(op)),
        Inst::Sub { w, op } => op_n(ctx, mn, AluKind::Sub, *w, &alu_args(op)),
        Inst::Mul { w, op } => op_n(ctx, mn, AluKind::Mul, *w, &alu_args(op)),
        Inst::And { w, op } => op_n(ctx, mn, AluKind::And, *w, &alu_args(op)),
        Inst::Or { w, op } => op_n(ctx, mn, AluKind::Or, *w, &alu_args(op)),
        Inst::Xor { w, op } => op_n(ctx, mn, AluKind::Xor, *w, &alu_args(op)),
        Inst::Not { w, dst } => e_not_neg(ctx, mn, *w, dst, false),
        Inst::Neg { w, dst } => e_not_neg(ctx, mn, *w, dst, true),
        Inst::Shift { w, op, dst, cnt } => e_shift(ctx, mn, *w, *op, *dst, cnt),
        Inst::MulImm { w, dst, lhs, imm } => e_mulimm(ctx, mn, *w, *dst, *lhs, *imm),
        Inst::AluS { op, w, alu } => e_alus(ctx, mn, *op, *w, alu),
        Inst::Adc { dst, src } => e_adc_sbb(ctx, mn, dst, src, false),
        Inst::Sbb { dst, src } => e_adc_sbb(ctx, mn, dst, src, true),
        Inst::MulWide {
            signed,
            dst,
            lhs,
            rhs,
        } => e_mulwide(ctx, *signed, *dst, *lhs, *rhs),
        Inst::MulHigh { signed, rhs } => e_mulhigh(ctx, mn, *signed, rhs),
        Inst::DivMod1 { signed, w, divisor } => e_divmod1(ctx, mn, *signed, *w, divisor),
        Inst::Div3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        } => e_div(ctx, mn, *w, *signed, true, *dst, dvd, dvs),
        Inst::Rem3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        } => e_div(ctx, mn, *w, *signed, false, *dst, dvd, dvs),
        Inst::Extend {
            from,
            to,
            sx,
            dst,
            src,
        } => e_extend(ctx, mn, *from, *to, *sx, *dst, src),
        Inst::Ctz { w, dst, src } => e_ctz(ctx, mn, *w, *dst, src),
        Inst::Clz { w, dst, src } => e_clz(ctx, mn, *w, *dst, src),
        Inst::Popcnt { w, dst, src } => e_popcnt(ctx, mn, *w, *dst, src),
        Inst::Cqo { quad } => {
            e_cqo(ctx, *quad);
            Ok(())
        }
        Inst::AddShifted {
            dst,
            lhs,
            rhs,
            amount,
        } => e_addshifted(ctx, mn, *dst, *lhs, *rhs, *amount),
        Inst::Cmov {
            w,
            zero,
            dst,
            src,
            test,
        } => e_cmov(ctx, mn, *w, *zero, *dst, src, *test),
        Inst::VecExtract { w, dst, src, lane } => e_vecextract(ctx, mn, *w, *dst, *src, *lane),
        Inst::Branch {
            cc,
            w,
            lhs,
            rhs,
            target,
            patch,
        } => e_branch(ctx, mn, *cc, *w, lhs, rhs, target, *patch),
        Inst::TestBranch {
            w,
            value,
            mask,
            test,
            target,
            patch,
        } => e_testbranch(ctx, mn, *w, value, mask.as_ref(), *test, target, *patch),
        Inst::OpBranch {
            op,
            w,
            flag,
            args,
            target,
            patch,
        } => e_opbranch(ctx, mn, *op, *w, *flag, args.as_slice(), target, *patch),
        Inst::FlagBranch {
            flag,
            target,
            patch,
        } => e_flagbranch(ctx, *flag, target, *patch),
        Inst::Jump { target, patch } => e_jmp_call(ctx, mn, target, *patch, false),
        Inst::Call { target, patch } => e_jmp_call(ctx, mn, target, *patch, true),
        Inst::Ret => {
            ins!(ctx, "ret");
            Ok(())
        }
        Inst::Break => {
            ins!(ctx, "ebreak");
            Ok(())
        }
        Inst::Nop => {
            ins!(ctx, "nop");
            Ok(())
        }
        Inst::IntSet {
            cc,
            w,
            dst,
            lhs,
            rhs,
        } => e_intset(ctx, mn, *cc, *w, dst, lhs, rhs),
        Inst::TestSet {
            w,
            value,
            mask,
            test,
            dst,
        } => e_testset(ctx, mn, *w, value, mask.as_ref(), *test, dst),
        Inst::FArith { op, k, arith } => e_farith(ctx, mn, *op, *k, arith),
        Inst::Fma {
            op,
            k,
            a,
            b,
            c,
            dst,
        } => e_fma(ctx, mn, *op, *k, a, b, c, *dst),
        Inst::FSqrt { k, dst, src } => e_fsqrt(ctx, mn, *k, *dst, src),
        Inst::FRound { k, mode, dst, src } => e_fround(ctx, mn, *k, *mode, *dst, src),
        Inst::FAbs { k, dst, src } => e_fabsneg(ctx, mn, *k, *dst, src, false),
        Inst::FNeg { k, dst, src } => e_fabsneg(ctx, mn, *k, *dst, src, true),
        Inst::FBit { or, k, dst, src } => e_fbit(ctx, mn, *or, *k, *dst, src),
        Inst::CvtFI { k, w, dst, src } => e_cvtfi(ctx, mn, *k, *w, *dst, src),
        Inst::CvtIF {
            signed,
            from,
            k,
            dst,
            src,
        } => e_cvtif(ctx, mn, *signed, *from, *k, *dst, src),
        Inst::CvtFF { from, to, dst, src } => e_cvtff(ctx, mn, *from, *to, *dst, src),
        Inst::Bitcast { dir, dst, src } => e_bitcast(ctx, mn, *dir, dst, src),
        Inst::BranchF {
            cc,
            k,
            lhs,
            rhs,
            target,
            patch,
        } => e_branchf(ctx, mn, *cc, *k, lhs, rhs, target, *patch),
        Inst::FSet {
            cc,
            k,
            dst,
            lhs,
            rhs,
        } => e_fset(ctx, mn, *cc, *k, dst, lhs, rhs),
        Inst::Fence { full: _ } => {
            // RISC-V has one barrier instruction. Both `memfence` and `fence`
            // print it.
            ins!(ctx, "fence");
            Ok(())
        }
        Inst::Pause => {
            ins!(ctx, "pause");
            Ok(())
        }
        Inst::TlsLoad { w, dst, idx } => e_tls(ctx, mn, *w, *dst, *idx, true),
        Inst::TlsStore { w, src, idx } => e_tls(ctx, mn, *w, *src, *idx, false),
        Inst::TlsLea { dst, idx } => e_tls_lea(ctx, mn, *dst, *idx),
        Inst::AtomicRmw { op, w, a, b } => e_rmw(ctx, mn, *op, *w, a, b),
        Inst::AtomicCas {
            w,
            mem,
            src,
            branch,
        } => e_cas(ctx, mn, *w, mem, *src, branch.as_ref(), false),
        Inst::LoadLinked { w, mem, dst } => e_loadlinked(ctx, mn, *w, mem, *dst),
        Inst::StoreCond {
            w,
            status,
            src,
            mem,
        } => e_storecond(ctx, mn, *w, *status, *src, mem),
        Inst::PairLoad { w, dst1, dst2, mem } => e_pair(ctx, mn, *w, dst1, dst2, mem, true),
        Inst::PairStore { w, src1, src2, mem } => e_pair(ctx, mn, *w, src1, src2, mem, false),
    }
}

/// Narrow (`B8`/`B16`) shift/rotate with x86 lane semantics and upper-bit
/// preservation: spill `dst`, mask to the lane, operate, merge back.
fn e_shift_narrow(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    op: ShiftOp,
    dst: Gpr,
    cnt: &ShiftCnt,
) -> Result<(), String> {
    let n = if w == Width::B8 { 8 } else { 16 };
    if dst == G1 {
        return Err(format!(
            "riscv64: `{}`: narrow shift aliased the scratch register",
            mn
        ));
    }
    ins!(ctx, "addi x2, x2, -8");
    ins!(ctx, "sd {}, 0(x2)", gpr(dst));
    // Mask to the lane so arithmetic shifts see the lane's own sign and
    // rotates stay inside the lane.
    ins!(ctx, "slli {}, {}, {}", gpr(dst), gpr(dst), 64 - n);
    ins!(ctx, "srli {}, {}, {}", gpr(dst), gpr(dst), 64 - n);
    match cnt {
        ShiftCnt::Imm(v) => {
            let c = (*v as u64 & 63) as i64;
            match op {
                ShiftOp::Shl => ins!(ctx, "slli {}, {}, {}", gpr(dst), gpr(dst), c),
                ShiftOp::Shr | ShiftOp::ShrSar => {
                    ins!(ctx, "srli {}, {}, {}", gpr(dst), gpr(dst), c);
                }
                ShiftOp::Rotl | ShiftOp::Rotr => {
                    let r = if op == ShiftOp::Rotl {
                        c as u64 % n as u64
                    } else {
                        (n as u64 - c as u64) % n as u64
                    };
                    if r != 0 {
                        ins!(ctx, "slli {}, {}, {}", gpr(G1), gpr(dst), r);
                        ins!(ctx, "srli {}, {}, {}", gpr(dst), gpr(dst), n - r as i64);
                        ins!(ctx, "or {}, {}, {}", gpr(dst), gpr(dst), gpr(G1));
                    }
                }
            }
        }
        ShiftCnt::Reg(g) => {
            if *g == G1 {
                return Err(format!(
                    "riscv64: `{}`: narrow shift count aliased scratch",
                    mn
                ));
            }
            match op {
                ShiftOp::Shl => ins!(ctx, "sll {}, {}, {}", gpr(dst), gpr(dst), gpr(*g)),
                ShiftOp::Shr | ShiftOp::ShrSar => {
                    ins!(ctx, "srl {}, {}, {}", gpr(dst), gpr(dst), gpr(*g));
                }
                ShiftOp::Rotl | ShiftOp::Rotr => {
                    lane_rot_reg(ctx, n, dst, *g, op == ShiftOp::Rotl)?;
                }
            }
        }
    }
    // The lane result merges under the spilled upper bits.
    ins!(ctx, "slli {}, {}, {}", gpr(G1), gpr(dst), 64 - n);
    ins!(ctx, "srli {}, {}, {}", gpr(G1), gpr(G1), 64 - n);
    ins!(ctx, "ld {}, 0(x2)", gpr(dst));
    ins!(ctx, "addi x2, x2, 8");
    ins!(ctx, "srli {}, {}, {}", gpr(dst), gpr(dst), n);
    ins!(ctx, "slli {}, {}, {}", gpr(dst), gpr(dst), n);
    ins!(ctx, "or {}, {}, {}", gpr(dst), gpr(dst), gpr(G1));
    Ok(())
}

/// `Shift`, `dst = dst OP cnt`.
fn e_shift(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    op: ShiftOp,
    dst: Gpr,
    cnt: &ShiftCnt,
) -> Result<(), String> {
    if w == Width::B8 || w == Width::B16 {
        return e_shift_narrow(ctx, mn, w, op, dst, cnt);
    }
    let bits: i64 = if w == Width::B32 { 32 } else { 64 };
    match cnt {
        ShiftCnt::Imm(v) => {
            let mask: u64 = if w == Width::B32 { 31 } else { 63 };
            let c = (*v as u64 & mask) as i64;
            match op {
                ShiftOp::Shl => {
                    ins!(ctx, "slli{} {}, {}, {}", w32(w), gpr(dst), gpr(dst), c);
                }
                ShiftOp::Shr => {
                    ins!(ctx, "srli{} {}, {}, {}", w32(w), gpr(dst), gpr(dst), c);
                }
                ShiftOp::ShrSar => {
                    ins!(ctx, "srai{} {}, {}, {}", w32(w), gpr(dst), gpr(dst), c);
                }
                ShiftOp::Rotl | ShiftOp::Rotr => {
                    let r = if op == ShiftOp::Rotl {
                        c as u64
                    } else {
                        (bits as u64 - c as u64) % bits as u64
                    };
                    rotl_imm(ctx, mn, w, dst, r as i64)?;
                }
            }
        }
        ShiftCnt::Reg(g) => match op {
            ShiftOp::Shl => {
                ins!(ctx, "sll{} {}, {}, {}", w32(w), gpr(dst), gpr(dst), gpr(*g));
            }
            ShiftOp::Shr => {
                ins!(ctx, "srl{} {}, {}, {}", w32(w), gpr(dst), gpr(dst), gpr(*g));
            }
            ShiftOp::ShrSar => {
                ins!(ctx, "sra{} {}, {}, {}", w32(w), gpr(dst), gpr(dst), gpr(*g));
            }
            ShiftOp::Rotl | ShiftOp::Rotr => {
                rot_reg(ctx, mn, w, dst, *g, op == ShiftOp::Rotl)?;
            }
        },
    }
    if w == Width::B32 {
        zero_upper32(ctx, dst);
    }
    Ok(())
}

//
// Extensions, division, counts.
//

/// `Extend`: sign/zero extension between widths.
fn e_extend(
    ctx: &mut LowerCtx,
    mn: &str,
    from: Width,
    to: Width,
    sx: Sx,
    dst: Gpr,
    src: &Op,
) -> Result<(), String> {
    let s = load_op_gpr(ctx, mn, src, from, G1)?;
    let (d, v) = (gpr(dst), gpr(s));
    match (from, to, sx) {
        (Width::B8, _, Sx::Zero) => ins!(ctx, "andi {}, {}, 255", d, v),
        (Width::B8, Width::B32, Sx::Sign) => {
            ins!(ctx, "slli {}, {}, 56", d, v);
            ins!(ctx, "srai {}, {}, 56", d, d);
            // x86 `movsbl` parity: keep only the low 32 bits.
            ins!(ctx, "slli {}, {}, 32", d, d);
            ins!(ctx, "srli {}, {}, 32", d, d);
        }
        (Width::B8, _, Sx::Sign) => {
            ins!(ctx, "slli {}, {}, 56", d, v);
            ins!(ctx, "srai {}, {}, 56", d, d);
        }
        (Width::B16, _, Sx::Zero) => {
            ins!(ctx, "slli {}, {}, 48", d, v);
            ins!(ctx, "srli {}, {}, 48", d, d);
        }
        (Width::B16, Width::B32, Sx::Sign) => {
            ins!(ctx, "slli {}, {}, 48", d, v);
            ins!(ctx, "srai {}, {}, 48", d, d);
            ins!(ctx, "slli {}, {}, 32", d, d);
            ins!(ctx, "srli {}, {}, 32", d, d);
        }
        (Width::B16, _, Sx::Sign) => {
            ins!(ctx, "slli {}, {}, 48", d, v);
            ins!(ctx, "srai {}, {}, 48", d, d);
        }
        (Width::B32, Width::B64, Sx::Sign) => ins!(ctx, "addiw {}, {}, 0", d, v),
        (Width::B32, _, _) => {
            ins!(ctx, "slli {}, {}, 32", d, v);
            ins!(ctx, "srli {}, {}, 32", d, d);
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: unsupported extension combination",
                mn
            ));
        }
    }
    Ok(())
}

fn div_rr(ctx: &mut LowerCtx, w: Width, signed: bool, div: bool, dst: Gpr, lhs: Gpr, rhs: Gpr) {
    let op = match (signed, div, w == Width::B32) {
        (true, true, false) => "div",
        (true, false, false) => "rem",
        (false, true, false) => "divu",
        (false, false, false) => "remu",
        (true, true, true) => "divw",
        (true, false, true) => "remw",
        (false, true, true) => "divuw",
        (false, false, true) => "remuw",
    };
    ins!(ctx, "{} {}, {}, {}", op, gpr(dst), gpr(lhs), gpr(rhs));
    if w == Width::B32 {
        zero_upper32(ctx, dst);
    }
}

/// `Div3` / `Rem3`: explicit divide/remainder (RV64 never traps).
#[allow(clippy::too_many_arguments)]
fn e_div(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    signed: bool,
    div: bool,
    dst: Gpr,
    dvd: &Op,
    dvs: &Op,
) -> Result<(), String> {
    let l = load_op_gpr(ctx, mn, dvd, w, G1)?;
    let rhs_needs_scratch = !matches!(dvs, Op::Gpr(_));
    let lhs_in_scratch = l == G1;
    if rhs_needs_scratch && lhs_in_scratch {
        ins!(ctx, "addi x2, x2, -8");
        ins!(ctx, "sd {}, 0(x2)", gpr(l));
        let r = load_op_gpr(ctx, mn, dvs, w, G1)?;
        ins!(ctx, "ld {}, 0(x2)", gpr(l));
        ins!(ctx, "addi x2, x2, 8");
        div_rr(ctx, w, signed, div, dst, l, r);
        return Ok(());
    }
    let r = load_op_gpr(ctx, mn, dvs, w, G1)?;
    div_rr(ctx, w, signed, div, dst, l, r);
    Ok(())
}

/// Leading-zero count (portable RV64I binary search, no Zbb).
fn clz_rr(ctx: &mut LowerCtx, w: Width, dst: Gpr, src: Gpr) {
    mov_reg(ctx, dst, src, Width::B64);
    let (d, n, t) = (gpr(dst), gpr(G1), gpr(G2));
    if w == Width::B32 {
        ins!(ctx, "slli {}, {}, 32", d, d);
        mov_imm(ctx, G2, 0xFFFF_FFFF);
        ins!(ctx, "or {}, {}, {}", d, d, t);
    }
    ins!(ctx, "addi {}, x0, 0", n);
    for k in [32, 16, 8, 4, 2, 1] {
        ins!(ctx, "srli {}, {}, {}", t, d, 64 - k);
        let skip = fresh(ctx);
        ins!(ctx, "bne {}, x0, {}", t, skip);
        ins!(ctx, "addi {}, {}, {}", n, n, k);
        ins!(ctx, "slli {}, {}, {}", d, d, k);
        bind(ctx, &skip);
    }
    let nonzero = fresh(ctx);
    ins!(ctx, "bne {}, x0, {}", d, nonzero);
    ins!(ctx, "addi {}, {}, 1", n, n);
    bind(ctx, &nonzero);
    mov_reg(ctx, dst, G1, Width::B64);
}

/// `Clz`.
fn e_clz(ctx: &mut LowerCtx, mn: &str, w: Width, dst: Gpr, src: &Op) -> Result<(), String> {
    let s = load_op_gpr(ctx, mn, src, w, G1)?;
    clz_rr(ctx, w, dst, s);
    Ok(())
}

/// Trailing-zero count (portable RV64I mirror of [`clz_rr`]).
fn ctz_rr(ctx: &mut LowerCtx, w: Width, dst: Gpr, src: Gpr) {
    mov_reg(ctx, dst, src, Width::B64);
    let (d, n, t) = (gpr(dst), gpr(G1), gpr(G2));
    if w == Width::B32 {
        mov_imm(ctx, G2, 0xFFFF_FFFF_0000_0000u64 as i64);
        ins!(ctx, "or {}, {}, {}", d, d, t);
    }
    ins!(ctx, "addi {}, x0, 0", n);
    for k in [32, 16, 8, 4, 2, 1] {
        ins!(ctx, "slli {}, {}, {}", t, d, 64 - k);
        let keep = fresh(ctx);
        let next = fresh(ctx);
        ins!(ctx, "bne {}, x0, {}", t, keep);
        ins!(ctx, "addi {}, {}, {}", n, n, k);
        ins!(ctx, "srli {}, {}, {}", d, d, k);
        ins!(ctx, "j {}", next);
        bind(ctx, &keep);
        bind(ctx, &next);
    }
    let nonzero = fresh(ctx);
    ins!(ctx, "bne {}, x0, {}", d, nonzero);
    ins!(ctx, "addi {}, {}, 1", n, n);
    bind(ctx, &nonzero);
    mov_reg(ctx, dst, G1, Width::B64);
}

/// `Ctz`.
fn e_ctz(ctx: &mut LowerCtx, mn: &str, w: Width, dst: Gpr, src: &Op) -> Result<(), String> {
    let s = load_op_gpr(ctx, mn, src, w, G1)?;
    ctz_rr(ctx, w, dst, s);
    Ok(())
}

/// Portable SWAR population count (no Zbb `cpop`).
fn popcnt_rr(ctx: &mut LowerCtx, dst: Gpr, src: Gpr) {
    mov_reg(ctx, dst, src, Width::B64);
    let (d, t, m) = (gpr(dst), gpr(G1), gpr(G2));
    mov_imm(ctx, G2, 0x5555_5555_5555_5555u64 as i64);
    ins!(ctx, "srli {}, {}, 1", t, d);
    ins!(ctx, "and {}, {}, {}", t, t, m);
    ins!(ctx, "sub {}, {}, {}", d, d, t);
    mov_imm(ctx, G2, 0x3333_3333_3333_3333u64 as i64);
    ins!(ctx, "and {}, {}, {}", t, d, m);
    ins!(ctx, "srli {}, {}, 2", d, d);
    ins!(ctx, "and {}, {}, {}", d, d, m);
    ins!(ctx, "add {}, {}, {}", d, d, t);
    mov_imm(ctx, G2, 0x0F0F_0F0F_0F0F_0F0Fu64 as i64);
    ins!(ctx, "srli {}, {}, 4", t, d);
    ins!(ctx, "add {}, {}, {}", d, d, t);
    ins!(ctx, "and {}, {}, {}", d, d, m);
    ins!(ctx, "srli {}, {}, 8", t, d);
    ins!(ctx, "add {}, {}, {}", d, d, t);
    ins!(ctx, "srli {}, {}, 16", t, d);
    ins!(ctx, "add {}, {}, {}", d, d, t);
    ins!(ctx, "srli {}, {}, 32", t, d);
    ins!(ctx, "add {}, {}, {}", d, d, t);
    ins!(ctx, "andi {}, {}, 127", d, d);
}

/// `Popcnt`. A `B32` count reads the zero-extended 32-bit operand.
fn e_popcnt(ctx: &mut LowerCtx, mn: &str, w: Width, dst: Gpr, src: &Op) -> Result<(), String> {
    let s = load_op_gpr(ctx, mn, src, w, G1)?;
    popcnt_rr(ctx, dst, s);
    Ok(())
}

fn intset_rr(ctx: &mut LowerCtx, cc: IntCc, dst: Gpr, lhs: Gpr, rhs: Gpr) {
    let (d, l, r) = (gpr(dst), gpr(lhs), gpr(rhs));
    match cc {
        IntCc::Eq => {
            ins!(ctx, "xor {}, {}, {}", d, l, r);
            ins!(ctx, "seqz {}, {}", d, d);
        }
        IntCc::Ne => {
            ins!(ctx, "xor {}, {}, {}", d, l, r);
            ins!(ctx, "snez {}, {}", d, d);
        }
        IntCc::Lt => ins!(ctx, "slt {}, {}, {}", d, l, r),
        IntCc::Ge => {
            ins!(ctx, "slt {}, {}, {}", d, l, r);
            ins!(ctx, "xori {}, {}, 1", d, d);
        }
        IntCc::Gt => ins!(ctx, "slt {}, {}, {}", d, r, l),
        IntCc::Le => {
            ins!(ctx, "slt {}, {}, {}", d, r, l);
            ins!(ctx, "xori {}, {}, 1", d, d);
        }
        IntCc::Lo => ins!(ctx, "sltu {}, {}, {}", d, l, r),
        IntCc::Hs => {
            ins!(ctx, "sltu {}, {}, {}", d, l, r);
            ins!(ctx, "xori {}, {}, 1", d, d);
        }
        IntCc::Hi => ins!(ctx, "sltu {}, {}, {}", d, r, l),
        IntCc::Ls => {
            ins!(ctx, "sltu {}, {}, {}", d, r, l);
            ins!(ctx, "xori {}, {}, 1", d, d);
        }
    }
}

/// Canonicalize a width lane for a comparison: sign-extend for signed
/// conditions, zero-extend for unsigned ones.
fn canon_lane(ctx: &mut LowerCtx, v: Gpr, w: Width, signed: bool) {
    match (signed, w) {
        (_, Width::B64) => {}
        (false, Width::B8) => ins!(ctx, "andi {}, {}, 255", gpr(v), gpr(v)),
        (false, Width::B16) => {
            ins!(ctx, "slli {}, {}, 48", gpr(v), gpr(v));
            ins!(ctx, "srli {}, {}, 48", gpr(v), gpr(v));
        }
        (false, _) => {
            ins!(ctx, "slli {}, {}, 32", gpr(v), gpr(v));
            ins!(ctx, "srli {}, {}, 32", gpr(v), gpr(v));
        }
        (true, Width::B8) => {
            ins!(ctx, "slli {}, {}, 56", gpr(v), gpr(v));
            ins!(ctx, "srai {}, {}, 56", gpr(v), gpr(v));
        }
        (true, Width::B16) => {
            ins!(ctx, "slli {}, {}, 48", gpr(v), gpr(v));
            ins!(ctx, "srai {}, {}, 48", gpr(v), gpr(v));
        }
        (true, _) => {
            ins!(ctx, "slli {}, {}, 32", gpr(v), gpr(v));
            ins!(ctx, "srai {}, {}, 32", gpr(v), gpr(v));
        }
    }
}

/// `IntSet`: `dst = (lhs cc rhs)` as 0/1.
fn e_intset(
    ctx: &mut LowerCtx,
    mn: &str,
    cc: IntCc,
    w: Width,
    dst: &Op,
    lhs: &Op,
    rhs: &Op,
) -> Result<(), String> {
    let l = load_op_gpr(ctx, mn, lhs, w, G1)?;
    let rhs_needs_scratch = !matches!(rhs, Op::Gpr(_));
    let lhs_in_scratch = l == G1;
    // Spilled destinations go through `G2` so `e_store` keeps `G1` free for
    // address synthesis.
    let d = match dst {
        Op::Gpr(d) => *d,
        Op::Mem(_) => G2,
        _ => {
            return Err(format!(
                "riscv64: `{}`: compare-set needs a register or memory destination",
                mn
            ));
        }
    };
    let signed = matches!(cc, IntCc::Gt | IntCc::Ge | IntCc::Lt | IntCc::Le);
    if rhs_needs_scratch && lhs_in_scratch {
        ins!(ctx, "addi x2, x2, -8");
        ins!(ctx, "sd {}, 0(x2)", gpr(l));
        let r = load_op_gpr(ctx, mn, rhs, w, G1)?;
        ins!(ctx, "ld {}, 0(x2)", gpr(l));
        ins!(ctx, "addi x2, x2, 8");
        canon_lane(ctx, l, w, signed);
        canon_lane(ctx, r, w, signed);
        intset_rr(ctx, cc, d, l, r);
    } else {
        let r = load_op_gpr(ctx, mn, rhs, w, G1)?;
        canon_lane(ctx, l, w, signed);
        canon_lane(ctx, r, w, signed);
        intset_rr(ctx, cc, d, l, r);
    }
    match dst {
        Op::Mem(a) => e_store(ctx, mn, w, &Op::Gpr(G2), a),
        _ => Ok(()),
    }
}

/// Materialize a test value (+ optional mask) into scratch for
/// `TestBranch`/`TestSet`.
fn test_value(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    value: &Op,
    mask: Option<&Op>,
) -> Result<Gpr, String> {
    let lw = if w == Width::B64 { w } else { Width::B32 };
    let v = match value {
        Op::Gpr(g) => *g,
        Op::Mem(a) => {
            e_load(ctx, mn, lw, Sx::Zero, G1, a)?;
            G1
        }
        Op::Imm(vv) => {
            mov_imm_w(ctx, G1, lw, *vv);
            G1
        }
        Op::Sym(s) => {
            mov_imm_sym(ctx, G1, *s)?;
            G1
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: test needs a register, memory, or immediate value",
                mn
            ));
        }
    };
    let Some(m) = mask else {
        return Ok(v);
    };
    let mv = match m {
        Op::Gpr(g) => *g,
        _ if v == G1 => load_op_gpr(ctx, mn, m, Width::B32, G2)?,
        _ => load_op_gpr(ctx, mn, m, Width::B32, G1)?,
    };
    if v == G1 {
        ins!(ctx, "and {}, {}, {}", gpr(G1), gpr(G1), gpr(mv));
        Ok(G1)
    } else {
        ins!(ctx, "and {}, {}, {}", gpr(G2), gpr(v), gpr(mv));
        Ok(G2)
    }
}

/// `TestSet`: `dst = test(value(, mask))`.
fn e_testset(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    value: &Op,
    mask: Option<&Op>,
    test: TestKind,
    dst: &Op,
) -> Result<(), String> {
    let v = test_value(ctx, mn, w, value, mask)?;
    let bits = lane_bits(w);
    match test {
        TestKind::Zero => ins!(ctx, "seqz {}, {}", gpr(G2), gpr(v)),
        TestKind::NonZero => ins!(ctx, "snez {}, {}", gpr(G2), gpr(v)),
        TestKind::Sign => {
            if bits == 64 {
                ins!(ctx, "slti {}, {}, 0", gpr(G2), gpr(v));
            } else {
                ins!(ctx, "srli {}, {}, {}", gpr(G2), gpr(v), bits - 1);
                ins!(ctx, "andi {}, {}, 1", gpr(G2), gpr(G2));
            }
        }
    }
    match dst {
        Op::Gpr(d) => {
            mov_reg(ctx, *d, G2, Width::B64);
            Ok(())
        }
        Op::Mem(a) => e_store(ctx, mn, w, &Op::Gpr(G2), a),
        _ => Err(format!(
            "riscv64: `{}`: test-set needs a register or memory destination",
            mn
        )),
    }
}

/// Emit a branch to `target` when `v` is zero (`eq`) or nonzero.
fn emit_cond_branch(ctx: &mut LowerCtx, eq: bool, v: Gpr, target: &str, patch: bool) {
    if patch {
        let skip = fresh(ctx);
        if eq {
            ins!(ctx, "bne {}, x0, {}", gpr(v), skip);
        } else {
            ins!(ctx, "beq {}, x0, {}", gpr(v), skip);
        }
        ins!(ctx, "j {}", target);
        bind(ctx, &skip);
        return;
    }
    if eq {
        ins!(ctx, "beq {}, x0, {}", gpr(v), target);
    } else {
        ins!(ctx, "bne {}, x0, {}", gpr(v), target);
    }
}

/// `TestBranch`: test `value(, mask)` then branch.
#[allow(clippy::too_many_arguments)]
fn e_testbranch(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    value: &Op,
    mask: Option<&Op>,
    test: TestKind,
    target: &offlineasm_ir::Lbl,
    patch: bool,
) -> Result<(), String> {
    let v = test_value(ctx, mn, w, value, mask)?;
    let bits = lane_bits(w);
    let t = text::label_text(ctx, *target)?;
    // Sign observation moves the tested bit to bit 0.
    let v = if test == TestKind::Sign {
        if bits == 64 {
            ins!(ctx, "slti {}, {}, 0", gpr(G2), gpr(v));
        } else {
            ins!(ctx, "srli {}, {}, {}", gpr(G2), gpr(v), bits - 1);
            ins!(ctx, "andi {}, {}, 1", gpr(G2), gpr(G2));
        }
        G2
    } else {
        v
    };
    emit_cond_branch(ctx, test == TestKind::Zero, v, &t, patch);
    Ok(())
}

/// Load a branch/compare side, canonicalizing narrow lanes.
fn branch_side(
    ctx: &mut LowerCtx,
    mn: &str,
    op: &Op,
    w: Width,
    cc: IntCc,
    tmp: Gpr,
) -> Result<Gpr, String> {
    let r = load_op_gpr(
        ctx,
        mn,
        op,
        if w == Width::B64 { w } else { Width::B32 },
        tmp,
    )?;
    let signed = matches!(cc, IntCc::Gt | IntCc::Ge | IntCc::Lt | IntCc::Le);
    if signed {
        match w {
            Width::B8 => {
                ins!(ctx, "slli {}, {}, 56", gpr(tmp), gpr(r));
                ins!(ctx, "srai {}, {}, 56", gpr(tmp), gpr(r));
                return Ok(tmp);
            }
            Width::B16 => {
                ins!(ctx, "slli {}, {}, 48", gpr(tmp), gpr(r));
                ins!(ctx, "srai {}, {}, 48", gpr(tmp), gpr(r));
                return Ok(tmp);
            }
            Width::B32 => {
                ins!(ctx, "slli {}, {}, 32", gpr(tmp), gpr(r));
                ins!(ctx, "srai {}, {}, 32", gpr(tmp), gpr(tmp));
                return Ok(tmp);
            }
            Width::B64 => {}
        }
    }
    Ok(r)
}

/// The raw branch for `cc` over `(l, r)`.
fn emit_branch_cc_raw(ctx: &mut LowerCtx, cc: IntCc, l: Gpr, r: Gpr, t: &str) {
    let (a, b) = (gpr(l), gpr(r));
    match cc {
        IntCc::Eq => ins!(ctx, "beq {}, {}, {}", a, b, t),
        IntCc::Ne => ins!(ctx, "bne {}, {}, {}", a, b, t),
        IntCc::Lt => ins!(ctx, "blt {}, {}, {}", a, b, t),
        IntCc::Ge => ins!(ctx, "bge {}, {}, {}", a, b, t),
        IntCc::Lo => ins!(ctx, "bltu {}, {}, {}", a, b, t),
        IntCc::Hs => ins!(ctx, "bgeu {}, {}, {}", a, b, t),
        // Greater-than forms swap the sides.
        IntCc::Gt => ins!(ctx, "blt {}, {}, {}", b, a, t),
        IntCc::Le => ins!(ctx, "bge {}, {}, {}", b, a, t),
        IntCc::Hi => ins!(ctx, "bltu {}, {}, {}", b, a, t),
        IntCc::Ls => ins!(ctx, "bgeu {}, {}, {}", b, a, t),
    }
}

/// Flip an integer condition (for canonicalizing `imm OP x`).
fn flip_cc(cc: IntCc) -> IntCc {
    match cc {
        IntCc::Eq => IntCc::Eq,
        IntCc::Ne => IntCc::Ne,
        IntCc::Hi => IntCc::Lo,
        IntCc::Hs => IntCc::Ls,
        IntCc::Lo => IntCc::Hi,
        IntCc::Ls => IntCc::Hs,
        IntCc::Gt => IntCc::Lt,
        IntCc::Ge => IntCc::Le,
        IntCc::Lt => IntCc::Gt,
        IntCc::Le => IntCc::Ge,
    }
}

fn emit_branch_cc(ctx: &mut LowerCtx, cc: IntCc, l: Gpr, r: Gpr, t: &str, patch: bool) {
    if patch {
        let skip = fresh(ctx);
        emit_branch_cc_raw(ctx, flip_cc(cc), l, r, &skip);
        ins!(ctx, "j {}", t);
        bind(ctx, &skip);
        return;
    }
    emit_branch_cc_raw(ctx, cc, l, r, t);
}

#[allow(clippy::too_many_arguments)]
fn e_branch(
    ctx: &mut LowerCtx,
    mn: &str,
    cc: IntCc,
    w: Width,
    lhs: &Op,
    rhs: &Op,
    target: &offlineasm_ir::Lbl,
    patch: bool,
) -> Result<(), String> {
    let (cc, lhs, rhs) = match (lhs, rhs) {
        (Op::Imm(_), Op::Gpr(_)) | (Op::Imm(_), Op::Mem(_)) => (flip_cc(cc), rhs, lhs),
        _ => (cc, lhs, rhs),
    };
    let l = branch_side(ctx, mn, lhs, w, cc, G1)?;
    let l_in_scratch = l == G1;
    let r = branch_side(ctx, mn, rhs, w, cc, if l_in_scratch { G2 } else { G1 })?;
    let t = text::label_text(ctx, *target)?;
    emit_branch_cc(ctx, cc, l, r, &t, patch);
    Ok(())
}

fn flag_op(ctx: &mut LowerCtx, mn: &str, op: &Op, w: Width, tmp: Gpr) -> Result<Gpr, String> {
    match op {
        Op::Gpr(g) => Ok(*g),
        Op::Imm(v) => {
            mov_imm_w(ctx, tmp, if w == Width::B64 { w } else { Width::B32 }, *v);
            Ok(tmp)
        }
        Op::Sym(s) => {
            mov_imm_sym(ctx, tmp, *s)?;
            Ok(tmp)
        }
        Op::Mem(a) => {
            let lw = if w == Width::B64 { w } else { Width::B32 };
            e_load(ctx, mn, lw, Sx::Zero, tmp, a)?;
            Ok(tmp)
        }
        _ => Err(format!(
            "riscv64: `{}`: flag ALU needs a register, memory, or immediate operand",
            mn
        )),
    }
}

fn stash_a(ctx: &mut LowerCtx, mn: &str, a: &Op) -> Result<(), String> {
    match a {
        Op::Gpr(g) => mov_reg(ctx, G2, *g, Width::B64),
        Op::Imm(v) => mov_imm(ctx, G2, *v),
        Op::Sym(s) => mov_imm_sym(ctx, G2, *s)?,
        Op::Mem(m) => e_load(ctx, mn, Width::B64, Sx::Zero, G2, m)?,
        _ => {
            return Err(format!(
                "riscv64: `{}`: flag ALU needs a register, memory, or immediate operand",
                mn
            ));
        }
    }
    Ok(())
}

/// `FLAGS = Z | N << 1` from a fully-masked lane in `t`.
fn flags_zn(ctx: &mut LowerCtx, t: Gpr, bits: u32) {
    ins!(ctx, "seqz {}, {}", gpr(FLAGS), gpr(t));
    if bits == 64 {
        ins!(ctx, "slti {}, {}, 0", gpr(G1), gpr(t));
    } else {
        ins!(ctx, "srli {}, {}, {}", gpr(G1), gpr(t), bits - 1);
        ins!(ctx, "andi {}, {}, 1", gpr(G1), gpr(G1));
    }
    ins!(ctx, "slli {}, {}, 1", gpr(G1), gpr(G1));
    ins!(ctx, "or {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G1));
}

/// Full-width Add/Sub flag derivation (`B64`): `r` is the result
/// register, `a` the stashed `a` side (`G2`), `b` the reloaded `b` side
/// (a user register, `G1`, or `G2` when `b` aliased `a`). Writes all four
/// `FLAGS` bits. `r` survives; `a` (a private copy) and `b` (when it is
/// `G1`) die. Every read of `b` precedes the first write to `G1`, so `b`
/// may live in it.
fn derive_addsub_64(ctx: &mut LowerCtx, sub: bool, r: Gpr, a: Gpr, b: Gpr) {
    let (rr, aa, bb) = (gpr(r), gpr(a), gpr(b));
    let (f, tv) = (gpr(FLAGS), gpr(G1));
    // C (bit 2): carry (`r < a`, unsigned) / not-borrow (`!(a < b)`).
    if sub {
        ins!(ctx, "sltu {}, {}, {}", f, aa, bb);
        ins!(ctx, "xori {}, {}, 1", f, f);
    } else {
        ins!(ctx, "sltu {}, {}, {}", f, rr, aa);
    }
    ins!(ctx, "slli {}, {}, 2", f, f);
    // V (bit 3): sign((a ^ b) & (a ^ r)) for Sub, sign((~(a ^ b)) &
    // (a ^ r)) for Add.
    ins!(ctx, "xor {}, {}, {}", tv, aa, bb);
    if !sub {
        ins!(ctx, "xori {}, {}, -1", tv, tv);
    }
    ins!(ctx, "xor {}, {}, {}", aa, aa, rr); // `a` is a private copy now
    ins!(ctx, "and {}, {}, {}", tv, tv, aa);
    ins!(ctx, "srli {}, {}, 63", tv, tv);
    ins!(ctx, "slli {}, {}, 3", tv, tv);
    ins!(ctx, "or {}, {}, {}", f, f, tv);
    // Z (bit 0) / N (bit 1) from the result.
    ins!(ctx, "seqz {}, {}", tv, rr);
    ins!(ctx, "slti {}, {}, 0", aa, rr);
    ins!(ctx, "slli {}, {}, 1", aa, aa);
    ins!(ctx, "or {}, {}, {}", tv, tv, aa);
    ins!(ctx, "or {}, {}, {}", f, f, tv);
}

/// Narrow/`B32` Add/Sub flag derivation: `a` (in `G2`) and `b` (in `G1`)
/// are raw lane values; `mask`/`bits` select the lane (`sh = 64 - bits`).
/// Widened sides make the sum exact, so V comes from a truncation check
/// and C from the lane values. Uses one 16-byte stack slot.
fn derive_addsub_narrow(ctx: &mut LowerCtx, sub: bool, mask: i64, bits: u32) {
    let sh = 64 - bits;
    let (a, b, f) = (gpr(G2), gpr(G1), gpr(FLAGS));
    // Widen both sides (sign-extended exact) and park the exact sum.
    ins!(ctx, "slli {}, {}, {}", a, a, sh);
    ins!(ctx, "srai {}, {}, {}", a, a, sh);
    ins!(ctx, "slli {}, {}, {}", b, b, sh);
    ins!(ctx, "srai {}, {}, {}", b, b, sh);
    if sub {
        ins!(ctx, "sub {}, {}, {}", f, a, b);
    } else {
        ins!(ctx, "add {}, {}, {}", f, a, b);
    }
    ins!(ctx, "addi x2, x2, -16");
    ins!(ctx, "sd {}, 0(x2)", f);
    // C from the zero-extended lanes: carry out (Add) / not-borrow (Sub).
    // The widened sides die here. The sum is parked.
    mov_imm(ctx, FLAGS, mask);
    ins!(ctx, "and {}, {}, {}", a, a, f);
    ins!(ctx, "and {}, {}, {}", b, b, f);
    if sub {
        ins!(ctx, "sltu {}, {}, {}", b, a, b);
        ins!(ctx, "xori {}, {}, 1", b, b);
    } else {
        ins!(ctx, "add {}, {}, {}", b, a, b);
        ins!(ctx, "srli {}, {}, {}", b, b, bits);
        ins!(ctx, "andi {}, {}, 1", b, b);
    }
    ins!(ctx, "slli {}, {}, 2", f, b);
    // V = (sext(trunc(sum)) != sum). `G2` holds the mask (`FLAGS` holds C).
    ins!(ctx, "ld {}, 0(x2)", b);
    mov_imm(ctx, G2, mask);
    ins!(ctx, "and {}, {}, {}", b, b, a);
    ins!(ctx, "slli {}, {}, {}", a, b, sh);
    ins!(ctx, "srai {}, {}, {}", a, a, sh);
    ins!(ctx, "ld {}, 0(x2)", b);
    ins!(ctx, "xor {}, {}, {}", b, a, b);
    ins!(ctx, "snez {}, {}", b, b);
    ins!(ctx, "slli {}, {}, 3", b, b);
    ins!(ctx, "or {}, {}, {}", f, f, b);
    // Z / N from the truncated lane.
    ins!(ctx, "ld {}, 0(x2)", b);
    mov_imm(ctx, G2, mask);
    ins!(ctx, "and {}, {}, {}", b, b, a);
    ins!(ctx, "srli {}, {}, {}", a, b, bits - 1);
    ins!(ctx, "andi {}, {}, 1", a, a);
    ins!(ctx, "slli {}, {}, 1", a, a);
    ins!(ctx, "seqz {}, {}", b, b);
    ins!(ctx, "or {}, {}, {}", b, b, a);
    ins!(ctx, "or {}, {}, {}", f, f, b);
    ins!(ctx, "addi x2, x2, 16");
}

/// Where the `b` side of a flag-setting Add/Sub lives once `op_n` ran.
#[derive(Clone, Copy)]
enum BSide {
    /// Still readable from its operand (`dst` is not `b`): registers stay,
    /// memory/immediates reload into `G1`.
    Op,
    /// `b` was `dst` and `a` is another operand, so `dst` no longer holds
    /// it: [`pin_b`] copied it to `FLAGS` before the op.
    Snap,
    /// `b`, `a`, and `dst` were all one register: the `a` stash in `G2`
    /// is `b` too.
    SameAsA,
}

/// Before `op_n` overwrites `dst`, keep the value `b` will need if `b` is
/// `dst` itself (`stash_a` already copied `a` to `G2`).
fn pin_b(ctx: &mut LowerCtx, a_op: &Op, b_op: &Op, dst: Gpr) -> BSide {
    match b_op {
        Op::Gpr(g) if *g == dst => {
            if matches!(a_op, Op::Gpr(ag) if *ag == dst) {
                BSide::SameAsA
            } else {
                mov_reg(ctx, FLAGS, dst, Width::B64);
                BSide::Snap
            }
        }
        _ => BSide::Op,
    }
}

/// Derive `Add`/`Sub` flags after `op_n` computed `r` into a register
/// destination: stash discipline is the caller's job (`a` already in
/// `G2`, `b` pinned per [`pin_b`]). `b` is materialized into a register
/// here. `r` survives.
fn derive_reg(
    ctx: &mut LowerCtx,
    mn: &str,
    sub: bool,
    w: Width,
    b_op: &Op,
    bside: BSide,
    r: Gpr,
) -> Result<(), String> {
    let b = match bside {
        BSide::Snap => {
            mov_reg(ctx, G1, FLAGS, Width::B64);
            G1
        }
        BSide::SameAsA => G2,
        BSide::Op => flag_op(ctx, mn, b_op, w, G1)?,
    };
    if w == Width::B64 {
        derive_addsub_64(ctx, sub, r, G2, b);
        return Ok(());
    }
    // The narrow derivation reads `b` from `G1` and `a` from `G2`.
    mov_reg(ctx, G1, b, Width::B64);
    derive_addsub_narrow(ctx, sub, lane_mask(w), lane_bits(w));
    Ok(())
}

fn e_alus(ctx: &mut LowerCtx, mn: &str, op: AluOp, w: Width, alu: &Alu3) -> Result<(), String> {
    let k = match op {
        AluOp::Add => AluKind::Add,
        AluOp::Sub => AluKind::Sub,
        AluOp::Or => AluKind::Or,
    };
    let ops = alu_args(alu);
    let mem_dst = ops.last().is_some_and(|o| matches!(o, Op::Mem(_)));
    let a_op: Op = match ops.as_slice() {
        [_, dst] => *dst,
        [lhs, _, _] => *lhs,
        _ => {
            return Err(format!("riscv64: `{}`: flag ALU takes 2 or 3 operands", mn));
        }
    };
    let b_op: Op = match ops.as_slice() {
        [rhs, _] => *rhs,
        [_, rhs, _] => *rhs,
        _ => {
            return Err(format!("riscv64: `{}`: flag ALU takes 2 or 3 operands", mn));
        }
    };
    let needs_ab = k == AluKind::Add || k == AluKind::Sub;
    let mut bside = BSide::Op;
    if needs_ab && !mem_dst {
        stash_a(ctx, mn, &a_op)?;
        if let Some(Op::Gpr(d)) = ops.last() {
            bside = pin_b(ctx, &a_op, &b_op, *d);
        }
    }
    op_n(ctx, mn, k, w, &ops)?;
    if mem_dst {
        if needs_ab {
            return Err(format!(
                "riscv64: `{}`: flag-setting add/sub over memory cannot persist carry/overflow",
                mn
            ));
        }
        let a = match ops.last() {
            Some(Op::Mem(m)) => *m,
            _ => {
                return Err(format!("riscv64: `{}`: flag ALU takes 2 or 3 operands", mn));
            }
        };
        let lw = if w == Width::B64 { w } else { Width::B32 };
        e_load(ctx, mn, lw, Sx::Zero, G1, &a)?;
        let bits = lane_bits(w);
        if bits == 64 {
            flags_zn(ctx, G1, 64);
        } else {
            mov_imm(ctx, G2, lane_mask(w));
            ins!(ctx, "and {}, {}, {}", gpr(G1), gpr(G1), gpr(G2));
            flags_zn(ctx, G1, bits);
        }
        return Ok(());
    }
    if k == AluKind::Or {
        let bits = lane_bits(w);
        let Some(Op::Gpr(d)) = ops.last() else {
            return Err(format!("riscv64: `{}`: flag ALU takes 2 or 3 operands", mn));
        };
        if bits != 64 {
            mov_imm(ctx, G1, lane_mask(w));
            ins!(ctx, "and {}, {}, {}", gpr(G1), gpr(*d), gpr(G1));
            flags_zn(ctx, G1, bits);
        } else {
            flags_zn(ctx, *d, 64);
        }
        return Ok(());
    }
    let r = match ops.last() {
        Some(Op::Gpr(d)) => *d,
        _ => {
            return Err(format!("riscv64: `{}`: flag ALU takes 2 or 3 operands", mn));
        }
    };
    derive_reg(ctx, mn, k == AluKind::Sub, w, &b_op, bside, r)
}

/// Isolate a `FLAGS` bit in scratch (zero iff clear). A branch only needs
/// zero versus nonzero, so one `andi` does it.
fn flag_bit(ctx: &mut LowerCtx, bit: u32) {
    ins!(ctx, "andi {}, {}, {}", gpr(G1), gpr(FLAGS), 1u32 << bit);
}

/// Branch on a `FLAGS` bit.
fn branch_flag(ctx: &mut LowerCtx, bit: u32, taken_if_set: bool, target: &str, patch: bool) {
    flag_bit(ctx, bit);
    if patch {
        let skip = fresh(ctx);
        if taken_if_set {
            ins!(ctx, "beq {}, x0, {}", gpr(G1), skip);
        } else {
            ins!(ctx, "bne {}, x0, {}", gpr(G1), skip);
        }
        ins!(ctx, "j {}", target);
        bind(ctx, &skip);
        return;
    }
    if taken_if_set {
        ins!(ctx, "bne {}, x0, {}", gpr(G1), target);
    } else {
        ins!(ctx, "beq {}, x0, {}", gpr(G1), target);
    }
}

fn e_flagbranch(
    ctx: &mut LowerCtx,
    flag: PredFlag,
    target: &offlineasm_ir::Lbl,
    patch: bool,
) -> Result<(), String> {
    let (bit, set) = match flag {
        PredFlag::O => (3, true),
        PredFlag::S => (1, true),
        PredFlag::Z => (0, true),
        PredFlag::Nz => (0, false),
    };
    let t = text::label_text(ctx, *target)?;
    branch_flag(ctx, bit, set, &t, patch);
    Ok(())
}

/// Branch condition on one register against zero.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ZCond {
    Eqz,
    Nez,
    Ltz,
}

/// Branch to `target` when `cond` holds of `v`. The patched form inverts
/// over a patchable jump.
fn branch_zero(ctx: &mut LowerCtx, v: Gpr, cond: ZCond, target: &str, patch: bool) {
    let (taken, inverse) = match cond {
        ZCond::Eqz => ("beqz", "bnez"),
        ZCond::Nez => ("bnez", "beqz"),
        ZCond::Ltz => ("bltz", "bgez"),
    };
    if patch {
        let skip = fresh(ctx);
        ins!(ctx, "{} {}, {}", inverse, gpr(v), skip);
        ins!(ctx, "j {}", target);
        bind(ctx, &skip);
        return;
    }
    ins!(ctx, "{} {}, {}", taken, gpr(v), target);
}

/// `b` side of an overflow pre-check: a register, or an immediate small
/// enough for `addi` (already sign-extended to the lane for `B32`).
#[derive(Clone, Copy)]
enum OvfB {
    Reg(Gpr),
    Imm(i64),
}

/// Leave a nonzero value in `FLAGS` iff `a OP b` overflows (signed, at
/// width `w`), computed from the *original* operands so it can run before
/// `op_n` destroys either of them. `FLAGS` is free here (fused branches
/// never persist flags); `G1`/`G2` are temps, so a memory operand is
/// loaded into `G2` (`b`) then `G1` (`a`) (`e_load` may borrow `G1` for
/// the address, so `b` goes first).
///
/// `B32` sides are raw lanes with unspecified upper halves, so each is
/// normalized with `addiw` before the exact 64-bit op and the check is
/// `sext32(sum) != sum`. `B64` add/sub use the sign-of-`b` versus
/// `r < a` identity. `B64` multiply compares `mulh` with `sign(mul)`.
fn overflow_precheck(
    ctx: &mut LowerCtx,
    mn: &str,
    k: AluKind,
    w: Width,
    a_op: &Op,
    b_op: &Op,
) -> Result<(), String> {
    let lw = if w == Width::B64 { w } else { Width::B32 };
    let imm_ok = |v: i64| match k {
        AluKind::Sub => fits12(-v),
        AluKind::Add => fits12(v),
        _ => false,
    };
    // `b` already normalized once it is a sign-extended materialized
    // immediate (or symbol) in `G2`.
    let mut b_normalized = false;
    let b = match b_op {
        Op::Gpr(g) => OvfB::Reg(*g),
        Op::Imm(v) => {
            let v = if w == Width::B64 {
                *v
            } else {
                *v as i32 as i64
            };
            if imm_ok(v) {
                OvfB::Imm(v)
            } else {
                mov_imm(ctx, G2, v);
                b_normalized = true;
                OvfB::Reg(G2)
            }
        }
        Op::Sym(s) => {
            mov_imm_sym(ctx, G2, *s)?;
            OvfB::Reg(G2)
        }
        Op::Mem(m) => {
            e_load(ctx, mn, lw, Sx::Zero, G2, m)?;
            OvfB::Reg(G2)
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: op-branch needs register, memory, or immediate operands",
                mn
            ));
        }
    };
    let a = match a_op {
        Op::Gpr(g) => *g,
        Op::Imm(v) => {
            mov_imm(ctx, G1, *v);
            G1
        }
        Op::Sym(s) => {
            mov_imm_sym(ctx, G1, *s)?;
            G1
        }
        Op::Mem(m) => {
            e_load(ctx, mn, lw, Sx::Zero, G1, m)?;
            G1
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: op-branch needs register, memory, or immediate operands",
                mn
            ));
        }
    };
    if w == Width::B32 {
        ins!(ctx, "addiw {}, {}, 0", gpr(G1), gpr(a));
        let rb = match b {
            OvfB::Reg(g) => {
                if !b_normalized {
                    ins!(ctx, "addiw {}, {}, 0", gpr(G2), gpr(g));
                    G2
                } else {
                    g
                }
            }
            OvfB::Imm(_) => G2, // unused
        };
        match (k, b) {
            (AluKind::Add, OvfB::Imm(v)) => ins!(ctx, "addi {}, {}, {}", gpr(FLAGS), gpr(G1), v),
            (AluKind::Sub, OvfB::Imm(v)) => ins!(ctx, "addi {}, {}, {}", gpr(FLAGS), gpr(G1), -v),
            (AluKind::Add, _) => ins!(ctx, "add {}, {}, {}", gpr(FLAGS), gpr(G1), gpr(rb)),
            (AluKind::Sub, _) => ins!(ctx, "sub {}, {}, {}", gpr(FLAGS), gpr(G1), gpr(rb)),
            (AluKind::Mul, OvfB::Reg(_)) => {
                ins!(ctx, "mul {}, {}, {}", gpr(FLAGS), gpr(G1), gpr(rb))
            }
            _ => {
                return Err(format!(
                    "riscv64: `{}`: overflow check is add/sub/mul only",
                    mn
                ));
            }
        }
        ins!(ctx, "addiw {}, {}, 0", gpr(G1), gpr(FLAGS));
        ins!(ctx, "xor {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G1));
        return Ok(());
    }
    match k {
        AluKind::Add | AluKind::Sub => {
            let sub = k == AluKind::Sub;
            let mnem = if sub { "sub" } else { "add" };
            match b {
                OvfB::Reg(g) => ins!(ctx, "{} {}, {}, {}", mnem, gpr(FLAGS), gpr(a), gpr(g)),
                OvfB::Imm(v) => ins!(
                    ctx,
                    "addi {}, {}, {}",
                    gpr(FLAGS),
                    gpr(a),
                    if sub { -v } else { v }
                ),
            }
            ins!(ctx, "slt {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(a)); // r < a
            match b {
                OvfB::Reg(g) => {
                    if sub {
                        ins!(ctx, "slt {}, x0, {}", gpr(G2), gpr(g)); // b > 0
                    } else {
                        ins!(ctx, "slti {}, {}, 0", gpr(G2), gpr(g)); // b < 0
                    }
                    ins!(ctx, "xor {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G2));
                }
                OvfB::Imm(v) => {
                    if (sub && v > 0) || (!sub && v < 0) {
                        ins!(ctx, "xori {}, {}, 1", gpr(FLAGS), gpr(FLAGS));
                    }
                }
            }
        }
        AluKind::Mul => {
            let g = match b {
                OvfB::Reg(g) => g,
                OvfB::Imm(_) => unreachable!("mul immediates are always materialized"),
            };
            ins!(ctx, "mulh {}, {}, {}", gpr(FLAGS), gpr(a), gpr(g));
            ins!(ctx, "mul {}, {}, {}", gpr(G1), gpr(a), gpr(g));
            ins!(ctx, "srai {}, {}, 63", gpr(G1), gpr(G1));
            ins!(ctx, "xor {}, {}, {}", gpr(FLAGS), gpr(FLAGS), gpr(G1));
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: overflow check is add/sub/mul only",
                mn
            ));
        }
    }
    Ok(())
}

/// Fused ALU+flag branch (`b<op><w><flag>`).
///
/// No pending flags are produced or consumed: each flag kind gets the
/// shortest direct sequence.
/// - `Z`/`Nz`/`S`: run the ALU op, then branch on the result register
///   (a memory destination is reloaded sign-extended). A `B32` result
///   register has an unspecified upper half, so `Z`/`Nz` still test the
///   whole register (a zero lane is zero in either extension) but `S`
///   re-extends with `addiw` first.
/// - `O`: an overflow indicator is computed into `FLAGS` from the
///   original operands *before* the op (so aliasing `dst` with either
///   source, or a memory destination, needs no snapshots), then the op
///   runs and the branch tests `FLAGS`. `Or` clears OF on x86, so the
///   branch is never taken and only the op is emitted.
#[allow(clippy::too_many_arguments)]
fn e_opbranch(
    ctx: &mut LowerCtx,
    mn: &str,
    op: FlagAlu,
    w: Width,
    flag: PredFlag,
    args: &[Op],
    target: &offlineasm_ir::Lbl,
    patch: bool,
) -> Result<(), String> {
    let k = match op {
        FlagAlu::Add => AluKind::Add,
        FlagAlu::Sub => AluKind::Sub,
        FlagAlu::Mul => AluKind::Mul,
        FlagAlu::Or => AluKind::Or,
    };
    if w == Width::B8 || w == Width::B16 {
        return Err(format!(
            "riscv64: `{}`: op-branch is defined for 32- and 64-bit widths only",
            mn
        ));
    }
    let (a_op, b_op, dst_op) = match args {
        [rhs, dst] => (dst, rhs, dst),
        [lhs, rhs, dst] => (lhs, rhs, dst),
        _ => {
            return Err(format!(
                "riscv64: `{}`: expected 2 or 3 operands, got {}",
                mn,
                args.len()
            ));
        }
    };
    let t = text::label_text(ctx, *target)?;
    if flag == PredFlag::O {
        if k == AluKind::Or {
            return op_n(ctx, mn, k, w, args);
        }
        overflow_precheck(ctx, mn, k, w, a_op, b_op)?;
        op_n(ctx, mn, k, w, args)?;
        branch_zero(ctx, FLAGS, ZCond::Nez, &t, patch);
        return Ok(());
    }
    op_n(ctx, mn, k, w, args)?;
    let mut v = match dst_op {
        Op::Gpr(d) => *d,
        Op::Mem(m) => {
            e_load(ctx, mn, w, Sx::Sign, G1, m)?;
            G1
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: op-branch destination must be a register or memory",
                mn
            ));
        }
    };
    let cond = match flag {
        PredFlag::Z => ZCond::Eqz,
        PredFlag::Nz => ZCond::Nez,
        _ => ZCond::Ltz,
    };
    if cond == ZCond::Ltz && w == Width::B32 && matches!(dst_op, Op::Gpr(_)) {
        // The upper half of a `B32` result is unspecified (`or` and the
        // text emitter's ALU zero-extend, `addw` sign-extends). Test bit 31.
        ins!(ctx, "addiw {}, {}, 0", gpr(G1), gpr(v));
        v = G1;
    }
    branch_zero(ctx, v, cond, &t, patch);
    Ok(())
}

fn e_adc_sbb(ctx: &mut LowerCtx, mn: &str, dst: &Op, src: &Op, borrow: bool) -> Result<(), String> {
    ins!(ctx, "addi x2, x2, -48");
    ins!(ctx, "srli {}, {}, 2", gpr(G2), gpr(FLAGS));
    ins!(ctx, "andi {}, {}, 1", gpr(G2), gpr(G2));
    if borrow {
        ins!(ctx, "xori {}, {}, 1", gpr(G2), gpr(G2));
    }
    ins!(ctx, "sd {}, 16(x2)", gpr(G2));
    match src {
        Op::Gpr(s) => ins!(ctx, "sd {}, 8(x2)", gpr(*s)),
        Op::Imm(v) => {
            if !Width::B32.fits(*v) {
                return Err(format!(
                    "riscv64: `{}`: adc/sbb immediate must fit in 32 bits",
                    mn
                ));
            }
            mov_imm(ctx, G2, *v);
            ins!(ctx, "sd {}, 8(x2)", gpr(G2));
        }
        Op::Sym(s) => {
            mov_imm_sym(ctx, G2, *s)?;
            ins!(ctx, "sd {}, 8(x2)", gpr(G2));
        }
        Op::Mem(a) => {
            e_load(ctx, mn, Width::B64, Sx::Zero, G2, a)?;
            ins!(ctx, "sd {}, 8(x2)", gpr(G2));
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: adc/sbb needs register/memory operands",
                mn
            ));
        }
    }
    let r: Gpr = match dst {
        Op::Gpr(g) => {
            ins!(ctx, "sd {}, 0(x2)", gpr(*g));
            let d = gpr(*g);
            ins!(ctx, "ld {}, 8(x2)", gpr(G2));
            if borrow {
                ins!(ctx, "sub {}, {}, {}", d, d, gpr(G2));
            } else {
                ins!(ctx, "add {}, {}, {}", d, d, gpr(G2));
            }
            ins!(ctx, "ld {}, 16(x2)", gpr(G2));
            if borrow {
                ins!(ctx, "sub {}, {}, {}", d, d, gpr(G2));
            } else {
                ins!(ctx, "add {}, {}, {}", d, d, gpr(G2));
            }
            *g
        }
        Op::Mem(a) => {
            if a.index.is_some() || !fits_d12(a.disp.const_or_zero()) {
                return Err(format!(
                    "riscv64: `{}`: adc/sbb memory destination needs a directly encodable address",
                    mn
                ));
            }
            e_load(ctx, mn, Width::B64, Sx::Zero, G2, a)?;
            ins!(ctx, "sd {}, 0(x2)", gpr(G2));
            ins!(ctx, "ld {}, 8(x2)", gpr(G1));
            ins!(ctx, "ld {}, 16(x2)", gpr(G2));
            if borrow {
                ins!(ctx, "sub {}, {}, {}", gpr(G1), gpr(G1), gpr(G2));
            } else {
                ins!(ctx, "add {}, {}, {}", gpr(G1), gpr(G1), gpr(G2));
            }
            ins!(ctx, "ld {}, 8(x2)", gpr(G2));
            if borrow {
                ins!(ctx, "sub {}, {}, {}", gpr(G1), gpr(G1), gpr(G2));
            } else {
                ins!(ctx, "add {}, {}, {}", gpr(G1), gpr(G1), gpr(G2));
            }
            e_store(ctx, mn, Width::B64, &Op::Gpr(G1), a)?;
            G1
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: adc/sbb needs register/memory operands",
                mn
            ));
        }
    };
    derive_adc_sbb_64(ctx, borrow, r);
    ins!(ctx, "addi x2, x2, 48");
    Ok(())
}

fn derive_adc_sbb_64(ctx: &mut LowerCtx, sub: bool, r: Gpr) {
    let rr = gpr(r);
    let tmp = gpr(G2);
    let f = gpr(FLAGS);
    // V.
    ins!(ctx, "ld {}, 0(x2)", f);
    ins!(ctx, "ld {}, 8(x2)", tmp);
    ins!(ctx, "xor {}, {}, {}", f, f, tmp);
    if !sub {
        ins!(ctx, "xori {}, {}, -1", f, f);
    }
    ins!(ctx, "ld {}, 0(x2)", tmp);
    ins!(ctx, "xor {}, {}, {}", tmp, tmp, rr);
    ins!(ctx, "and {}, {}, {}", f, f, tmp);
    ins!(ctx, "srai {}, {}, 63", f, f);
    ins!(ctx, "andi {}, {}, 1", f, f);
    ins!(ctx, "slli {}, {}, 3", f, f);
    ins!(ctx, "sd {}, 24(x2)", f);
    // C / not-borrow.
    ins!(ctx, "ld {}, 16(x2)", tmp);
    if sub {
        ins!(ctx, "ld {}, 0(x2)", f);
        ins!(ctx, "ld {}, 8(x2)", tmp);
        ins!(ctx, "sltu {}, {}, {}", f, f, tmp);
        ins!(ctx, "sd {}, 32(x2)", f);
        ins!(ctx, "ld {}, 0(x2)", f);
        ins!(ctx, "ld {}, 8(x2)", tmp);
        ins!(ctx, "sub {}, {}, {}", f, f, tmp);
        ins!(ctx, "ld {}, 16(x2)", tmp);
        ins!(ctx, "sltu {}, {}, {}", f, f, tmp);
        ins!(ctx, "ld {}, 32(x2)", tmp);
        ins!(ctx, "or {}, {}, {}", f, f, tmp);
        ins!(ctx, "xori {}, {}, 1", f, f);
    } else {
        ins!(ctx, "ld {}, 0(x2)", f);
        ins!(ctx, "add {}, {}, {}", f, f, tmp);
        ins!(ctx, "sltu {}, {}, {}", tmp, f, tmp);
        ins!(ctx, "sltu {}, {}, {}", f, rr, f);
        ins!(ctx, "or {}, {}, {}", f, tmp, f);
    }
    ins!(ctx, "slli {}, {}, 2", f, f);
    ins!(ctx, "ld {}, 24(x2)", tmp);
    ins!(ctx, "or {}, {}, {}", f, f, tmp);
    // Z / N from the result.
    ins!(ctx, "seqz {}, {}", tmp, rr);
    ins!(ctx, "sd {}, 32(x2)", f);
    ins!(ctx, "slti {}, {}, 0", f, rr);
    ins!(ctx, "slli {}, {}, 1", f, f);
    ins!(ctx, "or {}, {}, {}", tmp, tmp, f);
    ins!(ctx, "ld {}, 32(x2)", f);
    ins!(ctx, "or {}, {}, {}", f, f, tmp);
}

fn e_jmp_call(
    ctx: &mut LowerCtx,
    mn: &str,
    target: &Target,
    patch: bool,
    is_call: bool,
) -> Result<(), String> {
    let _ = patch;
    match target {
        Target::Label(l) => {
            let t = text::label_text(ctx, *l)?;
            let line = if is_call {
                format!("call {}", t)
            } else {
                format!("j {}", t)
            };
            emit_link(ctx, &line, is_call);
            Ok(())
        }
        Target::Reg(g) => {
            let line = if is_call {
                format!("jalr x1, {}, 0", gpr(*g))
            } else {
                format!("jalr x0, {}, 0", gpr(*g))
            };
            emit_link(ctx, &line, is_call);
            Ok(())
        }
        Target::Mem(a) => {
            e_load(ctx, mn, Width::B64, Sx::Zero, G1, a)?;
            let line = if is_call {
                format!("jalr x1, {}, 0", gpr(G1))
            } else {
                format!("jalr x0, {}, 0", gpr(G1))
            };
            emit_link(ctx, &line, is_call);
            Ok(())
        }
        Target::Abs(v) => {
            mov_imm(ctx, G1, *v);
            let line = if is_call {
                format!("jalr x1, {}, 0", gpr(G1))
            } else {
                format!("jalr x0, {}, 0", gpr(G1))
            };
            emit_link(ctx, &line, is_call);
            Ok(())
        }
        Target::Extern(e) if e.reach == Reach::Near => {
            // `auipc` + `jalr` (`R_RISCV_CALL_PLT`). `jump` names the
            // scratch register itself, since `tail` would clobber `t1`.
            let sym = text::extern_text(ctx, e.id)?;
            let line = if is_call {
                format!("call {}", sym)
            } else {
                format!("jump {}, {}", sym, gpr(G1))
            };
            emit_link(ctx, &line, is_call);
            Ok(())
        }
        Target::Extern(e) => {
            e_extern_address(ctx, G1, *e)?;
            let line = if is_call {
                format!("jalr x1, {}, 0", gpr(G1))
            } else {
                format!("jalr x0, {}, 0", gpr(G1))
            };
            emit_link(ctx, &line, is_call);
            Ok(())
        }
    }
}

fn emit_link(ctx: &mut LowerCtx, line: &str, is_call: bool) {
    if is_call {
        ins!(ctx, "addi x2, x2, -16");
        ins!(ctx, "sd x1, 0(x2)");
        ins!(ctx, "{}", line);
        ins!(ctx, "ld x1, 0(x2)");
        ins!(ctx, "addi x2, x2, 16");
    } else {
        ins!(ctx, "{}", line);
    }
}

fn e_push_pop(ctx: &mut LowerCtx, mn: &str, op: &Op, push: bool) -> Result<(), String> {
    let g = match op {
        Op::Gpr(g) => *g,
        _ => {
            return Err(format!("riscv64: `{}`: push/pop needs a GPR operand", mn));
        }
    };
    if push {
        ins!(ctx, "addi x2, x2, -8");
        ins!(ctx, "sd {}, 0(x2)", gpr(g));
    } else {
        ins!(ctx, "ld {}, 0(x2)", gpr(g));
        ins!(ctx, "addi x2, x2, 8");
    }
    Ok(())
}

fn e_push_pop_v(ctx: &mut LowerCtx, mn: &str, op: &Op, push: bool) -> Result<(), String> {
    let f = match op {
        Op::Fpr(f) => *f,
        _ => {
            return Err(format!(
                "riscv64: `{}`: pushv/popv needs an FPR operand",
                mn
            ));
        }
    };
    let hi = fhi(f)?;
    if push {
        ins!(ctx, "addi x2, x2, -16");
        ins!(ctx, "fsd {}, 0(x2)", fpr(f));
        ins!(ctx, "fsd {}, 8(x2)", fpr(hi));
    } else {
        ins!(ctx, "fld {}, 0(x2)", fpr(f));
        ins!(ctx, "fld {}, 8(x2)", fpr(hi));
        ins!(ctx, "addi x2, x2, 16");
    }
    Ok(())
}

fn e_peek_poke(ctx: &mut LowerCtx, disp: i32, reg: Gpr, load: bool) {
    if fits_d12(disp) {
        if load {
            ins!(ctx, "ld {}, {}(x2)", gpr(reg), disp);
        } else {
            ins!(ctx, "sd {}, {}(x2)", gpr(reg), disp);
        }
        return;
    }
    mov_imm(ctx, G1, disp as i64);
    ins!(ctx, "add {}, {}, x2", gpr(G1), gpr(G1));
    if load {
        ins!(ctx, "ld {}, 0(x{})", gpr(reg), G1.0);
    } else {
        ins!(ctx, "sd {}, 0(x{})", gpr(reg), G1.0);
    }
}

fn e_cqo(ctx: &mut LowerCtx, quad: bool) {
    if quad {
        ins!(ctx, "srai {}, {}, 63", gpr(T2), gpr(T0));
    } else {
        ins!(ctx, "slli {}, {}, 32", gpr(T2), gpr(T0));
        ins!(ctx, "srai {}, {}, 32", gpr(T2), gpr(T2));
    }
}

/// `dst = lhs + (rhs << amount)`.
fn e_addshifted(
    ctx: &mut LowerCtx,
    mn: &str,
    dst: Gpr,
    lhs: Gpr,
    rhs: Gpr,
    amount: u8,
) -> Result<(), String> {
    if amount >= 64 {
        return Err(format!("riscv64: `{}`: shift amount out of range", mn));
    }
    ins!(ctx, "slli {}, {}, {}", gpr(dst), gpr(rhs), amount);
    ins!(ctx, "add {}, {}, {}", gpr(dst), gpr(lhs), gpr(dst));
    Ok(())
}

/// 32x32-to-64 multiply (`smulli`/`umulli`).
fn e_mulwide(ctx: &mut LowerCtx, signed: bool, dst: Gpr, lhs: Gpr, rhs: Gpr) -> Result<(), String> {
    let (a, b) = (gpr(G1), gpr(G2));
    ins!(ctx, "slli {}, {}, 32", a, gpr(lhs));
    ins!(ctx, "slli {}, {}, 32", b, gpr(rhs));
    if signed {
        ins!(ctx, "srai {}, {}, 32", a, a);
        ins!(ctx, "srai {}, {}, 32", b, b);
    } else {
        ins!(ctx, "srli {}, {}, 32", a, a);
        ins!(ctx, "srli {}, {}, 32", b, b);
    }
    ins!(ctx, "mul {}, {}, {}", gpr(dst), a, b);
    Ok(())
}

/// 64x64-to-128 multiply over the `t0`/`t2` pair.
fn e_mulhigh(ctx: &mut LowerCtx, mn: &str, signed: bool, rhs: &Op) -> Result<(), String> {
    let r = load_op_gpr(ctx, mn, rhs, Width::B64, G1)?;
    if signed {
        ins!(ctx, "mulh {}, {}, {}", gpr(T2), gpr(T0), gpr(r));
    } else {
        ins!(ctx, "mulhu {}, {}, {}", gpr(T2), gpr(T0), gpr(r));
    }
    ins!(ctx, "mul {}, {}, {}", gpr(T0), gpr(T0), gpr(r));
    Ok(())
}

fn e_divmod1(
    ctx: &mut LowerCtx,
    mn: &str,
    signed: bool,
    w: Width,
    divisor: &Op,
) -> Result<(), String> {
    if w != Width::B32 && w != Width::B64 {
        return Err(format!("riscv64: `{}`: div needs 32/64-bit widths", mn));
    }
    let dvs = match divisor {
        Op::Gpr(g) => *g,
        _ => {
            return Err(format!(
                "riscv64: `{}`: 1-op divide needs a register divisor",
                mn
            ));
        }
    };
    let trap = fresh(ctx);
    let done = fresh(ctx);
    if w == Width::B64 {
        ins!(ctx, "beq {}, x0, {}", gpr(dvs), trap);
    } else {
        ins!(ctx, "slli {}, {}, 32", gpr(G1), gpr(dvs));
        ins!(ctx, "srai {}, {}, 32", gpr(G1), gpr(G1));
        ins!(ctx, "beq {}, x0, {}", gpr(G1), trap);
    }
    if signed {
        let bound: i64 = if w == Width::B64 {
            i64::MIN
        } else {
            i32::MIN as i64
        };
        mov_imm(ctx, G1, bound);
        let no_trap = fresh(ctx);
        if w == Width::B64 {
            ins!(ctx, "bne {}, {}, {}", gpr(T0), gpr(G1), no_trap);
            ins!(ctx, "addi {}, x0, -1", gpr(G1));
            ins!(ctx, "bne {}, {}, {}", gpr(dvs), gpr(G1), no_trap);
        } else {
            ins!(ctx, "slli {}, {}, 32", gpr(G2), gpr(T0));
            ins!(ctx, "srai {}, {}, 32", gpr(G2), gpr(G2));
            ins!(ctx, "bne {}, {}, {}", gpr(G2), gpr(G1), no_trap);
            ins!(ctx, "slli {}, {}, 32", gpr(G2), gpr(dvs));
            ins!(ctx, "srai {}, {}, 32", gpr(G2), gpr(G2));
            ins!(ctx, "addi {}, x0, -1", gpr(G1));
            ins!(ctx, "bne {}, {}, {}", gpr(G2), gpr(G1), no_trap);
        }
        ins!(ctx, "j {}", trap);
        bind(ctx, &no_trap);
    }
    mov_reg(ctx, G1, T0, if w == Width::B64 { w } else { Width::B32 });
    let op = match (w == Width::B64, signed) {
        (true, true) => "div",
        (true, false) => "divu",
        (false, true) => "divw",
        (false, false) => "divuw",
    };
    let rem = match (w == Width::B64, signed) {
        (true, true) => "rem",
        (true, false) => "remu",
        (false, true) => "remw",
        (false, false) => "remuw",
    };
    ins!(ctx, "{} {}, {}, {}", op, gpr(T0), gpr(T0), gpr(dvs));
    ins!(ctx, "{} {}, {}, {}", rem, gpr(T2), gpr(G1), gpr(dvs));
    ins!(ctx, "j {}", done);
    bind(ctx, &trap);
    ins!(ctx, "ebreak");
    bind(ctx, &done);
    Ok(())
}

/// `Cmov`: `dst = src` when `test` is nonzero (or zero, for `zero`).
fn e_cmov(
    ctx: &mut LowerCtx,
    mn: &str,
    w: Width,
    zero: bool,
    dst: Gpr,
    src: &Op,
    test: Gpr,
) -> Result<(), String> {
    let done = fresh(ctx);
    if zero {
        ins!(ctx, "bne {}, x0, {}", gpr(test), done);
    } else {
        ins!(ctx, "beq {}, x0, {}", gpr(test), done);
    }
    match src {
        Op::Gpr(g) => mov_reg(ctx, dst, *g, w),
        Op::Imm(v) => mov_imm_w(ctx, dst, w, *v),
        Op::Sym(s) => {
            mov_imm_sym(ctx, dst, *s)?;
            if w == Width::B32 {
                zero_upper32(ctx, dst);
            }
        }
        Op::Mem(a) => {
            let lw = if w == Width::B64 { w } else { Width::B32 };
            e_load(ctx, mn, lw, Sx::Zero, dst, a)?;
        }
        _ => {
            return Err(format!(
                "riscv64: `{}`: cmov needs a register, immediate, or memory source",
                mn
            ));
        }
    }
    bind(ctx, &done);
    Ok(())
}
