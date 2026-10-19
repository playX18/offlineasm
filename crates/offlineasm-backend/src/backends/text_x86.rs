use super::text::{self, TextTarget};
use super::LowerCtx;
use offlineasm_ir::{
    Alu3, AluOp, AtomicOp, BitcastDir, Disp, ExternId, FAlu, FCc, FKind, FlagAlu, FmaOp, Fpr, Gpr,
    Inst, IntCc, Lbl, LeaSrc, Mem, Op, PairW, PredFlag, Reach, RoundMode, ShiftCnt, ShiftOp, Sx,
    Target, TestKind, Width,
};

fn scratch_gpr() -> Gpr {
    TextTarget::X86_64.scratch().gpr
}

fn scratch_fpr() -> Fpr {
    TextTarget::X86_64.scratch().fpr
}

const LOW_GPR_NAMES: [[&str; 4]; 8] = [
    ["al", "ax", "eax", "rax"],
    ["cl", "cx", "ecx", "rcx"],
    ["dl", "dx", "edx", "rdx"],
    ["bl", "bx", "ebx", "rbx"],
    ["spl", "sp", "esp", "rsp"],
    ["bpl", "bp", "ebp", "rbp"],
    ["sil", "si", "esi", "rsi"],
    ["dil", "di", "edi", "rdi"],
];

fn gpr_text(g: Gpr, w: Width) -> Result<String, String> {
    let width = match w {
        Width::B8 => 0,
        Width::B16 => 1,
        Width::B32 => 2,
        Width::B64 => 3,
    };
    match g.0 {
        0..=7 => Ok(LOW_GPR_NAMES[g.0 as usize][width].to_string()),
        8..=15 => Ok(match w {
            Width::B8 => format!("r{}b", g.0),
            Width::B16 => format!("r{}w", g.0),
            Width::B32 => format!("r{}d", g.0),
            Width::B64 => format!("r{}", g.0),
        }),
        id => Err(format!("x86: bad GPR id {id}")),
    }
}

fn fpr_text(x: Fpr) -> Result<String, String> {
    if x.0 < 16 {
        Ok(format!("xmm{}", x.0))
    } else {
        Err(format!("x86: bad FPR id {}", x.0))
    }
}

fn size_keyword(w: Width) -> &'static str {
    match w {
        Width::B8 => "byte ptr ",
        Width::B16 => "word ptr ",
        Width::B32 => "dword ptr ",
        Width::B64 => "qword ptr ",
    }
}

const XMMWORD: &str = "xmmword ptr ";

fn offset_term_text(v: i64) -> String {
    if v > 0 {
        format!(" + {}", v)
    } else if v < 0 {
        format!(" - {}", -v)
    } else {
        String::new()
    }
}

fn mem_text(ctx: &LowerCtx, m: &Mem, size: Option<&str>, extra: i64) -> Result<String, String> {
    let mut terms: Vec<String> = Vec::new();
    if let Some(b) = m.base {
        terms.push(gpr_text(b, Width::B64)?);
    }
    if let Some((i, scale)) = m.index {
        let index = gpr_text(i, Width::B64)?;
        if scale == 1 {
            terms.push(index);
        } else {
            terms.push(format!("{}*{}", index, scale));
        }
    }
    let disp = match m.disp {
        Disp::Const(v) => {
            let v = i64::from(v).wrapping_add(extra);
            if v == 0 && !terms.is_empty() {
                String::new()
            } else {
                imm_text(v)
            }
        }
        Disp::Sym(s) => {
            let mut t = text::sym_text(ctx, s)?;
            t.push_str(&offset_term_text(extra));
            t
        }
    };
    if terms.is_empty() && disp.is_empty() {
        return Err("x86: empty memory operand".to_string());
    }
    let mut inner = String::new();
    for term in &terms {
        if !inner.is_empty() {
            inner.push_str(" + ");
        }
        inner.push_str(term);
    }
    if !disp.is_empty() {
        if inner.is_empty() {
            inner = disp;
        } else if let Some(rest) = disp.strip_prefix('-') {
            inner.push_str(" - ");
            inner.push_str(rest);
        } else {
            inner.push_str(" + ");
            inner.push_str(&disp);
        }
    }
    Ok(format!("{}[{}]", size.unwrap_or(""), inner))
}

/// `[base]`, `[base + n]`, or `[base - n]`.
fn base_disp_text(base: &str, disp: i64) -> String {
    format!("[{}{}]", base, offset_term_text(disp))
}

fn imm_text(v: i64) -> String {
    v.to_string()
}

fn hex_imm(v: i64) -> String {
    format!("0x{:x}", v as u64)
}

fn imm_encodable(w: Width, v: i64) -> bool {
    match w {
        Width::B8 => (-128..=255).contains(&v),
        Width::B16 => (-32768..=65535).contains(&v),
        Width::B32 => (i32::MIN as i64..=u32::MAX as i64).contains(&v),
        Width::B64 => Width::B32.fits(v),
    }
}

fn load_scratch_imm(ctx: &mut LowerCtx, v: i64) -> Result<(), String> {
    let scratch = gpr_text(scratch_gpr(), Width::B64)?;
    if Width::B32.fits(v) {
        puts(ctx, &format!("mov {}, {}", scratch, imm_text(v)));
    } else {
        puts(ctx, &format!("movabs {}, {}", scratch, hex_imm(v)));
    }
    Ok(())
}

fn op_text(ctx: &LowerCtx, op: &Op, w: Width) -> Result<String, String> {
    match op {
        Op::Imm(v) => Ok(imm_text(*v)),
        Op::Gpr(g) => gpr_text(*g, w),
        Op::Fpr(x) => fpr_text(*x),
        Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(w)), 0),
        Op::Sym(s) => text::sym_text(ctx, *s),
        Op::Label(l) => Err(format!(
            "x86: label `{}` is only valid as a branch target or address source",
            text::label_text(ctx, *l)?
        )),
        Op::Extern(_) => Err(text::extern_operand_error()),
    }
}

fn fp_src_text(ctx: &LowerCtx, k: FKind, op: &Op) -> Result<String, String> {
    match op {
        Op::Fpr(x) => fpr_text(*x),
        Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(fk_width(k))), 0),
        Op::Sym(s) => text::sym_text(ctx, *s),
        _ => Err("x86: float operation needs a register or memory operand".to_string()),
    }
}

fn puts(ctx: &mut LowerCtx, line: &str) {
    ctx.emitter.puts(line);
}

fn fk_suffix(k: FKind) -> &'static str {
    match k {
        FKind::F32 => "ss",
        FKind::F64 => "sd",
    }
}

fn fk_width(k: FKind) -> Width {
    match k {
        FKind::F32 => Width::B32,
        FKind::F64 => Width::B64,
    }
}

fn fk_mov(k: FKind) -> &'static str {
    match k {
        FKind::F32 => "movss",
        FKind::F64 => "movsd",
    }
}

pub fn emit(ctx: &mut LowerCtx, inst: &Inst) -> Result<(), String> {
    match inst {
        Inst::Mov {
            w,
            dst,
            src,
            patch: _,
        } => mov(ctx, *w, dst, src),
        Inst::MovZero32 { dst, src } => mov(ctx, Width::B32, dst, src),
        Inst::Bind(l) => {
            let name = text::label_text(ctx, *l)?;
            puts(ctx, &format!("{}:", name));
            Ok(())
        }
        Inst::Bswap { w, dst, src } => bswap(ctx, *w, dst, src),
        // x86-64 loads are already acquire under TSO, so `acquire` needs no
        // extra instruction here (see `Inst::Load`'s doc comment).
        Inst::Load {
            w,
            sx,
            dst,
            addr,
            acquire: _,
        } => load(ctx, *w, *sx, *dst, addr),
        Inst::Store { w, src, addr } => store(ctx, *w, src, addr),
        Inst::LoadF { k, dst, addr } => {
            let d = fpr_text(*dst)?;
            let a = mem_text(ctx, addr, Some(size_keyword(fk_width(*k))), 0)?;
            puts(ctx, &format!("{} {}, {}", fk_mov(*k), d, a));
            Ok(())
        }
        Inst::StoreF { k, src, addr } => {
            let s = fpr_text(*src)?;
            let a = mem_text(ctx, addr, Some(size_keyword(fk_width(*k))), 0)?;
            puts(ctx, &format!("{} {}, {}", fk_mov(*k), a, s));
            Ok(())
        }
        Inst::FMov { k, dst, src } => {
            let (d, s) = (fpr_text(*dst)?, fpr_text(*src)?);
            puts(ctx, &format!("{} {}, {}", fk_mov(*k), d, s));
            Ok(())
        }
        Inst::LoadV { dst, addr } => {
            let d = fpr_text(*dst)?;
            let a = mem_text(ctx, addr, Some(XMMWORD), 0)?;
            puts(ctx, &format!("movdqu {}, {}", d, a));
            Ok(())
        }
        Inst::StoreV { src, addr } => {
            let s = fpr_text(*src)?;
            let a = mem_text(ctx, addr, Some(XMMWORD), 0)?;
            puts(ctx, &format!("movups {}, {}", a, s));
            Ok(())
        }
        Inst::VMov { dst, src } => {
            let (d, s) = (fpr_text(*dst)?, fpr_text(*src)?);
            puts(ctx, &format!("movdqu {}, {}", d, s));
            Ok(())
        }
        Inst::Lea { w, dst, src } => lea(ctx, *w, *dst, src),
        Inst::Push { op } => push(ctx, op),
        Inst::Pop { op } => pop(ctx, op),
        Inst::PushV { src } => {
            let s = fpr_text(*src)?;
            puts(ctx, "sub rsp, 16");
            puts(ctx, &format!("movdqu {}[rsp], {}", XMMWORD, s));
            Ok(())
        }
        Inst::PopV { dst } => {
            let d = fpr_text(*dst)?;
            puts(ctx, &format!("movdqu {}, {}[rsp]", d, XMMWORD));
            puts(ctx, "add rsp, 16");
            Ok(())
        }
        Inst::Peek { disp, dst } => {
            let d = gpr_text(*dst, Width::B64)?;
            puts(
                ctx,
                &format!("mov {}, {}", d, base_disp_text("rsp", i64::from(*disp))),
            );
            Ok(())
        }
        Inst::Poke { disp, src } => {
            let s = gpr_text(*src, Width::B64)?;
            puts(
                ctx,
                &format!("mov {}, {}", base_disp_text("rsp", i64::from(*disp)), s),
            );
            Ok(())
        }
        Inst::Add { w, op } => add3(ctx, *w, op),
        Inst::Sub { w, op } => bin3(ctx, Bin::Sub, *w, op),
        Inst::Mul { w, op } => mul3(ctx, *w, op),
        Inst::And { w, op } => bin3(ctx, Bin::And, *w, op),
        Inst::Or { w, op } => bin3(ctx, Bin::Or, *w, op),
        Inst::Xor { w, op } => bin3(ctx, Bin::Xor, *w, op),
        Inst::Not { w, dst } => unop(ctx, "not", *w, dst),
        Inst::Neg { w, dst } => unop(ctx, "neg", *w, dst),
        Inst::Shift { w, op, dst, cnt } => shift(ctx, *w, *op, *dst, cnt),
        Inst::MulImm { w, dst, lhs, imm } => mul_imm(ctx, *w, *dst, *lhs, *imm),
        Inst::AluS { op, w, alu } => match op {
            AluOp::Add => flag_bin3(ctx, Bin::Add, *w, alu),
            AluOp::Sub => flag_bin3(ctx, Bin::Sub, *w, alu),
            AluOp::Or => flag_bin3(ctx, Bin::Or, *w, alu),
        },
        Inst::Adc { dst, src } => bin2_text(ctx, "adc", Width::B64, dst, src),
        Inst::Sbb { dst, src } => bin2_text(ctx, "sbb", Width::B64, dst, src),
        Inst::MulWide {
            signed,
            dst,
            lhs,
            rhs,
        } => mul_wide(ctx, *signed, *dst, *lhs, *rhs),
        Inst::MulHigh { signed, rhs } => mul_high(ctx, *signed, rhs),
        Inst::DivMod1 { signed, w, divisor } => div_mod1(ctx, *signed, *w, divisor),
        Inst::Div3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        } => div3(ctx, *signed, *w, *dst, dvd, dvs, false),
        Inst::Rem3 {
            signed,
            w,
            dst,
            dvd,
            dvs,
        } => div3(ctx, *signed, *w, *dst, dvd, dvs, true),
        Inst::Extend {
            from,
            to,
            sx,
            dst,
            src,
        } => extend(ctx, *from, *to, *sx, *dst, src),
        Inst::Ctz { w, dst, src } => count_zeros(ctx, *w, *dst, src, true),
        Inst::Clz { w, dst, src } => count_zeros(ctx, *w, *dst, src, false),
        Inst::Popcnt { w, dst, src } => popcnt(ctx, *w, *dst, src),
        Inst::Cqo { quad } => {
            puts(ctx, if *quad { "cqo" } else { "cdq" });
            Ok(())
        }
        Inst::AddShifted {
            dst,
            lhs,
            rhs,
            amount,
        } => add_shifted(ctx, *dst, *lhs, *rhs, *amount),
        Inst::Cmov {
            w,
            zero,
            dst,
            src,
            test,
        } => cmov(ctx, *w, *zero, *dst, src, *test),
        Inst::VecExtract { w, dst, src, lane } => vec_extract(ctx, *w, *dst, *src, *lane),

        // Branches, sets, control flow.
        Inst::Branch {
            cc,
            w,
            lhs,
            rhs,
            target,
            patch: _,
        } => {
            int_compare(ctx, *cc, *w, lhs, rhs)?;
            let label = text::label_text(ctx, *target)?;
            puts(ctx, &format!("{} {}", int_jcc(*cc), label));
            Ok(())
        }
        Inst::TestBranch {
            w,
            value,
            mask,
            test,
            target,
            patch: _,
        } => {
            test_flags(ctx, *w, value, mask.as_ref())?;
            let label = text::label_text(ctx, *target)?;
            puts(ctx, &format!("{} {}", test_jcc(*test), label));
            Ok(())
        }
        Inst::OpBranch {
            op,
            w,
            flag,
            args,
            target,
            patch: _,
        } => {
            op_branch(ctx, *op, *w, *flag, args.as_slice())?;
            let label = text::label_text(ctx, *target)?;
            puts(ctx, &format!("{} {}", flag_jcc(*flag), label));
            Ok(())
        }
        Inst::FlagBranch {
            flag,
            target,
            patch: _,
        } => {
            let label = text::label_text(ctx, *target)?;
            puts(ctx, &format!("{} {}", flag_jcc(*flag), label));
            Ok(())
        }
        Inst::Jump { target, patch: _ } => jump(ctx, target, false),
        Inst::Call { target, patch: _ } => jump(ctx, target, true),
        Inst::Ret => {
            puts(ctx, "ret");
            Ok(())
        }
        Inst::Break => {
            puts(ctx, "int3");
            Ok(())
        }
        Inst::Nop => {
            puts(ctx, "nop");
            Ok(())
        }
        Inst::IntSet {
            cc,
            w,
            dst,
            lhs,
            rhs,
        } => {
            int_compare(ctx, *cc, *w, lhs, rhs)?;
            set_zx(ctx, int_setcc(*cc), dst)
        }
        Inst::TestSet {
            w,
            value,
            mask,
            test,
            dst,
        } => {
            test_flags(ctx, *w, value, mask.as_ref())?;
            set_zx(ctx, test_setcc(*test), dst)
        }

        // Float.
        Inst::FArith { op, k, arith } => farith(ctx, *op, *k, arith),
        Inst::Fma {
            op,
            k,
            a,
            b,
            c,
            dst,
        } => fma(ctx, *op, *k, a, b, c, *dst),
        Inst::FSqrt { k, dst, src } => {
            let d = fpr_text(*dst)?;
            let s = fp_src_text(ctx, *k, src)?;
            puts(ctx, &format!("sqrt{} {}, {}", fk_suffix(*k), d, s));
            Ok(())
        }
        Inst::FRound { k, mode, dst, src } => {
            let d = fpr_text(*dst)?;
            let s = fp_src_text(ctx, *k, src)?;
            puts(
                ctx,
                &format!("round{} {}, {}, {}", fk_suffix(*k), d, s, round_imm(*mode)),
            );
            Ok(())
        }
        Inst::FAbs { k, dst, src } => fp_sign(ctx, *k, *dst, src, false),
        Inst::FNeg { k, dst, src } => fp_sign(ctx, *k, *dst, src, true),
        Inst::FBit { or, k, dst, src } => {
            let d = fpr_text(*dst)?;
            let s = fp_src_text(ctx, *k, src)?;
            let mnemonic = match (*or, *k) {
                (false, FKind::F32) => "andps",
                (false, FKind::F64) => "andpd",
                (true, FKind::F32) => "orps",
                (true, FKind::F64) => "orpd",
            };
            puts(ctx, &format!("{} {}, {}", mnemonic, d, s));
            Ok(())
        }
        Inst::CvtFI { k, w, dst, src } => {
            let d = gpr_text(*dst, *w)?;
            let s = fp_src_text(ctx, *k, src)?;
            puts(ctx, &format!("cvtt{}2si {}, {}", fk_suffix(*k), d, s));
            Ok(())
        }
        Inst::CvtIF {
            signed,
            from,
            k,
            dst,
            src,
        } => {
            if !*signed {
                return Err("x86: unsigned int-to-float uses the shared slow path".to_string());
            }
            let d = fpr_text(*dst)?;
            let s = match src {
                Op::Gpr(g) => gpr_text(*g, *from)?,
                Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(*from)), 0)?,
                _ => return Err("x86: int-to-float needs a register or memory source".to_string()),
            };
            puts(ctx, &format!("cvtsi2{} {}, {}", fk_suffix(*k), d, s));
            Ok(())
        }
        Inst::CvtFF { from, to, dst, src } => {
            let d = fpr_text(*dst)?;
            let s = fp_src_text(ctx, *from, src)?;
            puts(
                ctx,
                &format!("cvt{}2{} {}, {}", fk_suffix(*from), fk_suffix(*to), d, s),
            );
            Ok(())
        }
        Inst::Bitcast { dir, dst, src } => bitcast(ctx, *dir, dst, src),
        Inst::BranchF {
            cc,
            k,
            lhs,
            rhs,
            target,
            patch: _,
        } => branch_f(ctx, *cc, *k, lhs, rhs, *target),
        Inst::FSet {
            cc,
            k,
            dst,
            lhs,
            rhs,
        } => fset(ctx, *cc, *k, dst, lhs, rhs),

        // Misc.
        Inst::Fence { full: _ } => {
            puts(ctx, "lock or dword ptr [rsp], 0");
            Ok(())
        }
        Inst::Pause => {
            puts(ctx, "pause");
            Ok(())
        }
        Inst::TlsLoad { w, dst, idx } => tls(ctx, *w, *dst, *idx, true),
        Inst::TlsStore { w, src, idx } => tls(ctx, *w, *src, *idx, false),
        Inst::TlsLea { dst, idx } => tls_lea(ctx, *dst, *idx),
        Inst::AtomicRmw { op, w, a, b } => atomic_rmw(ctx, *op, *w, a, b),
        Inst::AtomicCas {
            w,
            mem,
            src,
            branch,
        } => atomic_cas(ctx, *w, mem, *src, *branch),
        Inst::LoadLinked { w, mem, dst } => {
            let d = gpr_text(*dst, *w)?;
            let a = mem_text(ctx, mem, Some(size_keyword(*w)), 0)?;
            puts(ctx, &format!("mov {}, {}", d, a));
            // A 16-bit `mov` does not zero-extend on x86-64 (unlike 32-bit).
            // Match `loadi`/`loadh`'s zero-extending semantics for the
            // linked value's container.
            zero_extend_result(ctx, *dst, *w)?;
            Ok(())
        }
        Inst::StoreCond {
            w,
            status,
            src,
            mem,
        } => store_cond(ctx, *w, *status, *src, mem),
        Inst::PairLoad { w, dst1, dst2, mem } => pair(ctx, *w, dst1, dst2, mem, true),
        Inst::PairStore { w, src1, src2, mem } => pair(ctx, *w, src1, src2, mem, false),
    }
}

fn mov(ctx: &mut LowerCtx, w: Width, dst: &Op, src: &Op) -> Result<(), String> {
    match (dst, src) {
        (Op::Gpr(d), Op::Gpr(s)) => {
            if d == s && w != Width::B32 {
                return Ok(());
            }
            let (d, s) = (gpr_text(*d, w)?, gpr_text(*s, w)?);
            puts(ctx, &format!("mov {}, {}", d, s));
            Ok(())
        }
        (Op::Gpr(d), Op::Imm(v)) => mov_imm(ctx, *d, w, *v),
        (Op::Gpr(d), Op::Mem(m)) => {
            let d = gpr_text(*d, w)?;
            let s = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("mov {}, {}", d, s));
            Ok(())
        }
        (Op::Gpr(d), Op::Label(l)) => {
            let d = gpr_text(*d, w)?;
            let l = text::label_text(ctx, *l)?;
            puts(ctx, &format!("lea {}, [rip + {}]", d, l));
            Ok(())
        }
        (Op::Gpr(d), Op::Sym(s)) => {
            let d = gpr_text(*d, w)?;
            let s = text::sym_text(ctx, *s)?;
            puts(ctx, &format!("mov {}, {}", d, s));
            Ok(())
        }
        (Op::Mem(m), _) => store(ctx, w, src, m),
        (Op::Gpr(_), Op::Fpr(_)) | (Op::Fpr(_), _) => Err(
            "x86: register-class moves use the bit-cast mnemonics (`fq2d`/`fd2q`/`fi2f`/`ff2i`)"
                .to_string(),
        ),
        _ => Err("x86: unsupported `mov` operand pair".to_string()),
    }
}

fn mov_imm(ctx: &mut LowerCtx, d: Gpr, w: Width, v: i64) -> Result<(), String> {
    let dst = gpr_text(d, w)?;
    if w == Width::B64 && !Width::B32.fits(v) {
        puts(ctx, &format!("movabs {}, {}", dst, hex_imm(v)));
    } else {
        puts(ctx, &format!("mov {}, {}", dst, imm_text(truncate(v, w))));
    }
    Ok(())
}

fn truncate(v: i64, w: Width) -> i64 {
    match w {
        Width::B8 => i64::from(v as i8),
        Width::B16 => i64::from(v as i16),
        Width::B32 => i64::from(v as i32),
        Width::B64 => v,
    }
}

fn tls_offset(idx: i64) -> Result<i64, String> {
    idx.checked_mul(8)
        .filter(|off| Width::B32.fits(*off))
        .ok_or_else(|| format!("x86: tls index {} is out of range", idx))
}

fn store(ctx: &mut LowerCtx, w: Width, src: &Op, m: &Mem) -> Result<(), String> {
    let addr = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
    match src {
        Op::Gpr(s) => {
            let s = gpr_text(*s, w)?;
            puts(ctx, &format!("mov {}, {}", addr, s));
            Ok(())
        }
        Op::Imm(v) if imm_encodable(w, *v) => {
            puts(ctx, &format!("mov {}, {}", addr, imm_text(*v)));
            Ok(())
        }
        Op::Imm(v) => {
            load_scratch_imm(ctx, *v)?;
            let s = gpr_text(scratch_gpr(), w)?;
            puts(ctx, &format!("mov {}, {}", addr, s));
            Ok(())
        }
        Op::Sym(s) => {
            let s = text::sym_text(ctx, *s)?;
            puts(ctx, &format!("mov {}, {}", addr, s));
            Ok(())
        }
        Op::Label(l) => {
            let scratch64 = gpr_text(scratch_gpr(), Width::B64)?;
            let l = text::label_text(ctx, *l)?;
            puts(ctx, &format!("lea {}, [rip + {}]", scratch64, l));
            let s = gpr_text(scratch_gpr(), w)?;
            puts(ctx, &format!("mov {}, {}", addr, s));
            Ok(())
        }
        Op::Extern(_) => Err(text::extern_operand_error()),
        Op::Mem(s) => {
            let scratch = gpr_text(scratch_gpr(), w)?;
            let s = mem_text(ctx, s, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("mov {}, {}", scratch, s));
            puts(ctx, &format!("mov {}, {}", addr, scratch));
            Ok(())
        }
        Op::Fpr(_) => Err("x86: cannot store a float register as an integer".to_string()),
    }
}

fn bswap(ctx: &mut LowerCtx, w: Width, dst: &Op, src: &Op) -> Result<(), String> {
    let (Op::Gpr(d), Op::Gpr(s)) = (dst, src) else {
        return Err("x86: `bswap` needs general-purpose registers".to_string());
    };
    if w != Width::B32 && w != Width::B64 {
        return Err("x86: `bswap` needs a 32- or 64-bit width".to_string());
    }
    if d != s {
        let (dt, st) = (gpr_text(*d, w)?, gpr_text(*s, w)?);
        puts(ctx, &format!("mov {}, {}", dt, st));
    }
    let d = gpr_text(*d, w)?;
    puts(ctx, &format!("bswap {}", d));
    Ok(())
}

fn load(ctx: &mut LowerCtx, w: Width, sx: Sx, dst: Gpr, addr: &Mem) -> Result<(), String> {
    let extending = match (w, sx) {
        (Width::B64, _) | (Width::B32, Sx::Zero) => None,
        (Width::B32, Sx::Sign) => Some(("movsxd", Width::B64)),
        (Width::B16, Sx::Zero) => Some(("movzx", Width::B32)),
        (Width::B16, Sx::Sign) => Some(("movsx", Width::B64)),
        (Width::B8, Sx::Zero) => Some(("movzx", Width::B32)),
        (Width::B8, Sx::Sign) => Some(("movsx", Width::B64)),
    };
    let addr = mem_text(ctx, addr, Some(size_keyword(w)), 0)?;
    match extending {
        Some((mnemonic, to)) => {
            let d = gpr_text(dst, to)?;
            puts(ctx, &format!("{} {}, {}", mnemonic, d, addr));
        }
        None => {
            let d = gpr_text(dst, w)?;
            puts(ctx, &format!("mov {}, {}", d, addr));
        }
    }
    Ok(())
}

fn lea(ctx: &mut LowerCtx, w: Width, dst: Gpr, src: &LeaSrc) -> Result<(), String> {
    if w != Width::B32 && w != Width::B64 {
        return Err("x86: `lea` needs a 32- or 64-bit width".to_string());
    }
    let d = gpr_text(dst, w)?;
    match src {
        LeaSrc::Mem(m) => {
            let m = mem_text(ctx, m, None, 0)?;
            puts(ctx, &format!("lea {}, {}", d, m));
        }
        LeaSrc::Label(l) => {
            let l = text::label_text(ctx, *l)?;
            puts(ctx, &format!("lea {}, [rip + {}]", d, l));
        }
        LeaSrc::Extern(e) => match e.reach {
            Reach::Near => {
                let sym = text::extern_text(ctx, e.id)?;
                puts(ctx, &format!("lea {}, [rip + {}]", d, sym));
            }
            Reach::Far => {
                let slot = extern_slot_mem(ctx, e.id)?;
                puts(ctx, &format!("mov {}, {}", d, slot));
            }
        },
    }
    Ok(())
}

fn extern_slot_mem(ctx: &mut LowerCtx, e: ExternId) -> Result<String, String> {
    if ctx.coff() {
        let slot = text::extern_slot(ctx, e)?;
        Ok(format!("qword ptr [rip + {}]", slot))
    } else {
        let sym = text::extern_text(ctx, e)?;
        Ok(format!("qword ptr [rip + {}@GOTPCREL]", sym))
    }
}

fn push(ctx: &mut LowerCtx, op: &Op) -> Result<(), String> {
    match op {
        Op::Gpr(g) => {
            let g = gpr_text(*g, Width::B64)?;
            puts(ctx, &format!("push {}", g));
            Ok(())
        }
        Op::Mem(m) => {
            let m = mem_text(ctx, m, Some(size_keyword(Width::B64)), 0)?;
            puts(ctx, &format!("push {}", m));
            Ok(())
        }
        Op::Imm(v) if Width::B32.fits(*v) => {
            puts(ctx, &format!("push {}", imm_text(*v)));
            Ok(())
        }
        Op::Imm(v) => {
            load_scratch_imm(ctx, *v)?;
            let s = gpr_text(scratch_gpr(), Width::B64)?;
            puts(ctx, &format!("push {}", s));
            Ok(())
        }
        Op::Sym(s) => {
            let s = text::sym_text(ctx, *s)?;
            puts(ctx, &format!("push {}", s));
            Ok(())
        }
        Op::Extern(_) => Err(text::extern_operand_error()),
        Op::Label(l) => {
            let scratch = gpr_text(scratch_gpr(), Width::B64)?;
            let l = text::label_text(ctx, *l)?;
            puts(ctx, &format!("lea {}, [rip + {}]", scratch, l));
            puts(ctx, &format!("push {}", scratch));
            Ok(())
        }
        Op::Fpr(_) => Err("x86: cannot `push` a float register".to_string()),
    }
}

fn pop(ctx: &mut LowerCtx, op: &Op) -> Result<(), String> {
    match op {
        Op::Gpr(g) => {
            let g = gpr_text(*g, Width::B64)?;
            puts(ctx, &format!("pop {}", g));
            Ok(())
        }
        Op::Mem(m) => {
            let m = mem_text(ctx, m, Some(size_keyword(Width::B64)), 0)?;
            puts(ctx, &format!("pop {}", m));
            Ok(())
        }
        _ => Err("x86: `pop` needs a register or memory operand".to_string()),
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Bin {
    Add,
    Sub,
    And,
    Or,
    Xor,
}

impl Bin {
    fn mnemonic(self) -> &'static str {
        match self {
            Bin::Add => "add",
            Bin::Sub => "sub",
            Bin::And => "and",
            Bin::Or => "or",
            Bin::Xor => "xor",
        }
    }

    fn commutative(self) -> bool {
        self != Bin::Sub
    }
}

fn bin2_text(
    ctx: &mut LowerCtx,
    mnemonic: &str,
    w: Width,
    dst: &Op,
    src: &Op,
) -> Result<(), String> {
    match (dst, src) {
        (Op::Gpr(d), Op::Gpr(s)) => {
            let (d, s) = (gpr_text(*d, w)?, gpr_text(*s, w)?);
            puts(ctx, &format!("{} {}, {}", mnemonic, d, s));
            Ok(())
        }
        (Op::Gpr(d), Op::Mem(m)) => {
            let d = gpr_text(*d, w)?;
            let s = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("{} {}, {}", mnemonic, d, s));
            Ok(())
        }
        (Op::Gpr(d), Op::Imm(v)) => {
            let d = gpr_text(*d, w)?;
            if imm_encodable(w, *v) {
                puts(ctx, &format!("{} {}, {}", mnemonic, d, imm_text(*v)));
                return Ok(());
            }
            load_scratch_imm(ctx, *v)?;
            let s = gpr_text(scratch_gpr(), w)?;
            puts(ctx, &format!("{} {}, {}", mnemonic, d, s));
            Ok(())
        }
        (Op::Gpr(d), Op::Sym(s)) => {
            let d = gpr_text(*d, w)?;
            let s = text::sym_text(ctx, *s)?;
            puts(ctx, &format!("{} {}, {}", mnemonic, d, s));
            Ok(())
        }
        (Op::Mem(m), src) => {
            let addr = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            let op = bin_source_text(ctx, mnemonic, w, src)?;
            puts(ctx, &format!("{} {}, {}", mnemonic, addr, op));
            Ok(())
        }
        (Op::Imm(_), _) | (Op::Label(_), _) | (Op::Sym(_), _) | (Op::Fpr(_), _) => Err(format!(
            "x86: `{}` needs a register or memory destination",
            mnemonic
        )),
        (Op::Gpr(_), Op::Fpr(_)) | (Op::Gpr(_), Op::Label(_)) => {
            Err(format!("x86: `{}` needs an integer source", mnemonic))
        }
        (Op::Extern(_), _) | (_, Op::Extern(_)) => Err(text::extern_operand_error()),
    }
}

fn bin_source_text(
    ctx: &mut LowerCtx,
    mnemonic: &str,
    w: Width,
    src: &Op,
) -> Result<String, String> {
    match src {
        Op::Gpr(g) => gpr_text(*g, w),
        Op::Imm(v) if imm_encodable(w, *v) => Ok(imm_text(*v)),
        Op::Imm(v) => {
            load_scratch_imm(ctx, *v)?;
            gpr_text(scratch_gpr(), w)
        }
        Op::Mem(m) => {
            let scratch = gpr_text(scratch_gpr(), w)?;
            let s = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("mov {}, {}", scratch, s));
            Ok(scratch)
        }
        Op::Sym(s) => text::sym_text(ctx, *s),
        Op::Label(l) => Err(format!(
            "x86: `{}` cannot take label `{}` as a source",
            mnemonic,
            text::label_text(ctx, *l)?
        )),
        Op::Fpr(_) => Err(format!("x86: `{}` needs an integer source", mnemonic)),
        Op::Extern(_) => Err(text::extern_operand_error()),
    }
}

fn bin3(ctx: &mut LowerCtx, op: Bin, w: Width, alu: &Alu3) -> Result<(), String> {
    let (dst, lhs, rhs) = (&alu.dst, &alu.lhs, &alu.rhs);
    if offlineasm_ir::op_eq(lhs, dst) {
        if matches!(op, Bin::Add | Bin::Sub) && rhs.is_zero_imm() {
            return Ok(());
        }
        return bin2_text(ctx, op.mnemonic(), w, dst, rhs);
    }
    if op.commutative() && offlineasm_ir::op_eq(rhs, dst) {
        return bin2_text(ctx, op.mnemonic(), w, dst, lhs);
    }
    if op == Bin::Sub && offlineasm_ir::op_eq(rhs, dst) {
        unop(ctx, "neg", w, dst)?;
        return bin2_text(ctx, "add", w, dst, lhs);
    }
    if matches!(op, Bin::Add | Bin::Sub) && (lhs.is_zero_imm() || rhs.is_zero_imm()) {
        let other = if lhs.is_zero_imm() { rhs } else { lhs };
        return mov(ctx, w, dst, other);
    }
    mov(ctx, w, dst, lhs)?;
    bin2_text(ctx, op.mnemonic(), w, dst, rhs)
}

fn flag_bin3(ctx: &mut LowerCtx, op: Bin, w: Width, alu: &Alu3) -> Result<(), String> {
    let (dst, lhs, rhs) = (&alu.dst, &alu.lhs, &alu.rhs);
    if offlineasm_ir::op_eq(lhs, dst) {
        return bin2_text(ctx, op.mnemonic(), w, dst, rhs);
    }
    if op.commutative() && offlineasm_ir::op_eq(rhs, dst) {
        return bin2_text(ctx, op.mnemonic(), w, dst, lhs);
    }
    if op == Bin::Sub && offlineasm_ir::op_eq(rhs, dst) {
        if matches!(dst, Op::Gpr(_)) {
            mov(ctx, w, &Op::Gpr(scratch_gpr()), lhs)?;
            bin2_text(ctx, "sub", w, &Op::Gpr(scratch_gpr()), dst)?;
            mov(ctx, w, dst, &Op::Gpr(scratch_gpr()))?;
            return Ok(());
        }
        unop(ctx, "neg", w, dst)?;
        return bin2_text(ctx, "add", w, dst, lhs);
    }
    mov(ctx, w, dst, lhs)?;
    bin2_text(ctx, op.mnemonic(), w, dst, rhs)
}

fn add3(ctx: &mut LowerCtx, w: Width, alu: &Alu3) -> Result<(), String> {
    let (dst, lhs, rhs) = (&alu.dst, &alu.lhs, &alu.rhs);
    if offlineasm_ir::op_eq(lhs, dst) {
        if rhs.is_zero_imm() {
            return Ok(());
        }
        return bin2_text(ctx, "add", w, dst, rhs);
    }
    if matches!(w, Width::B32 | Width::B64) {
        if let Op::Gpr(d) = dst {
            let d = gpr_text(*d, w)?;
            match (lhs, rhs) {
                (Op::Gpr(a), Op::Gpr(b)) => {
                    let (a, b) = (gpr_text(*a, Width::B64)?, gpr_text(*b, Width::B64)?);
                    puts(ctx, &format!("lea {}, [{} + {}]", d, a, b));
                    return Ok(());
                }
                (Op::Gpr(a), Op::Imm(v)) | (Op::Imm(v), Op::Gpr(a)) => {
                    if *v == 0 {
                        let a = gpr_text(*a, w)?;
                        puts(ctx, &format!("mov {}, {}", d, a));
                        return Ok(());
                    }
                    if let Ok(disp) = i32::try_from(*v) {
                        let a = gpr_text(*a, Width::B64)?;
                        puts(
                            ctx,
                            &format!("lea {}, {}", d, base_disp_text(&a, i64::from(disp))),
                        );
                        return Ok(());
                    }
                }
                _ => {}
            }
        }
    }
    bin3(ctx, Bin::Add, w, alu)
}

fn mul3(ctx: &mut LowerCtx, w: Width, alu: &Alu3) -> Result<(), String> {
    let (dst, lhs, rhs) = (&alu.dst, &alu.lhs, &alu.rhs);
    if offlineasm_ir::op_eq(lhs, dst) {
        return imul2(ctx, w, dst, rhs);
    }
    if let Op::Imm(v) = rhs {
        if Width::B32.fits(*v) {
            let d = mul_dst_text(w, dst)?;
            let l = imul_src_text(ctx, w, lhs)?;
            puts(ctx, &format!("imul {}, {}, {}", d, l, imm_text(*v)));
            return Ok(());
        }
    }
    mov(ctx, w, dst, lhs)?;
    imul2(ctx, w, dst, rhs)
}

fn imul2(ctx: &mut LowerCtx, w: Width, dst: &Op, src: &Op) -> Result<(), String> {
    if matches!(dst, Op::Mem(_)) {
        if matches!(src, Op::Imm(v) if !Width::B32.fits(*v)) {
            return Err("x86: `imul` to memory needs a 32-bit immediate".to_string());
        }
        let scratch = Op::Gpr(scratch_gpr());
        mov(ctx, w, &scratch, dst)?;
        imul2(ctx, w, &scratch, src)?;
        return mov(ctx, w, dst, &scratch);
    }
    let d = mul_dst_text(w, dst)?;
    match src {
        Op::Gpr(g) => {
            let s = gpr_text(*g, w)?;
            puts(ctx, &format!("imul {}, {}", d, s));
            Ok(())
        }
        Op::Mem(m) => {
            let s = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("imul {}, {}", d, s));
            Ok(())
        }
        Op::Imm(v) if Width::B32.fits(*v) => {
            puts(ctx, &format!("imul {}, {}, {}", d, d, imm_text(*v)));
            Ok(())
        }
        Op::Imm(v) => {
            load_scratch_imm(ctx, *v)?;
            let s = gpr_text(scratch_gpr(), w)?;
            puts(ctx, &format!("imul {}, {}", d, s));
            Ok(())
        }
        _ => Err("x86: `imul` needs a register, memory, or immediate source".to_string()),
    }
}

fn imul_src_text(ctx: &LowerCtx, w: Width, src: &Op) -> Result<String, String> {
    match src {
        Op::Gpr(g) => gpr_text(*g, w),
        Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(w)), 0),
        _ => Err("x86: `imul` needs a register or memory source here".to_string()),
    }
}

fn mul_dst_text(w: Width, dst: &Op) -> Result<String, String> {
    if !matches!(w, Width::B32 | Width::B64) {
        return Err("x86: `imul` needs a 32- or 64-bit width".to_string());
    }
    match dst {
        Op::Gpr(g) => gpr_text(*g, w),
        _ => Err("x86: `imul` needs a register destination".to_string()),
    }
}

fn mul_imm(ctx: &mut LowerCtx, w: Width, dst: Gpr, lhs: Gpr, imm: i64) -> Result<(), String> {
    let (d, l) = (gpr_text(dst, w)?, gpr_text(lhs, w)?);
    if Width::B32.fits(imm) {
        puts(ctx, &format!("imul {}, {}, {}", d, l, imm_text(imm)));
        return Ok(());
    }
    load_scratch_imm(ctx, imm)?;
    let s = gpr_text(scratch_gpr(), w)?;
    if dst != lhs {
        puts(ctx, &format!("mov {}, {}", d, l));
    }
    puts(ctx, &format!("imul {}, {}", d, s));
    Ok(())
}

fn unop(ctx: &mut LowerCtx, mnemonic: &str, w: Width, dst: &Op) -> Result<(), String> {
    match dst {
        Op::Gpr(g) => {
            let d = gpr_text(*g, w)?;
            puts(ctx, &format!("{} {}", mnemonic, d));
            Ok(())
        }
        Op::Mem(m) => {
            let d = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("{} {}", mnemonic, d));
            Ok(())
        }
        _ => Err(format!(
            "x86: `{}` needs a register or memory operand",
            mnemonic
        )),
    }
}

fn shift(
    ctx: &mut LowerCtx,
    w: Width,
    op: ShiftOp,
    dst: Gpr,
    cnt: &ShiftCnt,
) -> Result<(), String> {
    let mnemonic = match op {
        ShiftOp::Shl => "sal",
        ShiftOp::ShrSar => "sar",
        ShiftOp::Shr => "shr",
        ShiftOp::Rotl => "rol",
        ShiftOp::Rotr => "ror",
    };
    let d = gpr_text(dst, w)?;
    match cnt {
        ShiftCnt::Imm(v) => {
            if !(-128..=255).contains(v) {
                return Err(format!("x86: shift count {} is out of range", v));
            }
            puts(ctx, &format!("{} {}, {}", mnemonic, d, imm_text(*v)));
            Ok(())
        }
        ShiftCnt::Reg(g) => {
            let cl = gpr_text(Gpr(1), Width::B8)?;
            if *g == Gpr(1) {
                puts(ctx, &format!("{} {}, {}", mnemonic, d, cl));
                return Ok(());
            }
            if dst == Gpr(1) {
                return Err("x86: cannot shift the count register by another register".to_string());
            }
            let rcx = gpr_text(Gpr(1), Width::B64)?;
            let g = gpr_text(*g, Width::B64)?;
            puts(ctx, &format!("xchg {}, {}", rcx, g));
            puts(ctx, &format!("{} {}, {}", mnemonic, d, cl));
            puts(ctx, &format!("xchg {}, {}", rcx, g));
            Ok(())
        }
    }
}

fn mul_wide(ctx: &mut LowerCtx, signed: bool, dst: Gpr, lhs: Gpr, rhs: Gpr) -> Result<(), String> {
    let (d64, l32, r32) = (
        gpr_text(dst, Width::B64)?,
        gpr_text(lhs, Width::B32)?,
        gpr_text(rhs, Width::B32)?,
    );
    let scratch64 = gpr_text(scratch_gpr(), Width::B64)?;
    if signed {
        puts(ctx, &format!("movsxd {}, {}", scratch64, r32));
        puts(ctx, &format!("movsxd {}, {}", d64, l32));
    } else {
        let d32 = gpr_text(dst, Width::B32)?;
        let scratch32 = gpr_text(scratch_gpr(), Width::B32)?;
        puts(ctx, &format!("mov {}, {}", scratch32, r32));
        puts(ctx, &format!("mov {}, {}", d32, l32));
    }
    puts(ctx, &format!("imul {}, {}", d64, scratch64));
    Ok(())
}

fn mul_high(ctx: &mut LowerCtx, signed: bool, rhs: &Op) -> Result<(), String> {
    let mnemonic = if signed { "imul" } else { "mul" };
    let src = match rhs {
        Op::Gpr(g) => gpr_text(*g, Width::B64)?,
        Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(Width::B64)), 0)?,
        _ => return Err("x86: multiply-high needs a register or memory factor".to_string()),
    };
    puts(ctx, &format!("{} {}", mnemonic, src));
    Ok(())
}

fn div_mod1(ctx: &mut LowerCtx, signed: bool, w: Width, divisor: &Op) -> Result<(), String> {
    let mnemonic = if signed { "idiv" } else { "div" };
    let src = match divisor {
        Op::Gpr(g) => gpr_text(*g, w)?,
        Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(w)), 0)?,
        Op::Imm(v) => {
            load_scratch_imm(ctx, *v)?;
            gpr_text(scratch_gpr(), w)?
        }
        _ => return Err("x86: divide needs a register, memory, or immediate divisor".to_string()),
    };
    puts(ctx, &format!("{} {}", mnemonic, src));
    Ok(())
}

fn div3(
    ctx: &mut LowerCtx,
    signed: bool,
    w: Width,
    dst: Gpr,
    dvd: &Op,
    dvs: &Op,
    remainder: bool,
) -> Result<(), String> {
    if w != Width::B32 && w != Width::B64 {
        return Err("x86: divide needs a 32- or 64-bit width".to_string());
    }

    let acc = |g: &Gpr| *g == Gpr(0) || *g == Gpr(2);
    let acc_mem =
        |m: &Mem| m.base.is_some_and(|g| acc(&g)) || matches!(m.index, Some((i, _)) if acc(&i));
    let sc_text = gpr_text(scratch_gpr(), w)?;
    let divisor = match dvs {
        Op::Gpr(g) if acc(g) => {
            puts(ctx, &format!("mov {}, {}", sc_text, gpr_text(*g, w)?));
            sc_text.clone()
        }
        Op::Gpr(g) => gpr_text(*g, w)?,
        Op::Mem(m) if acc_mem(m) => {
            let s = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("mov {}, {}", sc_text, s));
            sc_text.clone()
        }
        Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(w)), 0)?,
        Op::Imm(v) => {
            load_scratch_imm(ctx, *v)?;
            gpr_text(scratch_gpr(), w)?
        }
        _ => return Err("x86: divide needs a register, memory, or immediate divisor".to_string()),
    };
    let (ax64, dx64) = (gpr_text(Gpr(0), Width::B64)?, gpr_text(Gpr(2), Width::B64)?);
    let (axw, dxw) = (gpr_text(Gpr(0), w)?, gpr_text(Gpr(2), w)?);
    puts(ctx, &format!("push {}", ax64));
    puts(ctx, &format!("push {}", dx64));
    // Dividend into the accumulator, then the sign/zero fill.
    match dvd {
        Op::Gpr(g) => {
            let s = gpr_text(*g, w)?;
            puts(ctx, &format!("mov {}, {}", axw, s));
        }
        Op::Mem(m) => {
            let s = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("mov {}, {}", axw, s));
        }
        Op::Imm(v) => {
            if w == Width::B32 && !imm_encodable(w, *v) {
                // Out of `imm32` range: load through `rax` directly rather
                // than scratch, so a staged divisor keeps its slot. Only the
                // low 32 bits are the dividend, and `cdq`/`xor` refill the
                // upper half from them anyway.
                puts(ctx, &format!("movabs {}, {}", ax64, hex_imm(*v)));
            } else {
                puts(ctx, &format!("mov {}, {}", axw, imm_text(*v)));
            }
        }
        _ => {
            puts(ctx, &format!("pop {}", dx64));
            puts(ctx, &format!("pop {}", ax64));
            return Err("x86: divide needs a register, memory, or immediate dividend".to_string());
        }
    }
    if signed {
        puts(ctx, if w == Width::B64 { "cqo" } else { "cdq" });
    } else {
        puts(ctx, &format!("xor {}, {}", dxw, dxw));
    }
    let mnemonic = if signed { "idiv" } else { "div" };
    puts(ctx, &format!("{} {}", mnemonic, divisor));
    let half = if remainder { dxw } else { axw };
    let d = gpr_text(dst, w)?;
    if dst == Gpr(0) || dst == Gpr(2) {
        // Restoring the accumulator pair would overwrite a result produced
        // in one of those two registers, so store it in scratch first.
        let scratch = gpr_text(scratch_gpr(), w)?;
        puts(ctx, &format!("mov {}, {}", scratch, half));
        puts(ctx, &format!("pop {}", dx64));
        puts(ctx, &format!("pop {}", ax64));
        puts(ctx, &format!("mov {}, {}", d, scratch));
        return Ok(());
    }
    puts(ctx, &format!("mov {}, {}", d, half));
    puts(ctx, &format!("pop {}", dx64));
    puts(ctx, &format!("pop {}", ax64));
    Ok(())
}

fn extend(
    ctx: &mut LowerCtx,
    from: Width,
    to: Width,
    sx: Sx,
    dst: Gpr,
    src: &Op,
) -> Result<(), String> {
    if from == Width::B32 && to == Width::B32 && sx == Sx::Zero {
        return mov(ctx, Width::B32, &Op::Gpr(dst), src);
    }
    if from == Width::B32 && to == Width::B32 && sx == Sx::Sign {
        return mov(ctx, Width::B32, &Op::Gpr(dst), src);
    }
    let src_text = match src {
        Op::Gpr(g) => gpr_text(*g, from)?,
        Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(from)), 0)?,
        _ => return Err("x86: extending move needs a register or memory source".to_string()),
    };
    let d = gpr_text(dst, to)?;
    let mnemonic = match (from, to, sx) {
        (Width::B8, Width::B32 | Width::B64, Sx::Zero)
        | (Width::B16, Width::B32 | Width::B64, Sx::Zero) => "movzx",
        (Width::B8, Width::B32 | Width::B64, Sx::Sign)
        | (Width::B16, Width::B32 | Width::B64, Sx::Sign) => "movsx",
        (Width::B32, Width::B64, Sx::Sign) => "movsxd",
        _ => {
            return Err(format!(
                "x86: unsupported {} -> {} extension",
                from.bytes() * 8,
                to.bytes() * 8
            ))
        }
    };
    puts(ctx, &format!("{} {}, {}", mnemonic, d, src_text));
    Ok(())
}

fn count_zeros(
    ctx: &mut LowerCtx,
    w: Width,
    dst: Gpr,
    src: &Op,
    trailing: bool,
) -> Result<(), String> {
    if w != Width::B32 && w != Width::B64 {
        return Err("x86: zero count needs a 32- or 64-bit width".to_string());
    }
    let d = gpr_text(dst, w)?;
    let s = match src {
        Op::Gpr(g) => gpr_text(*g, w)?,
        Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(w)), 0)?,
        _ => return Err("x86: zero count needs a register or memory source".to_string()),
    };
    let mnemonic = if trailing { "bsf" } else { "bsr" };
    puts(ctx, &format!("{} {}, {}", mnemonic, d, s));
    let nonzero = text::synth_name(ctx, "countNonZero", u32::from(trailing));
    puts(ctx, &format!("jnz {}", nonzero));
    let bits = i64::from(w.bytes()) * 8;
    puts(ctx, &format!("mov {}, {}", d, imm_text(bits)));
    if trailing {
        puts(ctx, &format!("{}:", nonzero));
        return Ok(());
    }
    let done = text::synth_name(ctx, "countDone", 0);
    puts(ctx, &format!("jmp {}", done));
    puts(ctx, &format!("{}:", nonzero));
    let mask = if w == Width::B64 { 0x3f } else { 0x1f };
    puts(ctx, &format!("xor {}, {}", d, imm_text(mask)));
    puts(ctx, &format!("{}:", done));
    Ok(())
}

fn popcnt(ctx: &mut LowerCtx, w: Width, dst: Gpr, src: &Op) -> Result<(), String> {
    let d = gpr_text(dst, w)?;
    let s = match src {
        Op::Gpr(g) => gpr_text(*g, w)?,
        Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(w)), 0)?,
        _ => return Err("x86: `popcnt` needs a register or memory source".to_string()),
    };
    puts(ctx, &format!("popcnt {}, {}", d, s));
    Ok(())
}

fn add_shifted(ctx: &mut LowerCtx, dst: Gpr, lhs: Gpr, rhs: Gpr, amount: u8) -> Result<(), String> {
    let (d, l, r) = (
        gpr_text(dst, Width::B64)?,
        gpr_text(lhs, Width::B64)?,
        gpr_text(rhs, Width::B64)?,
    );
    if amount <= 3 {
        let index = if amount == 0 {
            r
        } else {
            format!("{}*{}", r, 1u32 << amount)
        };
        puts(ctx, &format!("lea {}, [{} + {}]", d, l, index));
        return Ok(());
    }
    let scratch = gpr_text(scratch_gpr(), Width::B64)?;
    puts(ctx, &format!("mov {}, {}", scratch, r));
    puts(
        ctx,
        &format!("sal {}, {}", scratch, imm_text(i64::from(amount))),
    );
    if dst == lhs {
        puts(ctx, &format!("add {}, {}", d, scratch));
    } else if dst == scratch_gpr() {
        puts(ctx, &format!("add {}, {}", d, l));
    } else {
        puts(ctx, &format!("mov {}, {}", d, l));
        puts(ctx, &format!("add {}, {}", d, scratch));
    }
    Ok(())
}

fn cmov(
    ctx: &mut LowerCtx,
    w: Width,
    zero: bool,
    dst: Gpr,
    src: &Op,
    test: Gpr,
) -> Result<(), String> {
    let (t, d) = (gpr_text(test, Width::B64)?, gpr_text(dst, w)?);
    puts(ctx, &format!("test {}, {}", t, t));
    let s = match src {
        Op::Gpr(g) => gpr_text(*g, w)?,
        Op::Mem(m) => {
            let scratch = gpr_text(scratch_gpr(), w)?;
            let m = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("mov {}, {}", scratch, m));
            scratch
        }
        Op::Imm(v) => {
            load_scratch_imm(ctx, *v)?;
            gpr_text(scratch_gpr(), w)?
        }
        _ => {
            return Err(
                "x86: conditional move needs a register, memory, or immediate source".to_string(),
            )
        }
    };
    let mnemonic = if zero { "cmovz" } else { "cmovnz" };
    puts(ctx, &format!("{} {}, {}", mnemonic, d, s));
    Ok(())
}

fn vec_extract(ctx: &mut LowerCtx, w: Width, dst: Gpr, src: Fpr, lane: u8) -> Result<(), String> {
    let (mnemonic, to) = match w {
        Width::B8 => ("pextrb", Width::B32),
        Width::B16 => ("pextrw", Width::B32),
        Width::B32 => ("pextrd", Width::B32),
        Width::B64 => ("pextrq", Width::B64),
    };
    let (d, x) = (gpr_text(dst, to)?, fpr_text(src)?);
    puts(ctx, &format!("{} {}, {}, {}", mnemonic, d, x, lane));
    Ok(())
}

fn int_compare(ctx: &mut LowerCtx, cc: IntCc, w: Width, lhs: &Op, rhs: &Op) -> Result<(), String> {
    let equality = matches!(cc, IntCc::Eq | IntCc::Ne);
    if equality {
        for (value, other) in [(lhs, rhs), (rhs, lhs)] {
            if value.is_zero_imm() {
                if let Op::Gpr(g) = other {
                    let r = gpr_text(*g, w)?;
                    puts(ctx, &format!("test {}, {}", r, r));
                    return Ok(());
                }
            }
        }
    }
    let mut scratch = false;
    let lhs_text = match lhs {
        Op::Imm(v) if matches!(rhs, Op::Imm(_)) => {
            return Err("x86: compare needs at least one register operand".to_string())
        }
        Op::Imm(v) => {
            if imm_encodable(w, *v) {
                let s = gpr_text(scratch_gpr(), w)?;
                puts(ctx, &format!("mov {}, {}", s, imm_text(*v)));
            } else {
                load_scratch_imm(ctx, *v)?;
            }
            scratch = true;
            gpr_text(scratch_gpr(), w)?
        }
        Op::Mem(m) if matches!(rhs, Op::Imm(_) | Op::Mem(_)) => {
            let s = gpr_text(scratch_gpr(), w)?;
            let m = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("mov {}, {}", s, m));
            scratch = true;
            s
        }
        _ => op_text(ctx, lhs, w)?,
    };
    let rhs_text = match rhs {
        Op::Imm(v) if imm_encodable(w, *v) => imm_text(*v),
        Op::Imm(v) => {
            if scratch {
                return Err("x86: compare needs both immediates to be encodable".to_string());
            }
            load_scratch_imm(ctx, *v)?;
            gpr_text(scratch_gpr(), w)?
        }
        _ => op_text(ctx, rhs, w)?,
    };
    puts(ctx, &format!("cmp {}, {}", lhs_text, rhs_text));
    Ok(())
}

fn test_flags(ctx: &mut LowerCtx, w: Width, value: &Op, mask: Option<&Op>) -> Result<(), String> {
    let all_ones = match mask {
        None | Some(Op::Imm(-1)) => true,
        Some(_) => false,
    };
    if all_ones {
        return match value {
            Op::Gpr(g) => {
                let r = gpr_text(*g, w)?;
                puts(ctx, &format!("test {}, {}", r, r));
                Ok(())
            }
            Op::Mem(m) => {
                let m = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
                puts(ctx, &format!("cmp {}, 0", m));
                Ok(())
            }
            _ => Err("x86: test needs a register or memory value".to_string()),
        };
    }
    let mask = mask.ok_or_else(|| "x86: test is missing its mask operand".to_string())?;
    match (mask, value) {
        (Op::Imm(v), Op::Gpr(g)) => {
            if !imm_encodable(w, *v) {
                return Err("x86: test mask is out of range for this width".to_string());
            }
            let r = gpr_text(*g, w)?;
            puts(ctx, &format!("test {}, {}", r, imm_text(*v)));
            Ok(())
        }
        (Op::Imm(v), Op::Mem(m)) => {
            if !imm_encodable(w, *v) {
                return Err("x86: test mask is out of range for this width".to_string());
            }
            let m = mem_text(ctx, m, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("test {}, {}", m, imm_text(*v)));
            Ok(())
        }
        (Op::Gpr(m), Op::Gpr(v)) => {
            let v = gpr_text(*v, w)?;
            let m = gpr_text(*m, w)?;
            puts(ctx, &format!("test {}, {}", v, m));
            Ok(())
        }
        (Op::Sym(m), Op::Gpr(v)) => {
            let v = gpr_text(*v, w)?;
            let m = text::sym_text(ctx, *m)?;
            puts(ctx, &format!("test {}, {}", v, m));
            Ok(())
        }
        _ => Err("x86: unsupported test operands".to_string()),
    }
}

fn set_zx(ctx: &mut LowerCtx, setcc: &str, dst: &Op) -> Result<(), String> {
    match dst {
        Op::Gpr(g) => {
            let (byte, int) = (gpr_text(*g, Width::B8)?, gpr_text(*g, Width::B32)?);
            puts(ctx, &format!("{} {}", setcc, byte));
            puts(ctx, &format!("movzx {}, {}", int, byte));
            Ok(())
        }
        Op::Mem(m) => {
            let m = mem_text(ctx, m, Some(size_keyword(Width::B8)), 0)?;
            puts(ctx, &format!("{} {}", setcc, m));
            Ok(())
        }
        _ => Err("x86: `set*` needs a register or memory destination".to_string()),
    }
}

fn int_jcc(cc: IntCc) -> &'static str {
    match cc {
        IntCc::Eq => "je",
        IntCc::Ne => "jne",
        IntCc::Hi => "ja",
        IntCc::Hs => "jae",
        IntCc::Lo => "jb",
        IntCc::Ls => "jbe",
        IntCc::Gt => "jg",
        IntCc::Ge => "jge",
        IntCc::Lt => "jl",
        IntCc::Le => "jle",
    }
}

fn int_setcc(cc: IntCc) -> &'static str {
    match cc {
        IntCc::Eq => "sete",
        IntCc::Ne => "setne",
        IntCc::Hi => "seta",
        IntCc::Hs => "setae",
        IntCc::Lo => "setb",
        IntCc::Ls => "setbe",
        IntCc::Gt => "setg",
        IntCc::Ge => "setge",
        IntCc::Lt => "setl",
        IntCc::Le => "setle",
    }
}

fn test_jcc(test: TestKind) -> &'static str {
    match test {
        TestKind::Sign => "js",
        TestKind::Zero => "jz",
        TestKind::NonZero => "jnz",
    }
}

fn test_setcc(test: TestKind) -> &'static str {
    match test {
        TestKind::Sign => "sets",
        TestKind::Zero => "setz",
        TestKind::NonZero => "setnz",
    }
}

fn flag_jcc(flag: PredFlag) -> &'static str {
    match flag {
        PredFlag::O => "jo",
        PredFlag::S => "js",
        PredFlag::Z => "jz",
        PredFlag::Nz => "jnz",
    }
}

fn op_branch(
    ctx: &mut LowerCtx,
    op: FlagAlu,
    w: Width,
    flag: PredFlag,
    args: &[Op],
) -> Result<(), String> {
    op_branch_alu(ctx, op, w, args)?;
    if op == FlagAlu::Mul && flag != PredFlag::O {
        let d = match args.last() {
            Some(Op::Gpr(d)) => *d,
            _ => scratch_gpr(),
        };
        let d = gpr_text(d, w)?;
        puts(ctx, &format!("test {}, {}", d, d));
    }
    Ok(())
}

fn op_branch_alu(ctx: &mut LowerCtx, op: FlagAlu, w: Width, args: &[Op]) -> Result<(), String> {
    if op == FlagAlu::Sub
        && args.len() == 3
        && offlineasm_ir::op_eq(&args[1], &args[2])
        && !offlineasm_ir::op_eq(&args[0], &args[2])
    {
        let scratch = Op::Gpr(scratch_gpr());
        mov(ctx, w, &scratch, &args[0])?;
        bin2_text(ctx, "sub", w, &scratch, &args[2])?;
        return mov(ctx, w, &args[2], &scratch);
    }
    let (dst, src) = match args {
        [src, dst] => (dst, src),
        [lhs, rhs, dst] if offlineasm_ir::op_eq(lhs, dst) => (dst, rhs),
        [lhs, rhs, dst] if offlineasm_ir::op_eq(rhs, dst) => (dst, lhs),
        [lhs, rhs, dst] => {
            mov(ctx, w, dst, lhs)?;
            (dst, rhs)
        }
        _ => {
            return Err(format!(
                "x86: op-branch expects 2 or 3 leading operands, got {}",
                args.len()
            ))
        }
    };
    match op {
        FlagAlu::Add => bin2_text(ctx, "add", w, dst, src),
        FlagAlu::Sub => bin2_text(ctx, "sub", w, dst, src),
        FlagAlu::Mul => imul2(ctx, w, dst, src),
        FlagAlu::Or => bin2_text(ctx, "or", w, dst, src),
    }
}

fn jump(ctx: &mut LowerCtx, target: &Target, is_call: bool) -> Result<(), String> {
    let mnemonic = if is_call { "call" } else { "jmp" };
    match target {
        Target::Label(l) => {
            let l = text::label_text(ctx, *l)?;
            puts(ctx, &format!("{} {}", mnemonic, l));
            Ok(())
        }
        Target::Reg(g) => {
            let g = gpr_text(*g, Width::B64)?;
            puts(ctx, &format!("{} {}", mnemonic, g));
            Ok(())
        }
        Target::Mem(m) => {
            let m = mem_text(ctx, m, Some(size_keyword(Width::B64)), 0)?;
            puts(ctx, &format!("{} {}", mnemonic, m));
            Ok(())
        }
        Target::Abs(v) => {
            load_scratch_imm(ctx, *v)?;
            let s = gpr_text(scratch_gpr(), Width::B64)?;
            puts(ctx, &format!("{} {}", mnemonic, s));
            Ok(())
        }
        Target::Extern(e) => {
            let target = match e.reach {
                Reach::Near => text::extern_text(ctx, e.id)?,
                Reach::Far => extern_slot_mem(ctx, e.id)?,
            };
            puts(ctx, &format!("{} {}", mnemonic, target));
            Ok(())
        }
    }
}

fn round_imm(mode: RoundMode) -> i64 {
    match mode {
        RoundMode::Nearest => 0,
        RoundMode::Down => 1,
        RoundMode::Up => 2,
        RoundMode::Trunc => 3,
    }
}

fn farith_proxy(op: FAlu) -> &'static str {
    match op {
        FAlu::Add => "add",
        FAlu::Sub => "sub",
        FAlu::Mul => "mul",
        FAlu::Div => "div",
        FAlu::Min => "min",
        FAlu::Max => "max",
    }
}

fn farith(
    ctx: &mut LowerCtx,
    op: FAlu,
    k: FKind,
    arith: &offlineasm_ir::FArith3,
) -> Result<(), String> {
    let mnemonic = farith_proxy(op);
    let dst = arith.dst;
    match &arith.rhs {
        None => fp_fold(ctx, mnemonic, k, dst, &arith.lhs),
        Some(rhs) => {
            let lhs = &arith.lhs;
            let vectorizable = matches!(op, FAlu::Add | FAlu::Sub | FAlu::Mul | FAlu::Div);
            if vectorizable && ctx.setting("HAS_AVX") {
                if let Op::Fpr(l) = lhs {
                    let (d, l) = (fpr_text(dst)?, fpr_text(*l)?);
                    let r = fp_src_text(ctx, k, rhs)?;
                    puts(
                        ctx,
                        &format!("v{}{} {}, {}, {}", mnemonic, fk_suffix(k), d, l, r),
                    );
                    return Ok(());
                }
            }
            if matches!(lhs, Op::Fpr(l) if *l == dst) {
                return fp_fold(ctx, mnemonic, k, dst, rhs);
            }
            if matches!(rhs, Op::Fpr(r) if *r == dst) {
                if op.is_commutative() {
                    return fp_fold(ctx, mnemonic, k, dst, lhs);
                }
                let scratch = scratch_fpr();
                fp_stage(ctx, k, scratch, lhs)?;
                fp_fold(ctx, mnemonic, k, scratch, &Op::Fpr(dst))?;
                let (d, s) = (fpr_text(dst)?, fpr_text(scratch)?);
                puts(ctx, &format!("{} {}, {}", fk_mov(k), d, s));
                return Ok(());
            }
            fp_stage(ctx, k, dst, lhs)?;
            fp_fold(ctx, mnemonic, k, dst, rhs)
        }
    }
}

fn fp_fold(ctx: &mut LowerCtx, mnemonic: &str, k: FKind, dst: Fpr, src: &Op) -> Result<(), String> {
    let d = fpr_text(dst)?;
    let s = fp_src_text(ctx, k, src)?;
    puts(ctx, &format!("{}{} {}, {}", mnemonic, fk_suffix(k), d, s));
    Ok(())
}

fn fp_stage(ctx: &mut LowerCtx, k: FKind, dst: Fpr, src: &Op) -> Result<(), String> {
    let d = fpr_text(dst)?;
    let s = fp_src_text(ctx, k, src)?;
    puts(ctx, &format!("{} {}, {}", fk_mov(k), d, s));
    Ok(())
}

fn fma(
    ctx: &mut LowerCtx,
    op: FmaOp,
    k: FKind,
    a: &Op,
    b: &Op,
    c: &Op,
    dst: Fpr,
) -> Result<(), String> {
    if !ctx.setting("HAS_AVX") {
        return Err(
            "x86: fused multiply-add requires the AVX/FMA3 CPU features (guard the call with \
             `if HAS_AVX`)"
                .to_string(),
        );
    }
    let mnemonic = match op {
        FmaOp::Add => "vfmadd213",
        FmaOp::Sub => "vfmsub213",
        FmaOp::NegAdd => "vfnmadd213",
        FmaOp::NegSub => "vfnmsub213",
    };
    let scratch = scratch_fpr();
    fp_stage(ctx, k, scratch, a)?;
    let (s, b, c) = (
        fpr_text(scratch)?,
        fp_src_text(ctx, k, b)?,
        fp_src_text(ctx, k, c)?,
    );
    puts(
        ctx,
        &format!("{}{} {}, {}, {}", mnemonic, fk_suffix(k), s, b, c),
    );
    let d = fpr_text(dst)?;
    puts(ctx, &format!("{} {}, {}", fk_mov(k), d, s));
    Ok(())
}

fn fp_sign(ctx: &mut LowerCtx, k: FKind, dst: Fpr, src: &Op, negate: bool) -> Result<(), String> {
    let d = fpr_text(dst)?;
    // The mask is built in `dst`, so a source that is `dst` itself moves to
    // the scratch FPR first.
    let aliased = matches!(src, Op::Fpr(x) if *x == dst);
    if aliased {
        let x = fpr_text(scratch_fpr())?;
        puts(ctx, &format!("{} {}, {}", fk_mov(k), x, d));
    }
    let (mask, mnemonic) = match (k, negate) {
        (FKind::F64, false) => (0x8000_0000_0000_0000u64 as i64, "andnps"),
        (FKind::F64, true) => (0x8000_0000_0000_0000u64 as i64, "xorpd"),
        (FKind::F32, false) => (0x8000_0000i64, "andnps"),
        (FKind::F32, true) => (0x8000_0000i64, "xorps"),
    };
    load_scratch_imm(ctx, mask)?;
    let scratch = gpr_text(scratch_gpr(), fk_width(k))?;
    let mv = match k {
        FKind::F32 => "movd",
        FKind::F64 => "movq",
    };
    puts(ctx, &format!("{} {}, {}", mv, d, scratch));
    let src = match src {
        Op::Fpr(_) if aliased => fpr_text(scratch_fpr())?,
        Op::Fpr(x) => fpr_text(*x)?,
        Op::Mem(m) => {
            let scratch_xmm = fpr_text(scratch_fpr())?;
            let m = mem_text(ctx, m, Some(size_keyword(fk_width(k))), 0)?;
            puts(ctx, &format!("{} {}, {}", fk_mov(k), scratch_xmm, m));
            scratch_xmm
        }
        _ => return Err("x86: `abs`/`neg` needs a register or memory source".to_string()),
    };
    puts(ctx, &format!("{} {}, {}", mnemonic, d, src));
    Ok(())
}

fn bitcast(ctx: &mut LowerCtx, dir: BitcastDir, dst: &Op, src: &Op) -> Result<(), String> {
    match dir {
        BitcastDir::Q2D => match (dst, src) {
            (Op::Fpr(d), Op::Gpr(s)) => {
                let (d, s) = (fpr_text(*d)?, gpr_text(*s, Width::B64)?);
                puts(ctx, &format!("movq {}, {}", d, s));
                Ok(())
            }
            (Op::Fpr(d), Op::Mem(m)) => {
                let d = fpr_text(*d)?;
                let m = mem_text(ctx, m, Some(size_keyword(Width::B64)), 0)?;
                puts(ctx, &format!("movq {}, {}", d, m));
                Ok(())
            }
            _ => {
                Err("x86: `fq2d` needs a quad or memory source and an FPR destination".to_string())
            }
        },
        BitcastDir::D2Q => match (dst, src) {
            (Op::Gpr(d), Op::Fpr(s)) => {
                let (d, s) = (gpr_text(*d, Width::B64)?, fpr_text(*s)?);
                puts(ctx, &format!("movq {}, {}", d, s));
                Ok(())
            }
            (Op::Mem(m), Op::Fpr(s)) => {
                let s = fpr_text(*s)?;
                let m = mem_text(ctx, m, Some(size_keyword(Width::B64)), 0)?;
                puts(ctx, &format!("movq {}, {}", m, s));
                Ok(())
            }
            _ => {
                Err("x86: `fd2q` needs an FPR source and a quad or memory destination".to_string())
            }
        },
        BitcastDir::I2F => match (dst, src) {
            (Op::Fpr(d), Op::Gpr(s)) => {
                let (d, s) = (fpr_text(*d)?, gpr_text(*s, Width::B32)?);
                puts(ctx, &format!("movd {}, {}", d, s));
                Ok(())
            }
            (Op::Fpr(d), Op::Mem(m)) => {
                let d = fpr_text(*d)?;
                let m = mem_text(ctx, m, Some(size_keyword(Width::B32)), 0)?;
                puts(ctx, &format!("movd {}, {}", d, m));
                Ok(())
            }
            _ => {
                Err("x86: `fi2f` needs an int or memory source and an FPR destination".to_string())
            }
        },
        BitcastDir::F2I => match (dst, src) {
            (Op::Gpr(d), Op::Fpr(s)) => {
                let (d, s) = (gpr_text(*d, Width::B32)?, fpr_text(*s)?);
                puts(ctx, &format!("movd {}, {}", d, s));
                Ok(())
            }
            (Op::Mem(m), Op::Fpr(s)) => {
                let s = fpr_text(*s)?;
                let m = mem_text(ctx, m, Some(size_keyword(Width::B32)), 0)?;
                puts(ctx, &format!("movd {}, {}", m, s));
                Ok(())
            }
            _ => {
                Err("x86: `ff2i` needs an FPR source and an int or memory destination".to_string())
            }
        },
    }
}

fn fp_ucomi(ctx: &mut LowerCtx, k: FKind, lhs: &Op, rhs: &Op) -> Result<(), String> {
    let l = match lhs {
        Op::Fpr(x) => fpr_text(*x)?,
        Op::Mem(m) => {
            let scratch = fpr_text(scratch_fpr())?;
            let m = mem_text(ctx, m, Some(size_keyword(fk_width(k))), 0)?;
            puts(ctx, &format!("{} {}, {}", fk_mov(k), scratch, m));
            scratch
        }
        _ => return Err("x86: float compare needs a register or memory left side".to_string()),
    };
    let r = match rhs {
        Op::Fpr(x) => fpr_text(*x)?,
        Op::Mem(m) => mem_text(ctx, m, Some(size_keyword(fk_width(k))), 0)?,
        _ => return Err("x86: float compare needs a register or memory right side".to_string()),
    };
    puts(ctx, &format!("ucomi{} {}, {}", fk_suffix(k), l, r));
    Ok(())
}

fn branch_f(
    ctx: &mut LowerCtx,
    cc: FCc,
    k: FKind,
    lhs: &Op,
    rhs: &Op,
    target: Lbl,
) -> Result<(), String> {
    let label = text::label_text(ctx, target)?;
    let simple = |ctx: &mut LowerCtx, jcc: &str| -> Result<(), String> {
        fp_ucomi(ctx, k, lhs, rhs)?;
        puts(ctx, &format!("{} {}", jcc, label));
        Ok(())
    };
    match cc {
        FCc::Eq => {
            fp_ucomi(ctx, k, lhs, rhs)?;
            let unordered = text::synth_name(ctx, "fpEqUnordered", 0);
            puts(ctx, &format!("jp {}", unordered));
            puts(ctx, &format!("je {}", label));
            puts(ctx, &format!("{}:", unordered));
            Ok(())
        }
        FCc::Ne => simple(ctx, "jne"),
        FCc::Gt | FCc::Lt => simple(ctx, "ja"),
        FCc::Ge | FCc::Le => simple(ctx, "jae"),
        FCc::EqUn => simple(ctx, "je"),
        FCc::NeUn => {
            fp_ucomi(ctx, k, lhs, rhs)?;
            puts(ctx, &format!("jp {}", label));
            puts(ctx, &format!("jne {}", label));
            Ok(())
        }
        FCc::GtUn | FCc::LtUn => simple(ctx, "jb"),
        FCc::GeUn | FCc::LeUn => simple(ctx, "jbe"),
    }
}

/// Float compare producing 0/1.
fn fset(ctx: &mut LowerCtx, cc: FCc, k: FKind, dst: &Op, lhs: &Op, rhs: &Op) -> Result<(), String> {
    match cc {
        FCc::Eq => {
            if offlineasm_ir::op_eq(lhs, rhs) {
                fp_ucomi(ctx, k, rhs, lhs)?;
                return set_zx(ctx, "setnp", dst);
            }
            let d = gpr_text(set_dst_gpr(dst)?, Width::B64)?;
            puts(ctx, &format!("mov {}, 0", d));
            fp_ucomi(ctx, k, rhs, lhs)?;
            let unordered = text::synth_name(ctx, "fpSetUnordered", 0);
            puts(ctx, &format!("jp {}", unordered));
            set_zx(ctx, "sete", dst)?;
            puts(ctx, &format!("{}:", unordered));
            Ok(())
        }
        FCc::NeUn => {
            if offlineasm_ir::op_eq(lhs, rhs) {
                fp_ucomi(ctx, k, rhs, lhs)?;
                return set_zx(ctx, "setp", dst);
            }
            let d = gpr_text(set_dst_gpr(dst)?, Width::B64)?;
            puts(ctx, &format!("mov {}, 1", d));
            fp_ucomi(ctx, k, rhs, lhs)?;
            let unordered = text::synth_name(ctx, "fpSetUnordered", 0);
            puts(ctx, &format!("jp {}", unordered));
            set_zx(ctx, "setne", dst)?;
            puts(ctx, &format!("{}:", unordered));
            Ok(())
        }
        FCc::Ne => set_cc(ctx, k, "setnz", lhs, rhs, dst, false),
        FCc::Gt => set_cc(ctx, k, "seta", lhs, rhs, dst, false),
        FCc::Ge => set_cc(ctx, k, "setae", lhs, rhs, dst, false),
        // The reversed forms compare the other way round. Expansion folds
        // them into `Gt`/`Ge` with swapped operands, but direct IR users get
        // the same treatment here.
        FCc::Lt => set_cc(ctx, k, "seta", lhs, rhs, dst, true),
        FCc::Le => set_cc(ctx, k, "setae", lhs, rhs, dst, true),
        FCc::EqUn | FCc::GtUn | FCc::GeUn | FCc::LtUn | FCc::LeUn => {
            Err("x86: unordered float set is only defined for eq/nequn".to_string())
        }
    }
}

fn set_cc(
    ctx: &mut LowerCtx,
    k: FKind,
    setcc: &str,
    lhs: &Op,
    rhs: &Op,
    dst: &Op,
    reverse: bool,
) -> Result<(), String> {
    if reverse {
        fp_ucomi(ctx, k, rhs, lhs)?;
    } else {
        fp_ucomi(ctx, k, lhs, rhs)?;
    }
    set_zx(ctx, setcc, dst)
}

fn set_dst_gpr(dst: &Op) -> Result<Gpr, String> {
    match dst {
        Op::Gpr(g) => Ok(*g),
        _ => Err("x86: `cf*`/`cd*` need a register destination".to_string()),
    }
}

fn tls_seg(ctx: &LowerCtx) -> &'static str {
    if ctx.setting("WINDOWS") || ctx.is_win || ctx.macho {
        "gs"
    } else {
        "fs"
    }
}

fn tls(ctx: &mut LowerCtx, w: Width, reg: Gpr, idx: i64, load: bool) -> Result<(), String> {
    let off = tls_offset(idx)?;
    let seg = tls_seg(ctx);
    let mem = format!("{}{}:[{}]", size_keyword(w), seg, imm_text(off));
    if load {
        let r = gpr_text(reg, w)?;
        puts(ctx, &format!("mov {}, {}", r, mem));
        zero_extend_result(ctx, reg, w)?;
    } else {
        let r = gpr_text(reg, w)?;
        puts(ctx, &format!("mov {}, {}", mem, r));
    }
    Ok(())
}

fn tls_lea(ctx: &mut LowerCtx, reg: Gpr, idx: i64) -> Result<(), String> {
    let off = tls_offset(idx)?;
    let r = gpr_text(reg, Width::B64)?;
    puts(
        ctx,
        &format!("lea {}, {}:[{}]", r, tls_seg(ctx), imm_text(off)),
    );
    Ok(())
}

fn rmw_operands<'a>(mnemonic: &str, a: &'a Op, b: &'a Op) -> Result<(Gpr, &'a Mem), String> {
    match (a, b) {
        (Op::Gpr(g), Op::Mem(m)) | (Op::Mem(m), Op::Gpr(g)) => Ok((*g, m)),
        _ => Err(format!(
            "x86: `{}` needs a register and a memory operand",
            mnemonic
        )),
    }
}

fn atomic_rmw(ctx: &mut LowerCtx, op: AtomicOp, w: Width, a: &Op, b: &Op) -> Result<(), String> {
    match op {
        AtomicOp::Add | AtomicOp::Sub => {
            let (reg, mem) = rmw_operands("atomicxchgadd", a, b)?;
            if op == AtomicOp::Sub {
                unop(ctx, "neg", w, &Op::Gpr(reg))?;
            }
            let r = gpr_text(reg, w)?;
            let m = mem_text(ctx, mem, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("lock xadd {}, {}", m, r));
            zero_extend_result(ctx, reg, w)?;
            Ok(())
        }
        AtomicOp::Xchg => {
            let (reg, mem) = rmw_operands("atomicxchg", a, b)?;
            let r = gpr_text(reg, w)?;
            let m = mem_text(ctx, mem, Some(size_keyword(w)), 0)?;
            puts(ctx, &format!("xchg {}, {}", m, r));
            zero_extend_result(ctx, reg, w)?;
            Ok(())
        }
        AtomicOp::And | AtomicOp::Or | AtomicOp::Xor => atomic_logic(ctx, op, w, a, b),
    }
}

fn atomic_logic(ctx: &mut LowerCtx, op: AtomicOp, w: Width, a: &Op, b: &Op) -> Result<(), String> {
    let (reg, mem) = rmw_operands("atomicxchg", a, b)?;
    let acc = Gpr(0);
    let (ax, d) = (gpr_text(acc, w)?, gpr_text(reg, w)?);
    let scratch = scratch_gpr();
    let m = mem_text(ctx, mem, Some(size_keyword(w)), 0)?;
    let retry = text::synth_name(ctx, "atomicRetry", w.bytes());
    let mnemonic = match op {
        AtomicOp::And => "and",
        AtomicOp::Or => "or",
        _ => "xor",
    };
    if reg == acc {
        let s = gpr_text(scratch, w)?;
        let slot = format!("{}[rsp]", size_keyword(w));
        puts(ctx, &format!("push {}", gpr_text(reg, Width::B64)?));
        puts(ctx, &format!("{}:", retry));
        puts(ctx, &format!("mov {}, {}", ax, m));
        puts(ctx, &format!("mov {}, {}", s, ax));
        puts(ctx, &format!("{} {}, {}", mnemonic, s, slot));
        puts(ctx, &format!("lock cmpxchg {}, {}", m, s));
        puts(ctx, &format!("jne {}", retry));
        puts(ctx, "add rsp, 8");
        zero_extend_result(ctx, reg, w)?;
        return Ok(());
    }
    puts(ctx, "push rax");
    puts(ctx, &format!("{}:", retry));
    puts(ctx, &format!("mov {}, {}", ax, m));
    if reg == scratch {
        puts(ctx, &format!("{} {}, {}", mnemonic, d, ax));
    } else {
        let s = gpr_text(scratch, w)?;
        puts(ctx, &format!("mov {}, {}", s, ax));
        puts(ctx, &format!("{} {}, {}", mnemonic, s, d));
    }
    let s = gpr_text(scratch, w)?;
    puts(ctx, &format!("lock cmpxchg {}, {}", m, s));
    puts(ctx, &format!("jne {}", retry));
    puts(ctx, &format!("mov {}, {}", d, ax));
    zero_extend_result(ctx, reg, w)?;
    puts(ctx, "pop rax");
    Ok(())
}

fn zero_extend_result(ctx: &mut LowerCtx, dst: Gpr, w: Width) -> Result<(), String> {
    match w {
        Width::B8 => {
            let (d32, d8) = (gpr_text(dst, Width::B32)?, gpr_text(dst, Width::B8)?);
            puts(ctx, &format!("movzx {}, {}", d32, d8));
        }
        Width::B16 => {
            let (d32, d16) = (gpr_text(dst, Width::B32)?, gpr_text(dst, Width::B16)?);
            puts(ctx, &format!("movzx {}, {}", d32, d16));
        }
        Width::B32 | Width::B64 => {}
    }
    Ok(())
}

fn atomic_cas(
    ctx: &mut LowerCtx,
    w: Width,
    mem: &Mem,
    src: Gpr,
    branch: Option<Lbl>,
) -> Result<(), String> {
    let s = gpr_text(src, w)?;
    let m = mem_text(ctx, mem, Some(size_keyword(w)), 0)?;
    puts(ctx, &format!("lock cmpxchg {}, {}", m, s));
    if let Some(l) = branch {
        let label = text::label_text(ctx, l)?;
        puts(ctx, &format!("jne {}", label));
    }
    Ok(())
}

fn store_cond(
    ctx: &mut LowerCtx,
    w: Width,
    status: Gpr,
    src: Gpr,
    mem: &Mem,
) -> Result<(), String> {
    let s = gpr_text(src, w)?;
    let m = mem_text(ctx, mem, Some(size_keyword(w)), 0)?;
    puts(ctx, &format!("lock cmpxchg {}, {}", m, s));
    set_zx(ctx, "setnz", &Op::Gpr(status))
}

fn pair(
    ctx: &mut LowerCtx,
    w: PairW,
    first: &Op,
    second: &Op,
    mem: &Mem,
    load: bool,
) -> Result<(), String> {
    match (w, load) {
        (PairW::B64, true) | (PairW::B32, true) => {
            let dw = if w == PairW::B64 {
                Width::B64
            } else {
                Width::B32
            };
            let g1 = gpr_of(first)?;
            let g2 = gpr_of(second)?;
            let (d1, d2) = (gpr_text(g1, dw)?, gpr_text(g2, dw)?);
            let (m1, m2) = (
                mem_text(ctx, mem, Some(size_keyword(dw)), 0)?,
                mem_text(ctx, mem, Some(size_keyword(dw)), i64::from(dw.bytes()))?,
            );

            let addr_reg_clobbered_by =
                |g: Gpr| mem.base == Some(g) || mem.index.is_some_and(|(idx, _)| idx == g);
            if addr_reg_clobbered_by(g1) && (g1 == g2 || addr_reg_clobbered_by(g2)) {
                let t = gpr_text(scratch_gpr(), dw)?;
                puts(ctx, &format!("mov {}, {}", t, m2));
                puts(ctx, &format!("mov {}, {}", d1, m1));
                puts(ctx, &format!("mov {}, {}", d2, t));
            } else if addr_reg_clobbered_by(g1) {
                puts(ctx, &format!("mov {}, {}", d2, m2));
                puts(ctx, &format!("mov {}, {}", d1, m1));
            } else {
                puts(ctx, &format!("mov {}, {}", d1, m1));
                puts(ctx, &format!("mov {}, {}", d2, m2));
            }
            Ok(())
        }
        (PairW::B64, false) | (PairW::B32, false) => {
            let dw = if w == PairW::B64 {
                Width::B64
            } else {
                Width::B32
            };
            let (s1, s2) = (
                gpr_text(gpr_of(first)?, dw)?,
                gpr_text(gpr_of(second)?, dw)?,
            );
            let (m1, m2) = (
                mem_text(ctx, mem, Some(size_keyword(dw)), 0)?,
                mem_text(ctx, mem, Some(size_keyword(dw)), i64::from(dw.bytes()))?,
            );
            puts(ctx, &format!("mov {}, {}", m1, s1));
            puts(ctx, &format!("mov {}, {}", m2, s2));
            Ok(())
        }
        (PairW::F64, true) => {
            let (d1, d2) = (fpr_text(fpr_of(first)?)?, fpr_text(fpr_of(second)?)?);
            let (m1, m2) = (
                mem_text(ctx, mem, Some(size_keyword(Width::B64)), 0)?,
                mem_text(ctx, mem, Some(size_keyword(Width::B64)), 8)?,
            );
            puts(ctx, &format!("movsd {}, {}", d1, m1));
            puts(ctx, &format!("movsd {}, {}", d2, m2));
            Ok(())
        }
        (PairW::F64, false) => {
            let (s1, s2) = (fpr_text(fpr_of(first)?)?, fpr_text(fpr_of(second)?)?);
            let (m1, m2) = (
                mem_text(ctx, mem, Some(size_keyword(Width::B64)), 0)?,
                mem_text(ctx, mem, Some(size_keyword(Width::B64)), 8)?,
            );
            puts(ctx, &format!("movsd {}, {}", m1, s1));
            puts(ctx, &format!("movsd {}, {}", m2, s2));
            Ok(())
        }
        (PairW::V128, true) => {
            let (d1, d2) = (fpr_text(fpr_of(first)?)?, fpr_text(fpr_of(second)?)?);
            let (m1, m2) = (
                mem_text(ctx, mem, Some(XMMWORD), 0)?,
                mem_text(ctx, mem, Some(XMMWORD), 16)?,
            );
            puts(ctx, &format!("movdqu {}, {}", d1, m1));
            puts(ctx, &format!("movdqu {}, {}", d2, m2));
            Ok(())
        }
        (PairW::V128, false) => {
            let (s1, s2) = (fpr_text(fpr_of(first)?)?, fpr_text(fpr_of(second)?)?);
            let (m1, m2) = (
                mem_text(ctx, mem, Some(XMMWORD), 0)?,
                mem_text(ctx, mem, Some(XMMWORD), 16)?,
            );
            puts(ctx, &format!("movups {}, {}", m1, s1));
            puts(ctx, &format!("movups {}, {}", m2, s2));
            Ok(())
        }
    }
}

fn gpr_of(op: &Op) -> Result<Gpr, String> {
    match op {
        Op::Gpr(g) => Ok(*g),
        _ => Err("x86: paired access needs register operands".to_string()),
    }
}

fn fpr_of(op: &Op) -> Result<Fpr, String> {
    match op {
        Op::Fpr(x) => Ok(*x),
        _ => Err("x86: paired access needs register operands".to_string()),
    }
}
