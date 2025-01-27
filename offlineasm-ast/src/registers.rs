#[macro_export]
macro_rules! registers {
    ($handler: ident) => {
        $handler! {
            GPRS = [
                t0,
                t1,
                t2,
                t3,
                t4,
                t5,
                t6,
                t7,
                t8,
                t9,
                t10,
                t11,
                t12,
                cfr,
                a0,
                a1,
                a2,
                a3,
                a4,
                a5,
                a6,
                a7,
                r0,
                r1,
                sp,
                lr,
                pc,
                // 64-bit only registers:
                csr0,
                csr1,
                csr2,
                csr3,
                csr4,
                csr5,
                csr6,
                csr7,
                csr8,
                csr9,
                csr10,
                invalidGPR,
            ];

            FPRS = [
                ft0, ft1, ft2, ft3, ft4, ft5, fa0, fa1, fa2, fa3, csfr0, csfr1,
                csfr2, csfr3, csfr4, csfr5, csfr6, csfr7, csfr8, csfr9, csfr10, csfr11,
                fr,
            ];

            VECS = [
                v0, v0_b, v0_h, v0_i, v0_q, v1, v1_b, v1_h, v1_i, v1_q, v2, v2_b,
                v2_h, v2_i, v2_q, v3, v3_b, v3_h, v3_i, v3_q, v4, v4_b, v4_h, v4_i,
                v4_q, v5, v5_b, v5_h, v5_i, v5_q, v6, v6_b, v6_h, v6_i, v6_q, v7,
                v7_b, v7_h, v7_i, v7_q,
            ];
        }
    };
}

macro_rules! define_registers {
    ($(
        $group: ident = [$($reg:ident),* $(,)?];
    )*) => {
        paste::paste! {
            $(
                pub mod [<$group: lower _kw>] {
                    $(
                        syn::custom_keyword!($reg);
                    )*
                }

                pub static [<$group>]: &[&str] = &[
                    $(stringify!($reg)),*
                ];

                pub static [<$group _PATTERN>]: LazyLock<Regex> = LazyLock::new(|| {
                    let regs = $group.join(")|(");
                    Regex::new(&format!("\\A(({}))", regs)).unwrap()
                });

                pub fn [<peek_ $group: lower>](input: syn::parse::ParseStream) -> bool {
                    let cursor = input.cursor();

                    match cursor.ident()  {
                        Some((id, _)) => {
                            let s = id.to_string();

                            return $group.contains(&s.as_str());
                        }

                        _ => false
                    }
                }
            )*

            pub static REGISTER_PATTERN: LazyLock<Regex> = LazyLock::new(|| {
                let mut regs = String::new();
                $(
                    regs.push_str(&$group.join(")|("));
                )*
                Regex::new(&format!("\\A(({}))", regs)).unwrap()
            });

            pub fn is_register(token: &str) -> bool {
                REGISTER_PATTERN.is_match(&token)
            }

            pub fn peek_register(input: syn::parse::ParseStream) -> bool {
                let cursor = input.cursor();
                match cursor.ident() {
                    Some((id, _)) => {
                        let s = id.to_string();
                        return is_register(&s);
                    }
                    _ => false
                }
            }
        }
    };
}
use regex::Regex;
use std::sync::LazyLock;

registers!(define_registers);
