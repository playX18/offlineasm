use crate::instructions;

use super::x86::*;
use crate::instructions::*;

macro_rules! x86_operand_kinds {
    (
        $(
            $group: ident => {
                $(
                    $(#[$outer:meta])*
                    $ins: ident {
                        $(
                            $(#[$inner:meta])*
                            $v: vis $name: ident : $t: ty
                        ),* $(,)?
                    }
                ),*
            }
        ),*
    ) => {
        $(
            $(
                paste::paste! {
                    impl [<$ins:camel>] {
                        macro_extra::match_ident! {
                            match $ins {
                                push | pop => {
                                    pub const KIND: OperandKind = OperandKind::Ptr;
                                },

                                popv | pushv => {
                                    pub const KIND: OperandKind = OperandKind::Double;
                                },
                                r#"i2f"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Int;
                                    pub const DST_KIND: OperandKind = OperandKind::Float;
                                    pub const KIND: OperandKind = OperandKind::Float;
                                },

                                r#"f2i"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Float;
                                    pub const DST_KIND: OperandKind = OperandKind::Int;
                                    pub const KIND: OperandKind = OperandKind::Int;
                                },

                                r#"d2i"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Double;
                                    pub const DST_KIND: OperandKind = OperandKind::Int;
                                    pub const KIND: OperandKind = OperandKind::Int;
                                },

                                r#"q2i"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Quad;
                                    pub const DST_KIND: OperandKind = OperandKind::Int;
                                    pub const KIND: OperandKind = OperandKind::Int;
                                },

                                r#"f2d"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Float;
                                    pub const DST_KIND: OperandKind = OperandKind::Double;
                                    pub const KIND: OperandKind = OperandKind::Double;
                                },

                                r#"d2f"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Double;
                                    pub const DST_KIND: OperandKind = OperandKind::Float;
                                    pub const KIND: OperandKind = OperandKind::Float;
                                },

                                r#"q2f"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Quad;
                                    pub const DST_KIND: OperandKind = OperandKind::Float;
                                    pub const KIND: OperandKind = OperandKind::Float;
                                },

                                r#"q2d"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Quad;
                                    pub const DST_KIND: OperandKind = OperandKind::Double;
                                    pub const KIND: OperandKind = OperandKind::Double;
                                },

                                r#"f2q"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Float;
                                    pub const DST_KIND: OperandKind = OperandKind::Quad;
                                    pub const KIND: OperandKind = OperandKind::Quad;
                                },

                                r#"d2q"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Double;
                                    pub const DST_KIND: OperandKind = OperandKind::Quad;
                                    pub const KIND: OperandKind = OperandKind::Quad;
                                },

                                r#"d2f"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Double;
                                    pub const DST_KIND: OperandKind = OperandKind::Float;
                                    pub const KIND: OperandKind = OperandKind::Float;
                                },

                                r#"f2d"# => {
                                    pub const SRC_KIND: OperandKind = OperandKind::Float;
                                    pub const DST_KIND: OperandKind = OperandKind::Double;
                                    pub const KIND: OperandKind = OperandKind::Double;
                                },

                                r#"b?f(o|s|z|nz|gt|eq|gteq|lt|lteq||b|beq|a|aeq)?$"# => {
                                    pub const KIND: OperandKind = OperandKind::Float;
                                },

                                r#"b?d(o|s|z|nz|gt|eq|gteq|lt|lteq||b|beq|a|aeq)?$"# => {
                                    pub const KIND: OperandKind = OperandKind::Double;
                                },

                                r#"b?b(o|s|z|nz|gt|eq|gteq|lt|lteq||b|beq|a|aeq)?$"# => {
                                    pub const KIND: OperandKind = OperandKind::Byte;
                                },


                                r#"i(o|s|z|nz|gt|eq|gteq|lt|lteq||b|beq|a|aeq)?$"# => {
                                    pub const KIND: OperandKind = OperandKind::Int;
                                },

                                r#"p(o|s|z|nz|gt|eq|gteq|lt|lteq||b|beq|a|aeq)?$"# => {
                                    pub const KIND: OperandKind = OperandKind::Ptr;
                                },

                                r#"q(o|s|z|nz|gt|eq|gteq|lt|lteq||b|beq|a|aeq)?$"# => {
                                    pub const KIND: OperandKind = OperandKind::Quad;
                                },



                                r#"h(o|s|z|nz|gt|eq|gteq|lt|lteq||b|beq|a|aeq)?$"# => {
                                    pub const KIND: OperandKind = OperandKind::Half;
                                },
                                _ => { pub const KIND: OperandKind = OperandKind::None; }
                            }
                        }
                    }
                }
            )*

            paste::paste! {
            impl [<$group:camel>] {
                pub fn x86_operand_kind(&self) -> OperandKind {
                    match self {
                        $(
                            Self::[<$ins:camel>] {..} => [<$ins:camel>]::KIND,
                        )*
                        }
                    }
                }
            }
        )*
    }
}

instructions!(x86_operand_kinds);
