//! OfflineASM instruction definitions.

#[macro_export]
macro_rules! for_each_instruction {
    ($m: ident) => {
        $m! {
            (MACRO_INSTRUCTIONS =>
                emit
                addi
                andi
                andf
                andd
                lshifti
                lshiftp
                lshiftq
                muli
                negi
                negp
                negq
                noti
                notq
                ori
                orf
                ord
                orh
                rshifti
                urshifti
                rshiftp
                urshiftp
                rshiftq
                urshiftq
                lrotatei
                lrotateq
                rrotatei
                rrotateq
                subi
                xori
                load2ia
                loadi
                loadis
                loadb
                loadbsi
                loadbsq
                loadh
                loadhsi
                loadhsq
                store2ia
                storei
                storeh
                storeb
                loadf
                loadd
                loadv
                moved
                storef
                stored
                storev
                addf
                addd
                divf
                divd
                subf
                subd
                mulf
                muld
                sqrtf
                sqrtd
                floorf
                floord
                roundf
                roundd
                truncatef
                truncated
                truncatef2i
                truncatef2q
                truncated2q
                truncated2i
                truncatef2is
                truncated2is
                truncatef2qs
                truncated2qs
                ci2d
                ci2ds
                ci2f
                ci2fs
                cq2f
                cq2fs
                cq2d
                cq2ds
                cd2f
                cf2d
                fii2d
                fd2ii
                fq2d
                fd2q
                bdeq
                bdneq
                bdgt
                bdgteq
                bdlt
                bdlteq
                bdequn
                bdnequn
                bdgtun
                bdgtequn
                bdltun
                bdltequn
                bfeq
                bfgt
                bflt
                bfgtun
                bfgtequn
                bfltun
                bfltequn
                btd2i
                td2i
                bcd2i
                movdz
                pop
                popv
                push
                pushv
                mov
                sxi2q
                zxi2q
                sxb2i
                sxh2i
                sxb2q
                sxh2q
                nop
                bieq
                bineq
                bia
                biaeq
                bib
                bibeq
                bigt
                bigteq
                bilt
                bilteq
                bbeq
                bbneq
                bba
                bbaeq
                bbb
                bbbeq
                bbgt
                bbgteq
                bblt
                bblteq
                btis
                btiz
                btinz
                btbs
                btbz
                btbnz
                jmp
                baddio
                baddis
                baddiz
                baddinz
                bsubio
                bsubis
                bsubiz
                bsubinz
                bmulio
                bmulis
                bmuliz
                bmulinz
                borio
                boris
                boriz
                borinz
                breakpoint
                call
                ret
                cbeq
                cbneq
                cba
                cbaeq
                cbb
                cbbeq
                cbgt
                cbgteq
                cblt
                cblteq
                cieq
                cineq
                cia
                ciaeq
                cib
                cibeq
                cigt
                cigteq
                cilt
                cilteq
                tis
                tiz
                tinz
                tbs
                tbz
                tbnz
                tps
                tpz
                tpnz
                peek
                poke
                bpeq
                bpneq
                bpa
                bpaeq
                bpb
                bpbeq
                bpgt
                bpgteq
                bplt
                bplteq
                addp
                mulp
                andp
                orp
                subp
                xorp
                loadp
                cpeq
                cpneq
                cpa
                cpaeq
                cpb
                cpbeq
                cpgt
                cpgteq
                cplt
                cplteq
                storep
                btps
                btpz
                btpnz
                baddpo
                baddps
                baddpz
                baddpnz
                tqs
                tqz
                tqnz
                bqeq
                bqneq
                bqa
                bqaeq
                bqb
                bqbeq
                bqgt
                bqgteq
                bqlt
                bqlteq
                addq
                mulq
                andq
                orq
                subq
                xorq
                loadq
                cqeq
                cqneq
                cqa
                cqaeq
                cqb
                cqbeq
                cqgt
                cqgteq
                cqlt
                cqlteq
                storeq
                btqs
                btqz
                btqnz
                baddqo
                baddqs
                baddqz
                baddqnz
                bo
                bs
                bz
                bnz
                leai
                leap
                memfence
                tagCodePtr
                tagReturnAddress
                untagReturnAddress
                removeCodePtrTag
                untagArrayPtr
                removeArrayPtrTag
                tzcnti
                tzcntq
                lzcnti
                lzcntq
                absf
                absd
                negf
                negd
                ceilf
                ceild
                cfeq
                cdeq
                cfneq
                cfnequn
                cdneq
                cdnequn
                cflt
                cdlt
                cflteq
                cdlteq
                cfgt
                cdgt
                cfgteq
                cdgteq
                fi2f
                ff2i
                tls_loadp
                tls_storep
            )
            (X86_INSTRUCTIONS =>
                cdqi
                idivi
                udivi
                cqoq
                idivq
                udivq
                notq
                atomicxchgaddb
                atomicxchgaddh
                atomicxchgaddi
                atomicxchgaddq
                atomicxchgsubb
                atomicxchgsubh
                atomicxchgsubi
                atomicxchgsubq
                atomicxchgb
                atomicxchgh
                atomicxchgi
                atomicxchgq
                batomicweakcasb
                batomicweakcash
                batomicweakcasi
                batomicweakcasq
                atomicweakcasb
                atomicweakcash
                atomicweakcasi
                atomicweakcasq
                atomicloadb
                atomicloadh
                atomicloadi
                atomicloadq
                fence
            )
            (ARM_INSTRUCTIONS =>
                adci
                bcs
                clrbp
                mvlbl
                globaladdr
                sbci
                moveii
                loadlinkb
                loadlinkh
                loadlinki
                loadlink2i
                storecondb
                storecondh
                storecondi
                storecond2i
                writefence
            )
            (ARM64_INSTRUCTIONS =>
                bfiq
                pcrtoaddr
                loadqinc
                loadlinkacqb
                loadlinkacqh
                loadlinkacqi
                loadlinkacqq
                storecondrelb
                storecondrelh
                storecondreli
                storecondrelq
                atomicxchgclearb
                atomicxchgclearh
                atomicxchgcleari
                atomicxchgclearq
                atomicxchgorb
                atomicxchgorh
                atomicxchgori
                atomicxchgorq
                atomicxchgxorb
                atomicxchgxorh
                atomicxchgxori
                atomicxchgxorq
                loadpairq
                loadpairi
                storepairq
                storepairi
                loadpaird
                storepaird
            )
            (RISC_INSTRUCTIONS =>
                smulli
                umulli
                addis
                subis
                oris
                addps
                divi
                divis
                divq
                divqs
                remi
                remis
                remq
                remqs
            )
            (MIPS_INSTRUCTIONS =>
                la
                movz
                movn
                setcallreg
                slt
                sltu
                pichdr
            )
            (RUST_INSTRUCTIONS =>
                callNative
                rloopCrash
                rloopDo
            )
        }
    };
}
// ($group: ident => $($instruction: ident { $($field: ident: $typ: ty),* })*)
#[macro_export]
macro_rules! instructions {
    (
        $handler: path
    ) => {
        $handler! {
            Instruction => {
                emit { pub raw: Operand },
                addi {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                andi {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                andf {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                andd {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                lshifti {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                lshiftp {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                lshiftq {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                muli {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                negi {
                    pub src_dst: Operand
                },
                negp {
                    pub src_dst: Operand
                },
                negq {
                    pub src_dst: Operand
                },
                noti {
                    pub src_dst: Operand
                },
                notq {
                    pub src_dst: Operand
                },
                ori {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                orf {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                ord {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                orh {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                rshifti {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                urshifti {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                rshiftp {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                urshiftp {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                rshiftq {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                urshiftq {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                lrotatei {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                lrotateq {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                rrotatei {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                rrotateq {
                    pub src_dst: Operand,
                    pub shift: Operand
                },
                subi {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                xori {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                load2ia {
                    pub dst: Operand,
                    pub addr: Operand
                },
                loadi {
                    pub dst: Operand,
                    pub addr: Operand
                },
                loadis {
                    pub dst: Operand,
                    pub addr: Operand
                },
                loadb {
                    pub dst: Operand,
                    pub addr: Operand
                },
                loadbsi {
                    pub dst: Operand,
                    pub addr: Operand
                },
                loadbsq {
                    pub dst: Operand,
                    pub addr: Operand,
                },
                store2ia {
                    pub addr: Operand,
                    pub src: Operand,
                },
                storei {
                    pub addr: Operand,
                    pub src: Operand,
                },
                storeh {
                    pub addr: Operand,
                    pub src: Operand,
                },
                storeb {
                    pub addr: Operand,
                    pub src: Operand,
                },
                loadf {
                    pub dst: Operand,
                    pub addr: Operand,
                },
                loadd {
                    pub dst: Operand,
                    pub addr: Operand,
                },
                loadv {
                    pub dst: Operand,
                    pub addr: Operand,
                },
                moved {
                    pub dst: Operand,
                    pub src: Operand,
                },
                storef {
                    pub addr: Operand,
                    pub src: Operand,
                },
                stored {
                    pub addr: Operand,
                    pub src: Operand,
                },
                storev {
                    pub addr: Operand,
                    pub src: Operand,
                },
                addf {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                addd {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                divf {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                divd {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                subf {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                subd {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                mulf {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                muld {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                sqrtf {
                    pub dst: Operand,
                    pub src: Operand,
                },
                sqrtd {
                    pub dst: Operand,
                    pub src: Operand,
                },
                floorf {
                    pub dst: Operand,
                    pub src: Operand,
                },
                floord {
                    pub dst: Operand,
                    pub src: Operand,
                },
                roundf {
                    pub dst: Operand,
                    pub src: Operand,
                },
                roundd {
                    pub dst: Operand,
                    pub src: Operand,
                },
                truncatef {
                    pub dst: Operand,
                    pub src: Operand,
                },
                truncated {
                    pub dst: Operand,
                    pub src: Operand,
                },
                truncatef2i {
                    pub dst: Operand,
                    pub src: Operand,
                },
                truncatef2q {
                    pub dst: Operand,
                    pub src: Operand,
                },
                truncated2q {
                    pub dst: Operand,
                    pub src: Operand,
                },
                truncated2i {
                    pub dst: Operand,
                    pub src: Operand,
                },
                truncatef2is {
                    pub dst: Operand,
                    pub src: Operand,
                },
                truncated2is {
                    pub dst: Operand,
                    pub src: Operand,
                },
                truncatef2qs {
                    pub dst: Operand,
                    pub src: Operand,
                },
                truncated2qs {
                    pub dst: Operand,
                    pub src: Operand,
                },
                ci2d {
                    pub dst: Operand,
                    pub src: Operand,
                },
                ci2ds {
                    pub dst: Operand,
                    pub src: Operand,
                },
                ci2f {
                    pub dst: Operand,
                    pub src: Operand,
                },
                ci2fs {
                    pub dst: Operand,
                    pub src: Operand,
                },
                cq2f {
                    pub dst: Operand,
                    pub src: Operand,
                },
                cq2fs {
                    pub dst: Operand,
                    pub src: Operand,
                },
                cq2d {
                    pub dst: Operand,
                    pub src: Operand,
                },
                cq2ds {
                    pub dst: Operand,
                    pub src: Operand,
                },
                cd2f {
                    pub dst: Operand,
                    pub src: Operand,
                },
                cf2d {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// usage: `fii2d <fpr>, <gpr with least significant bits>, <gpr with most significant bits>`
                fii2d {
                    pub dst: Operand,
                    pub src_lsb: Operand,
                    pub src_msb: Operand,

                },
                /// usage: `fd2ii <gpr with least significant bits>, <gpr with most significant bits>, <fpr>`
                fd2ii {
                    pub dst_lsb: Operand,
                    pub dst_msb: Operand,
                    pub src: Operand,
                },
                fq2d {
                    pub dst: Operand,
                    pub src: Operand
                },
                fd2q {
                    pub dst: Operand,
                    pub src: Operand
                },
                bdeq {
                    pub lhs: Operand,
                    pub dst: Operand,
                    pub target: Operand
                },
                bdneq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bdgt {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bdgteq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bdlt {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bdlteq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bdequn {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bdnequn {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bdgtun {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bdgtequn {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bdltun {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bdltequn {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bfeq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bfgt {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bflt {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bfgteq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bflteq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bfgtun {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bfgtequn {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bfltun {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                bfltequn {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand
                },
                btd2i {
                    pub dst: Operand,
                    pub src: Operand,
                    pub target: Operand
                },
                td2i {
                    pub dst: Operand,
                    pub src: Operand
                },
                bcd2i {
                    pub dst: Operand,
                    pub src: Operand,
                    pub target: Operand
                },
                /// Move zero to destination fpr register.
                /// Usage: `movdz <fpr>`
                movdz {
                    pub dst: Operand
                },
                /// Pop values from sp register into destination registers.
                /// Usage: `pop <gpr>, <gpr>, ...`
                pop {
                    pub dst: Operand,
                },
                /// Pop values from sp register into destination registers.
                /// Usage `popv <fpr>, <fpr>, ...`
                popv {
                    pub dst: Operand,
                },
                /// Push values from source registers to sp register.
                /// Usage: `push <gpr>, <gpr>, ...`
                push {
                    pub src: Operand,
                },
                /// Push values from source registers to sp register.
                /// Usage: `pushv <fpr>, <fpr>, ...`
                pushv {
                    pub src: Operand,
                },
                /// Move values from source register to destination register.
                /// Usage `mv <dst>, <src>`
                mv {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Sign extend i32 to i64.
                /// Usage: `sxi2q <dst>, <src>`
                sxi2q {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Zero extend i32 to i64.
                /// Usage: `zxi2q <dst>, <src>`
                zxi2q {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Sign extend i8 to i32.
                /// Usage: `sxb2i <dst>, <src>`
                sxb2i {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Sign extend i16 to i32.
                /// Usage: `sxh2i <dst>, <src>`
                sxh2i {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Sign extend i8 to i64.
                /// Usage: `sxb2q <dst>, <src>`
                sxb2q {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Sign extend i16 to i64.
                /// Usage: `sxh2q <dst>, <src>`
                sxh2q {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// No operation.
                /// Usage: `nop`
                nop {},
                /// Branch if i32 equal.
                /// Usage: `bieq <lhs>, <rhs>, <target>`
                bieq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 not equal.
                /// Usage: `bineq <lhs>, <rhs>, <target>`
                bineq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 above.
                /// Usage `bia <lhs>, <rhs>, <target>`
                bia {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 above or equal.
                /// Usage `biaeq <lhs>, <rhs>, <target>`
                biaeq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 below.
                /// Usage `bib <lhs>, <rhs>, <target>`
                bib {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 below or equal.
                /// Usage `bibeq <lhs>, <rhs>, <target>`
                bibeq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 greater.
                /// Usage `bigt <lhs>, <rhs>, <target>`
                bigt {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 greater or equal.
                /// Usage `bigteq <lhs>, <rhs>, <target>`
                bigteq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 less.
                /// Usage `bilt <lhs>, <rhs>, <target>`
                bilt {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 less or equal.
                /// Usage `bilteq <lhs>, <rhs>, <target>`
                bilteq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i8 equal.
                /// Usage `bbeq <lhs>, <rhs>, <target>`
                bbeq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i8 not equal.
                /// Usage `bbneq <lhs>, <rhs>, <target>`
                bbneq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i8 above.
                /// Usage `bba <lhs>, <rhs>, <target>`
                bba {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i8 above or equal.
                /// Usage `bbaeq <lhs>, <rhs>, <target>`
                bbaeq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i8 below.
                /// Usage `bbb <lhs>, <rhs>, <target>`
                bbb {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i8 below or equal.
                /// Usage `bbbeq <lhs>, <rhs>, <target>`
                bbbeq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i8 greater.
                /// Usage `bbgt <lhs>, <rhs>, <target>`
                bbgt {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i8 greater or equal.
                /// Usage `bbgteq <lhs>, <rhs>, <target>`
                bbgteq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i8 less.
                /// Usage `bblt <lhs>, <rhs>, <target>`
                bblt {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i8 less or equal.
                /// Usage `bblteq <lhs>, <rhs>, <target>`
                bblteq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch test if i32 sign bit is set.
                ///
                /// Usage: `btis <value>, <mask> <target>`
                btis {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Branch test if i32 is zero
                ///
                /// Usage: `btiz <value>, <mask>, <target>`
                btiz {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Branch test if i32 is non-zero.
                ///
                /// Usage: `btinz <value>, <mask>, <target>`
                btinz {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Branch test if i8 sign bit is set.
                ///
                /// Usage: `btbs <value>, <mask>, <target>`
                btbs {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Branch test if i8 is zero.
                ///
                /// Usage: `btbz <value>, <mask>, <target>`
                btbz {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Branch test if i8 is non-zero.
                ///
                /// Usage: `btbnz <value>, <mask>, <target>`
                btbnz {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Jump to target.
                ///
                /// Usage: `jmp <target>`
                jmp {
                    pub target: Operand
                },
                /// Branch if i32 add overflow.
                ///
                /// Usage: `baddio <dst>, <lhs>, <rhs>, <target>`
                baddio {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 add sign-bit is set.
                ///
                /// Usage: `baddis <dst>, <lhs>, <rhs>, <target>`
                baddis {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 add is zero.
                ///
                /// Usage: `baddiz <dst>, <lhs>, <rhs>, <target>`
                baddiz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 add is non-zero.
                ///
                /// Usage: `baddinz <dst>, <lhs>, <rhs>, <target>`
                baddinz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 sub overflow.
                ///
                /// Usage: `bsubio <dst>, <lhs>, <rhs>, <target>`
                bsubio {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 sub sign-bit is set.
                ///
                /// Usage: `bsubis <dst>, <lhs>, <rhs>, <target>`
                bsubis {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 sub is zero.
                ///
                /// Usage: `bsubiz <dst>, <lhs>, <rhs>, <target>`
                bsubiz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 sub is non-zero.
                ///
                /// Usage: `bsubinz <dst>, <lhs>, <rhs>, <target>`
                bsubinz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 mul overflow.
                ///
                /// Usage: `bmulio <dst>, <lhs>, <rhs>, <target>`
                bmulio {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 mul sign-bit is set.
                ///
                /// Usage: `bmulis <dst>, <lhs>, <rhs>, <target>`
                bmulis {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 mul is zero.
                ///
                /// Usage: `bmuliz <dst>, <lhs>, <rhs>, <target>`
                bmuliz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 mul is non-zero.
                ///
                /// Usage: `bmulinz <dst>, <lhs>, <rhs>, <target>`
                bmulinz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 or overflow.
                ///
                /// Usage: `borio <dst>, <lhs>, <rhs>, <target>`
                borio {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 or sign-bit is set.
                ///
                /// Usage: `boris <dst>, <lhs>, <rhs>, <target>`
                boris {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 or is zero.
                ///
                /// Usage: `boriz <dst>, <lhs>, <rhs>, <target>`
                boriz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i32 or is non-zero.
                ///
                /// Usage: `borinz <dst>, <lhs>, <rhs>, <target>`
                boriinz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Breakpoint.
                ///
                /// Usage: `breakpoint`
                breakpoint {},
                /// Call target.
                ///
                /// Usage: `call <target>`
                call {
                    pub target: Operand
                },
                /// Return from function.
                ///
                /// Usage: `ret`
                ret {},

                /// Compare i8 equal.
                ///
                /// Usage: `cbeq <dst>, <lhs>, <rhs>`
                cbeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i8 not equal.
                ///
                /// Usage: `cbneq <dst>, <lhs>, <rhs>`
                cbneq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i8 above.
                ///
                /// Usage: `cba <dst>, <lhs>, <rhs>`
                cba {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i8 above or equal.
                ///
                /// Usage: `cbaeq <dst>, <lhs>, <rhs>`
                cbaeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i8 below.
                ///
                /// Usage: `cbb <dst>, <lhs>, <rhs>`
                cbb {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i8 below or equal.
                ///
                /// Usage: `cbbeq <dst>, <lhs>, <rhs>`
                cbbeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i8 greater.
                ///
                /// Usage: `cbgt <dst>, <lhs>, <rhs>`
                cbgt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i8 greater or equal.
                ///
                /// Usage: `cbgteq <dst>, <lhs>, <rhs>`
                cbgteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i8 less.
                ///
                /// Usage: `cblt <dst>, <lhs>, <rhs>`
                cblt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i8 less or equal.
                ///
                /// Usage: `cblteq <dst>, <lhs>, <rhs>`
                cblteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i32 equal.
                ///
                /// Usage: `cieq <dst>, <lhs>, <rhs>`
                cieq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i32 not equal.
                ///
                /// Usage: `cineq <dst>, <lhs>, <rhs>`
                cineq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i32 above.
                ///
                /// Usage: `cia <dst>, <lhs>, <rhs>`
                cia {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i32 above or equal.
                ///
                /// Usage: `ciaeq <dst>, <lhs>, <rhs>`
                ciaeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i32 below.
                ///
                /// Usage: `cib <dst>, <lhs>, <rhs>`
                cib {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i32 below or equal.
                ///
                /// Usage: `cibeq <dst>, <lhs>, <rhs>`
                cibeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i32 greater.
                ///
                /// Usage: `cigt <dst>, <lhs>, <rhs>`
                cigt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i32 greater or equal.
                ///
                /// Usage: `cigteq <dst>, <lhs>, <rhs>`
                cigteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i32 less.
                ///
                /// Usage: `cilt <dst>, <lhs>, <rhs>`
                cilt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i32 less or equal.
                ///
                /// Usage: `cilteq <dst>, <lhs>, <rhs>`
                cilteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Test i32 sign-bit set.
                ///
                /// Usage: `tis <dst>, <value>, <mask>`
                tis {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand
                },
                /// Test i32 is zero
                ///
                /// Usage: `tiz <dst>, <value>, <mask>`
                tiz {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand
                },
                /// Test i32 is non-zero.
                ///
                /// Usage: `tinz <dst>, <value>, <mask>`
                tinz {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand
                },
                /// Test i8 sign-bit set.
                ///
                /// Usage: `tbs <dst>, <value>, <mask>`
                tbs {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand
                },
                /// Test i8 is zero.
                ///
                /// Usage: `tbz <dst>, <value>, <mask>`
                tbz {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand
                },
                /// Test i8 is non-zero.
                ///
                /// Usage: `tbnz <dst>, <value>, <mask>`
                tbnz {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand
                },

                /// Test isize sign-bit set.
                ///
                /// Usage: `tps <dst>, <value>, <mask>`
                tps {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand
                },
                /// Test isize is zero.
                ///
                /// Usage: `tpz <dst>, <value>, <mask>`
                tpz {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand
                },
                /// Test isize is non-zero.
                ///
                /// Usage: `tpnz <dst>, <value>, <mask>`
                tpnz {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand
                },

                /// Peek a value from sp.
                ///
                /// Usage: `peek <dst>`
                peek {
                    pub dst: Operand
                },
                /// Poke a value to sp.
                ///
                /// Usage: `poke <value>`
                poke {
                    pub poke: Operand
                },
                /// Branch if isize equal.
                ///
                /// Usage: `bpeq <dst>, <lhs>, <rhs>`
                bpeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Branch if isize not equal.
                ///
                /// Usage: `bpneq <dst>, <lhs>, <rhs>`
                bpneq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Branch if isize above.
                ///
                /// Usage: `bpa <dst>, <lhs>, <rhs>`
                bpa {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Branch if isize above or equal.
                ///
                /// Usage: `bpaeq <dst>, <lhs>, <rhs>`
                bpaeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Branch if isize below.
                ///
                /// Usage: `bpb <dst>, <lhs>, <rhs>`
                bpb {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Branch if isize below or equal.
                ///
                /// Usage: `bplteq <dst>, <lhs>, <rhs>`
                bpbeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Branch if isize greater.
                ///
                /// Usage: `bpgt <dst>, <lhs>, <rhs>`
                bpgt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Branch if isize greater or equal.
                ///
                /// Usage: `bpgteq <dst>, <lhs>, <rhs>`
                bpgteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Branch if isize less.
                ///
                /// Usage: `bplt <dst>, <lhs>, <rhs>`
                bplt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Branch if isize less or equal.
                ///
                /// Usage: `bplteq <dst>, <lhs>, <rhs>`
                bplteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Add isize.
                ///
                /// Usage: `addp <dst>, <lhs>, <rhs>`
                addp {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },


                /// Multiply isize.
                ///
                /// Usage: `mulp <dst>, <lhs>, <rhs>`
                mulp {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },

                /// And isize.
                ///
                /// Usage: `andp <dst>, <lhs>, <rhs>`
                andp {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },

                /// Or isize.
                ///
                /// Usage: `orp <dst>, <lhs>, <rhs>`
                orp {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                /// Subtract isize.
                ///
                /// Usage: `subp <dst>, <lhs>, <rhs>`
                subp {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                /// Xor isize.
                ///
                /// Usage: `xorp <dst>, <lhs>, <rhs>`
                xorp {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand
                },
                /// Load isize from memory.
                ///
                /// Usage: `loadp <dst>, <src>`
                loadp {
                    pub dst: Operand,
                    pub addr: Operand,
                },

                /// Compare isize equal.
                ///
                /// Usage: `cpeq <dst>, <lhs>, <rhs>`
                cpeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare isize not equal.
                ///
                /// Usage: `cpneq <dst>, <lhs>, <rhs>`
                cpneq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Compare isize above.
                ///
                /// Usage: `cpa <dst>, <lhs>, <rhs>`
                cpa {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Compare isize above or equal.
                ///
                /// Usage: `cpaeq <dst>, <lhs>, <rhs>`
                cpaeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Compare isize below.
                ///
                /// Usage: `cpb <dst>, <lhs>, <rhs>`
                cpb {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare isize below or equal.
                ///
                /// Usage: `cpbeq <dst>, <lhs>, <rhs>`
                cpbeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare isize greater.
                ///
                /// Usage: `cpgt <dst>, <lhs>, <rhs>`
                cpgt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare isize greater or equal.
                ///
                /// Usage: `cpgteq <dst>, <lhs>, <rhs>`
                cpgteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare isize less.
                ///
                /// Usage: `cplt <dst>, <lhs>, <rhs>`
                cplt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare isize less or equal.
                ///
                /// Usage: `cplteq <dst>, <lhs>, <rhs>`
                cplteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Store isize to memory.
                ///
                /// Usage: `storep <dst>, <src>`
                storep {
                    pub dst: Operand,
                    pub src: Operand,
                },

                /// Branch test if isize sign-bit set.
                ///
                /// Usage: `btps <value>, <mask>, <target>`
                btps {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },

                /// Branch test if isize is zero.
                ///
                /// Usage: `btpz <value>, <mask>, <target>`
                btpz {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Branch test if isize is non-zero.
                ///
                /// Usage: `btpnz <value>, <mask>, <target>`
                btpnz {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Branch add isize if overflow.
                ///
                /// Usage: `baddpo <dst>, <lhs>, <rhs>`
                baddpo {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Branch add isize if sign bit is set.
                ///
                /// Usage: `baddps <dst>, <lhs>, <rhs>`
                baddps {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Branch add isize if zero.
                ///
                /// Usage: `baddpz <dst>, <lhs>, <rhs>`
                baddpz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Branch add isize if non-zero.
                ///
                /// Usage: `baddpnz <dst>, <lhs>, <rhs>`
                baddpnz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Test if i64 sign-bit set.
                ///
                /// Usage: `tqs <dst>, <value>, <mask>`
                tqs {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand,
                },


                /// Test if i64 is zero.
                ///
                /// Usage: `tqz <dst>, <value>, <mask>`
                tqz {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand,
                },
                /// Test if i64 is non-zero.
                ///
                /// Usage: `tqnz <dst>, <value>, <mask>`
                tqnz {
                    pub dst: Operand,
                    pub value: Operand,
                    pub mask: Operand,
                },
                /// Branch if i64 equal.
                ///
                /// Usage: `bqeq <lhs>, <rhs>, <target>`
                bqeq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },

                /// Branch if i64 not equal.
                ///
                /// Usage: `bqneq <lhs>, <rhs>, <target>`
                bqneq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },

                /// Branch if i64 above.
                ///
                /// Usage: `bqa <lhs>, <rhs>, <target>`
                bqa {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },

                /// Branch if i64 above or equal.
                ///
                /// Usage: `bqeq <lhs>, <rhs>, <target>`
                bqaeq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },

                /// Branch if i64 below.
                ///
                /// Usage: `bqb <lhs>, <rhs>, <target>`
                bqb {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i64 below or equal.
                ///
                /// Usage: `bqbeq <lhs>, <rhs>, <target>`
                bqbeq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },

                /// Branch if i64 greater.
                ///
                /// Usage: `bqgt <lhs>, <rhs>, <target>`
                bqgt {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i64 greater or equal.
                ///
                /// Usage: `bqgteq <lhs>, <rhs>, <target>`
                bqgteq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i64 less.
                ///
                /// Usage: `bqlt <lhs>, <rhs>, <target>`
                bqlt {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch if i64 less or equal.
                ///
                /// Usage: `bqleq <lhs>, <rhs>, <target>`
                bqleq {
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },

                //// Add i64.
                ///
                /// Usage: `addq <dst>, <lhs>, <rhs>`
                addq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Multiply i64.
                ///
                /// Usage: `mulq <dst>, <lhs>, <rhs>`
                mulq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// And i64.
                ///
                /// Usage: `andq <dst>, <lhs>, <rhs>`
                andq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Or i64.
                ///
                /// Usage: `orq <dst>, <lhs>, <rhs>`
                orq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Subtract i64.
                ///
                /// Usage: `subq <dst>, <lhs>, <rhs>`
                subq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Xor i64.
                ///
                /// Usage: `xorq <dst>, <lhs>, <rhs>`
                xorq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Load i64 from memory.
                ///
                /// Usage: `loadq <dst>, <src>`
                loadq {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Compare i64 equal.
                ///
                /// Usage: `cqeq <dst>, <lhs>, <rhs>`
                cqeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i64 below or equal.
                ///
                /// Usage: `cqbeq <dst>, <lhs>, <rhs>`
                cqbeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i64 greater.
                ///
                /// Usage: `cqgt <dst>, <lhs>, <rhs>`
                cqgt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i64 greater or equal.
                ///
                /// Usage: `cqgteq <dst>, <lhs>, <rhs>`
                cqgteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i64 less.
                ///
                /// Usage: `cqlt <dst>, <lhs>, <rhs>`
                cqlt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare i64 less or equal.
                ///
                /// Usage: `cqlteq <dst>, <lhs>, <rhs>`
                cqlteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Store i64 to memory.
                ///
                /// Usage: `storeq <dst>, <src>`
                storeq {
                    pub dst: Operand,
                    pub src: Operand,
                },

                /// Branch test if i64 sign-bit set.
                ///
                /// Usage: `btqs <value>, <mask>, <target>`
                btqs {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Branch test if i64 is zero.
                ///
                /// Usage: `btqz <value>, <mask>, <target>`
                btqz {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Branch test if i64 is non-zero.
                ///
                /// Usage: `btqnz <value>, <mask>, <target>`
                btqnz {
                    pub value: Operand,
                    pub mask: Operand,
                    pub target: Operand,
                },
                /// Branch add i64 if overflow.
                ///
                /// Usage: `baddqo <dst>, <lhs>, <rhs>, <target>`
                baddqo {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch add i64 if sign-bit set.
                ///
                /// Usage: `baddqs <dst>, <lhs>, <rhs>, <target>`
                baddqs {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch add i64 if zero.
                ///
                /// Usage: `baddqz <dst>, <lhs>, <rhs>, <target>`
                baddqz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },
                /// Branch add i64 if non-zero.
                ///
                /// Usage: `baddqnz <dst>, <lhs>, <rhs>, <target>`
                baddqnz {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                    pub target: Operand,
                },

                /// Branch if overflow flag is set.
                ///
                /// Usage: `bo <target>`
                bo {
                    pub target: Operand,
                },
                /// Branch if sign-bit flag is set.
                ///
                /// Usage: `bs <target>`
                bs {
                    pub target: Operand,
                },
                /// Branch if zero flag is set.
                ///
                /// Usage: `bz <target>`
                bz {
                    pub target: Operand,
                },
                /// Branch if non-zero flag is set.
                ///
                /// Usage: `bnz <target>`
                bnz {
                    pub target: Operand,
                },

                /// Load 32-bit effective address.
                ///
                /// Usage: `leai <dst>, <src>`
                leai {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Load 64-bit effective address.
                ///
                /// Usage: `leap <dst>, <src>`
                leap {
                    pub dst: Operand,
                    pub src: Operand,
                },

                /// Memory fence.
                memfence {},

                /// Count trailing zero bits in i32.
                ///
                /// Usage: `tzcnti <dst>, <src>`
                tzcnti {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Count trailing zero bits in i64.
                ///
                /// Usage: `tzcntq <dst>, <src>`
                tzcntq {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Count leading zero bits in i32.
                ///
                /// Usage: `lzcnti <dst>, <src>`
                lzcnti {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Count leading zero bits in i64.
                ///
                /// Usage: `lzcntq <dst>, <src>`
                lzcntq {
                    pub dst: Operand,
                    pub src: Operand,
                },

                /// Absolute value f32.
                ///
                /// Usage: `absf <dst>, <src>`
                absf {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Absolute value f64.
                ///
                /// Usage: `absd <dst>, <src>`
                absd {
                    pub dst: Operand,
                    pub src: Operand,
                },

                /// Negate f32.
                ///
                /// Usage: `negf <dst>, <src>`
                negf {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Negate f64.
                ///
                /// Usage: `negd <dst>, <src>`
                negd {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Ceiling f32.
                ///
                /// Usage: `ceilf <dst>, <src>`
                ceilf {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Ceiling f64.
                ///
                /// Usage: `ceild <dst>, <src>`
                ceild {
                    pub dst: Operand,
                    pub src: Operand,
                },
                /// Compare f32 equal.
                ///
                /// Usage: `cfeq <dst>, <lhs>, <rhs>`
                cfeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare f64 equal.
                ///
                /// Usage: `cdeq <dst>, <lhs>, <rhs>`
                cdeq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare f32 not equal.
                ///
                /// Usage: `cfneq <dst>, <lhs>, <rhs>`
                cfneq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare f32 not equal unordered.
                ///
                /// Usage: `cfnequn <dst>, <lhs>, <rhs>`
                cfnequn {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare f64 not equal.
                ///
                /// Usage: `cdneq <dst>, <lhs>, <rhs>`
                cdneq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare f64 not equal unordered.
                ///
                /// Usage: `cdnequn <dst>, <lhs>, <rhs>`
                cdnequn {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Compare f32 less.
                ///
                /// Usage: `cflt <dst>, <lhs>, <rhs>`
                cflt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare f64 less.
                ///
                /// Usage: `cdlt <dst>, <lhs>, <rhs>`
                cdlt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Compare f32 less or equal.
                ///
                /// Usage: `cflteq <dst>, <lhs>, <rhs>`
                cflteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare f64 less or equal.
                ///
                /// Usage: `cdlteq <dst>, <lhs>, <rhs>`
                cdlteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare f32 greater.
                ///
                /// Usage: `cfgt <dst>, <lhs>, <rhs>`
                cfgt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare f64 greater.
                ///
                /// Usage: `cdgt <dst>, <lhs>, <rhs>`
                cdgt {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },
                /// Compare f32 greater or equal.
                ///
                /// Usage: `cfgteq <dst>, <lhs>, <rhs>`
                cfgteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                /// Compare f64 greater or equal.
                ///
                /// Usage: `cdgteq <dst>, <lhs>, <rhs>`
                cdgteq {
                    pub dst: Operand,
                    pub lhs: Operand,
                    pub rhs: Operand,
                },

                fi2f {
                    pub dst: Operand,
                    pub src: Operand,
                },

                ff2i {
                    pub dst: Operand,
                    pub src: Operand,
                },

                tls_loadp {
                    pub dst: Operand,
                    pub src: Operand,
                },
                tls_storep {
                    pub dst: Operand,
                    pub src: Operand,
                }
            }

        }
    };
}

use proc_macro2::Span;
macro_rules! define_instructions {
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
                    $(#[$outer])*
                    #[derive(Clone)]
                    pub struct [<$ins: camel>] {
                        pub span: Span,
                        $(
                            $(#[$inner])*
                            $v $name: $t
                        ),*
                    }

                    impl syn::parse::Parse for [<$ins:camel>] {
                        #[allow(unused_variables, unused_mut, unused_assignments, dead_code)]
                        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                            let span = input.span();
                            let _ = input.parse::<[<$group:lower _kw>]::$ins>()?;
                            let mut count = 0;
                            $(
                                let _ = stringify!($name);
                                count += 1;
                            )*

                            let mut didread = 0;
                            $(
                                let $name = input.parse::<$t>()?;
                                didread += 1;
                                if didread < count {
                                    let _ = input.parse::<syn::Token![,]>()?;
                                }
                            )*
                            Ok(Self {
                                span,
                                $(
                                    $name
                                ),*
                            })
                        }
                    }

                    pub fn $ins($($name: impl Into<$t>),*) -> [<$ins:camel>] {
                        [<$ins:camel>]::new($($name.into()),*)
                    }

                    impl [<$ins:camel>] {
                        pub const NAME: &str = stringify!($ins);

                        pub fn new($($name: $t),*) -> Self {
                            Self {
                                span: Span::call_site(),
                                $(
                                    $name
                                ),*
                            }
                        }

                        pub fn with_span(mut self, span: Span) -> Self {
                            self.span = span;
                            self
                        }

                        pub fn span(&self) -> Span {
                            self.span
                        }

                        pub fn map<F>(&self, mut _f: F) -> Self
                        where F: FnMut(Operand) -> Operand {
                            Self {
                                span: self.span.clone(),
                                $(
                                    $name: _f(self.$name.clone())
                                ),*

                            }
                        }
                        #[allow(unused_mut, unused_assignments)]
                        pub fn operands(&self) -> SmallVec<[&Operand; 4]> {
                            let mut operands = SmallVec::new();
                            $(
                                operands.push(&self.$name);
                            )*
                            operands
                        }
                    }

                    impl<F> MapOperands<F> for [<$ins:camel>]
                    where F: FnMut(Operand) -> Operand {
                        fn map_operands(&self, mut _f: F) -> Self {
                            Self {
                                span: self.span.clone(),
                                $(
                                    $name: _f(self.$name.clone())
                                ),*
                            }
                        }
                        
                    }

                    impl<F, E> TryMapOperands<F, E> for [<$ins:camel>]
                    where F: FnMut(Operand) -> Result<Operand, E> {
                        fn try_map_operands(&self, mut _f: F) -> Result<Self, E> {
                            Ok(Self {
                                span: self.span.clone(),
                                $(
                                    $name: _f(self.$name.clone())?
                                ),*
                            })
                        }
                    }

                    impl<F> ForEachOperand<F> for [<$ins:camel>]
                    where F: FnMut(&Operand) {
                        fn for_each_operand(&self, mut _f: F) {
                            $(
                                _f(&self.$name);
                            )*
                        }
                    }

                    impl TryForEachOperand for [<$ins:camel>] {
                        fn try_for_each_operand<F, E>(&self, mut _f: F) -> Result<(), E>
                        where
                            F: FnMut(&Operand) -> Result<(), E>,
                        {
                            $(
                                _f(&self.$name)?;
                            )*
                            Ok(())
                        }
                    }

                    impl Display for [<$ins:camel>] {
                        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                            write!(f, "{}", Self::NAME)?;
                            let operands: &[&Operand] = &[$(&self.$name),*];
                            write!(f, " {}", operands.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "))?;

                            Ok(())
                        }
                    }


                }
            )*
            paste::paste! {
                #[derive(Clone)]
                pub enum [<$group:camel>] {
                    $(
                        [<$ins:camel>]([<$ins:camel>])
                    ),*
                }

                impl syn::parse::Parse for [<$group:camel>] {
                    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                        $(
                            if input.peek([<$group:lower _kw>]::$ins) {
                                return Ok(Self::[<$ins:camel>](input.parse::<[<$ins:camel>]>()?));
                            }
                        )*

                        Err(syn::Error::new(input.span(), "Invalid instruction"))
                    }
                }

                impl Display for [<$group:camel>] {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        match self {
                            $(
                                Self::[<$ins:camel>](ins) => write!(f, "{}", ins),
                            )*
                        }
                    }
                }

                $(impl From<[<$ins:camel>]> for [<$group:camel>] {
                    fn from(ins: [<$ins:camel>]) -> Self {
                        Self::[<$ins:camel>](ins)
                    }
                })*

                $(impl From<[<$ins:camel>]> for $crate::stmt::Stmt {
                    fn from(ins: [<$ins:camel>]) -> Self {
                        Self::Instruction(std::rc::Rc::new(ins.into()))
                    }
                })*

                impl<F> MapOperands<F> for [<$group:camel>]
                where F: FnMut(Operand) -> Operand {
                    fn map_operands(&self, mut _f: F) -> Self {
                        match self {
                            $(
                                Self::[<$ins:camel>](ins) => Self::[<$ins:camel>](ins.map_operands(_f)),
                            )*
                        }
                    }
                }

                impl<F, E> TryMapOperands<F, E> for [<$group:camel>]
                where F: FnMut(Operand) -> Result<Operand, E> {
                    fn try_map_operands(&self, mut _f: F) -> Result<Self, E> {
                        match self {
                            $(
                                Self::[<$ins:camel>](ins) => Ok(Self::[<$ins:camel>](ins.try_map_operands(_f)?)),
                            )*
                        }
                    }
                }

                impl<F> ForEachOperand<F> for [<$group:camel>]
                where F: FnMut(&Operand) {
                    fn for_each_operand(&self, mut _f: F) {
                        match self {
                            $(
                                Self::[<$ins:camel>](ins) => ins.for_each_operand(_f),
                            )*
                        }
                    }
                }

                impl TryForEachOperand for [<$group:camel>] {
                    fn try_for_each_operand<F, E>(&self, mut _f: F) -> Result<(), E>
                    where
                        F: FnMut(&Operand) -> Result<(), E>,
                    {
                        match self {
                            $(
                                Self::[<$ins:camel>](ins) => ins.try_for_each_operand(_f),
                            )*
                        }
                    }
                }

                impl [<$group:camel>] {
                    pub fn span(&self) -> Span {
                        match self {
                            $(
                                Self::[<$ins:camel>](ins) => ins.span(),
                            )*
                        }
                    }

                    $(
                        pub fn [<as_ $ins>](&self) -> &[<$ins:camel>] {
                            match self {
                                Self::[<$ins:camel>](ins) => ins,
                                _ => panic!("Invalid instruction, expected: {}, got: {}", [<$ins:camel>]::NAME, self),
                            }
                        }

                        pub fn [<try_as_$ins>](&self) -> Option<&[<$ins:camel>]> {
                            match self {
                                Self::[<$ins:camel>](ins) => Some(ins),
                                _ => None,
                            }
                        }
                    )*

                    pub fn operands(&self) -> SmallVec<[&Operand; 4]> {
                        match self {
                            $(
                                Self::[<$ins:camel>](ins) => ins.operands(),
                            )*
                        }
                    }
                }

                pub mod [<$group:snake _kw>] {
                    use super::*;
                    $(
                        syn::custom_keyword!($ins);
                    )*

                    impl [<$group:camel>] {
                        pub fn peek(input: syn::parse::ParseStream) -> bool {
                            $(
                                if input.peek($ins) {
                                    return true;
                                }
                            )*

                            false
                        }

                        pub fn peek2(input: syn::parse::ParseStream) -> bool {
                            $(
                                if input.peek2($ins) {
                                    return true;
                                }
                            )*

                            false
                        }

                        pub fn peek3(input: syn::parse::ParseStream) -> bool {
                            $(
                                if input.peek3($ins) {
                                    return true;
                                }
                            )*

                            false
                        }
                    }
                }
            }
        )*
    };
}

use super::operands::*;
use std::fmt::Display;

use smallvec::SmallVec;
instructions!(define_instructions);

pub trait MapOperands<F>: Sized
where
    F: FnMut(Operand) -> Operand,
{
    fn map_operands(&self, f: F) -> Self;
}

pub trait TryMapOperands<F, E>: Sized
where
    F: FnMut(Operand) -> Result<Operand, E>,
{
    fn try_map_operands(&self, f: F) -> Result<Self, E>;
}

pub trait ForEachOperand<F>
where
    F: FnMut(&Operand),
{
    fn for_each_operand(&self, f: F);
}

pub trait TryForEachOperand
{
    fn try_for_each_operand<F, E>(&self, f: F) -> Result<(), E>
    where
        F: FnMut(&Operand) -> Result<(), E>;
}
