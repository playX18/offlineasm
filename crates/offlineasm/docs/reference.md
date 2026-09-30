<!-- Packaging copy of docs/reference.md. Edit the root file and re-copy. -->

# Instruction reference

Instruction reference for offlineasm and onlineasm.
## Conventions

### Operands

`O1` is the first operand written in the assembly, `O2`, `O3`, `O4` the following ones, in the order they are written in. `O1` is
the destination wherever the mnemonic has one. `t0`, `t1`, `t2` are the ISA-implicit registers used
by the multiply/divide family.

- `op O1, O2` is `O1 = O1 <op> O2`. `op O1, O2, O3` is `O1 = O2 <op> O3`.
- Registers fall in three portable classes: general-purpose (`t0`-`t12`, `csr0`-`csr10`, and the
  special registers `cfr`, `sp`, `lr`, `zr`, `zero`, `fp`, `tp`), floating-point (`ft0`-`ft7`,
  `csfr0`-`csfr7`), and 128-bit vector (`v0`-`v7`). Every name is a fixed alias for a physical
  register of the selected target. See [Registers](#registers) for full mapping of them.
- Operand kinds are: 
  - `m` memory (`off[base]`, `off[base, index, scale]`, `off[]`)
  - `imm` immediate
  - `lbl` code label
  - `ext` external symbol (see [External symbols](#external-symbols))
  - `addr` any addressable source.
- Letter at the end of instruction specifies its width: `b` 8 bit, `h` 16, `i` 32, `q` 64, `p` 64 (pointer), `f` `f32`, `d`
  `f64`, `v` 128-bit vector.
- Branch names start with `b`, except `bswap*` and `bfiq`. 
  - `c*` compares and writes `0`/`1` to a register. 
  - `t*` tests a bit, and writes `0`/`1` to a register. 
  - `bt*` is a test + branch, which does not write to register.  
- `UInt()` and `SInt()` denote an unsigned or signed integers respectively.
- `IsUnordered()` is true when FP operand is NaN.



### Types and accessors

- `bits(N)`, `integer`, `boolean` are primitive types, where `bits(N)` denote integer of width N.
- `X[n]` - is a view of operand `n` as 64-bit integer. 
- `X[n]<hi:lo>` selects a bit slice (e.g. `X[n]<31:0>` is the 32-bit view).
- `V[n]` - 128-bit view of operand `n`'s vector/FP register. `V[n]<31:0>` and `V[n]<63:0>` are its
  `f32`/`f64` views.
- `Mem[address, size]` - a `size`-byte memory access at `address`. `size` is `1`/`2`/`4`/`8`/`16`
  (or `32` for a 256-bit pair store).
- `PC`, `LR`, `SP` - the implicit program counter, link register, and stack pointer.
- `FLAG` - `bits(4)` of `N:Z:C:V` (negative, zero, carry, overflow), the synthesized condition
  state written by the `*s`/compare/test family. `FLAG.N`, `FLAG.Z`, `FLAG.C`, `FLAG.V`
  name the individual bits.

### Shared subroutines

- `(bits(N), bits(4)) AddWithCarry(bits(N) x, bits(N) y, bit carry_in)` - computes `x + y +
  carry_in` and returns the result together with the `N:Z:C:V` flags it produces. Subtraction is
  `AddWithCarry(x, NOT(y), '1')`.
- `(bits(N), bit) MulWithOverflow(bits(N) x, bits(N) y)` - a full-width multiply together with
  whether the truncated `N`-bit result differs from the true product (signed overflow).
- `ZeroExtend(bits(M) x, integer N)` / `SignExtend(bits(M) x, integer N)` - widen `x` to `N` bits.
- `IsZeroBit(bits(N) x)` - `x == 0`, as a single bit usable in `X[n] = if ... then 1 else 0`.
- `Min(x, y)`, `Max(x, y)`, `Abs(x)` - minimum/maximum out of `x` and `y`, or absolute value of `x`.
- `RotateLeft(bits(N) x, integer amount)`, `RotateRight(bits(N) x, integer amount)`,
  `ByteReverse(bits(N) x)`.
- `CountLeadingZeroBits(bits(N) x)`, `CountTrailingZeroBits(bits(N) x)`, `BitCount(bits(N) x)` - clz, ctz, popcount.
- `Sqrt()`, `RoundToNearest()`, `FloorToIntegral()`, `CeilToIntegral()`, `TruncateToIntegral()` - the IEEE-754 rounding operations.
- `FPToFixed(bits(N) x, integer M, rounding)` / `FixedToFP(integer x, integer N)` - float-to-
  integer and integer-to-float conversion; `FPConvert(bits(N) x, integer M)` converts between
  float widths. `InexactConversion()` reports whether the most recent `FPToFixed` lost precision.
- `EffectiveAddress(m)` - the address denoted by a memory operand `m` (`off[base]`,
  `off[base, index, scale]`), computed without accessing memory. `GlobalAddress(sym)` resolves a
  global symbol's address at link/lowering time. `TLSBase()` is the platform's thread-local
  storage base.
- `Acquire(location)` / `Release(location) = value` - a load/store with acquire/release memory
  ordering.
- `AcquireExclusive(location)` / `(boolean) ReleaseExclusive(location) = value` - an exclusive
  (linked) load and its paired conditional store, returning whether the store succeeded.
- `Barrier(kind)` - a memory barrier, `kind` is `Full` (`memfence`) or `Sync` (`fence`).
  `SpinLoopHint()` is `pause`'s CPU hint. `Trap()` raises a trap. `CallNative()`/`CallSlowPath()`/
  `SuspendLoop()` are the `rloop` backend's host-call primitives. `EmitRawText()` is `emit`'s raw
  text splice.
- `BranchTo(target)` - transfers control to `target`.

## Registers

offlineasm and onlineasm have the same set of registers available. The availability of register is dependent on target platform. 

If you require access to a register by its raw platform name instead of its portable name, use
the `%` prefix: `move %rax, 42`.

The `X[n]`/`V[n]` accessors used throughout this reference address these same portable registers
by operand position; the tables below give the physical register each portable name maps to.

### General-purpose registers

|  | x86-64 | AArch64 | RISC-V 64 |
| ---| ---| ---| --- |
| `t0` | `rax` | `x0` | `x10` |
| `t1` | `rsi` | `x1` | `x11` |
| `t2` | `rdx` | `x2` | `x12` |
| `t3` | `rcx` | `x3` | `x13` |
| `t4` | `r8` | `x4` | `x14` |
| `t5` | `r10` | `x5` | `x15` |
| `t6` | `rdi` | `x6` | `x16` |
| `t7` | `r9` | `x7` | `x17` |
| `t8` | - | `x8` | `x5` |
| `t9` | - | `x9` | `x6` |
| `t10` | - | `x10` | `x7` |
| `t11` | - | `x11` | - |
| `t12` | - | `x12` | - |
| `csr0` | `rbx` | `x19` | `x18` |
| `csr1` | `r12` | `x20` | `x19` |
| `csr2` | `r13` | `x21` | `x20` |
| `csr3` | `r14` | `x22` | `x21` |
| `csr4` | `r15` | `x23` | `x22` |
| `csr5` | `rsi` | `x24` | `x23` |
| `csr6` | `rdi` | `x25` | `x24` |
| `csr7` | - | `x26` | `x25` |
| `csr8` | - | `x27` | `x26` |
| `csr9` | - | `x28` | `x27` |
| `csr10` | - | - | `x9` |
| `cfr` | `rbp` | `x29` | `x8` |
| `sp` | `rsp` | `sp` | `x2` |
| `lr` | - | `x30` | `x1` |
| `zr` | - | `xzr` | - |
| `zero` | - | - | `x0` |
| `tp` | - | - | `x4` |
| `fp` | - | - | `x8` |

`t0`-`t12` are caller-saved temporaries, `csr0`-`csr10` callee-saved. The rest are
- `cfr` is the frame pointer (`rbp`, `x29`, `x8`), 
- `sp` the stack pointer (`rsp`, `sp`, `x2`).
- `lr` the link register (AArch64 and RISC-V only),
- `fp` a RISC-V alias of `cfr`.
- `tp` the RISC-V thread pointer.
- `zr`/`zero` read as zero and discard writes.

### Floating-point and vector registers

| portable | x86-64 | AArch64 | RISC-V 64 |
| ---| ---| ---| --- |
| `ft0` | `xmm0` | `v0` | `f8` |
| `ft1` | `xmm1` | `v1` | `f10` |
| `ft2` | `xmm2` | `v2` | `f12` |
| `ft3` | `xmm3` | `v3` | `f14` |
| `ft4` | `xmm4` | `v4` | `f16` |
| `ft5` | `xmm5` | `v5` | `f18` |
| `ft6` | `xmm6` | `v6` | `f20` |
| `ft7` | `xmm7` | `v7` | `f22` |
| `csfr0` | - | `v8` | `f1` |
| `csfr1` | - | `v9` | `f3` |
| `csfr2` | - | `v10` | `f5` |
| `csfr3` | - | `v11` | `f7` |
| `csfr4` | - | `v12` | `f9` |
| `csfr5` | - | `v13` | `f11` |
| `csfr6` | - | `v14` | `f13` |
| `csfr7` | - | `v15` | `f15` |
| `v0` | `xmm0` | `v16` | `f0` |
| `v1` | `xmm1` | `v17` | `f2` |
| `v2` | `xmm2` | `v18` | `f4` |
| `v3` | `xmm3` | `v19` | `f6` |
| `v4` | `xmm4` | `v20` | `f24` |
| `v5` | `xmm5` | `v21` | `f26` |
| `v6` | `xmm6` | `v22` | `f28` |
| `v7` | `xmm7` | `v23` | `f30` |

### Callee-saved registers

These registers must be preserved by the callee using `pushCalleeSaves` or `popCalleeSaves` (or use push/pop manually).

| target | general-purpose | floating-point |
| --- | --- | --- |
| x86-64 (System V) | `csr0`-`csr4` | - |
| x86-64 (Windows x64) | `csr0`-`csr6` | - |
| AArch64 (AAPCS64) | `csr0`-`csr9` | `csfr0`-`csfr7` |
| RISC-V 64 | `csr0`-`csr10` | `csfr0`-`csfr7` |

`cfr` and `sp` are also preserved by the ABI, but they are not always required (e.g leaf functions), thus are not in pushCalleeSaves/popCalleeSaves requirements.

x86-64 also has no `csfr` registers which are floating point calle saved registers, as only Windows calling convention treats them as calle saved, and we do not expose `xmm6` to `xmm15` in the portable syntax, instead save them manually if you use them via `%` prefix. 

### Scratch and reserved registers

onlineasm/offlineasm sometimes need a register for materialization, or staging an operand e.g for division on x64. For this we reserve one or two machine registers. 

These registers are generally not recommended to be used in raw way (via `%r11` for example), as at any point of program they can be clobbered. Each numbered section below opens with a "Scratch registers" table listing which scratch registers its instructions clobber and when; consult it to know where it is safe, and where you have to save the register. 

| target | scratch GPR | scratch FPR |
| --- | --- | --- |
| x86-64 | `r11` | `xmm7` |
| AArch64 | `x16`, `x17` | `v31` |
| RISC-V 64 | `x29`, `x31` | `f31` |

- x86-64: 
  - `%r11` GPR expansion scratch.
  - `%xmm7`: FPR expansion scratch
- AArch64: 
  - `%x16`: GPR expansion scratch
  - `%x17` second GPR expansion scratch
  - `%x18` the platform register
  - `%q31`, `%d31`, `%s31`, `%v31`: FPR  expansion scratch
- RISC-V 64: 
  - `%x3`/`%gp`: psABI's reserved `gp` 
  - `%x29`: expansion scratch 
  - `%x30`: flags register
  - `%x31`/`%t6`: expansion scratch 
  - `%f31`/`%ft11`: FPR expansion scratch

*NOTE on rloop: it has no native registers, so `%` prefix has no effect and will produce an error during lowering.

## External symbols

An external symbol is a function or data object outside the code being assembled. It is a
`jmp`/`call` target, or the source of `move`, `leap`, `globaladdr`, and `la`, which take its address.

offlineasm declares one per file with `extern _name` (far) or `extern near _name`, and then uses it
like a label: `call _name`. A declared name cannot also be defined or declared `global` in the same file. rloop does not support external symbols. 

onlineasm uses asmkit's `ExternalName` as external names. `Assembler::extern_far`, `Assembler::extern_near`, and
`Assembler::extern_name` declare one and return an `Extern` operand. In `onlineasm!`,
`extern name = {expr};` (or `extern near name = {expr};`) binds it to `name`, and
`call extern {expr}` (or `extern near {expr}`) declares one in place. 

Once you are done emitting code `Finished::load` will allow you to manually resolve all declared extern names. `LoadedCode::rebind` allows to point **far** entries to a new address.

A **far** extern is reached through a pointer-sized slot in an address table, so it can be anywhere. onlineasm places the table right after the code. offlineasm uses the linker's GOT on ELF
and Mach-O, and on COFF emits a slot in `.rdata` with the
same instructions. A **near** extern is a direct PC-relative reference and must be in range of the
code: ±2 GiB on x86-64 and RISC-V 64, and on AArch64 ±128 MiB for `bl`/`b` and ±4 GiB for `adrp`.
onlineasm fails to load an image whose near extern is out of range.

Position-independent code (the `PIC` setting in offlineasm, `AssemblerOptions::with_pic` in
onlineasm) reaches every extern through the table, as if it were declared far.

| target | address (`leap`, `move`, ...) | `call` / `jmp` |
| --- | --- | --- |
| x86-64 near | `lea d, [rip + sym]` | `call sym` / `jmp sym` |
| x86-64 far | `mov d, qword ptr [rip + sym@GOTPCREL]` | `call`/`jmp qword ptr [rip + sym@GOTPCREL]` |
| AArch64 near | `adrp d, sym` + `add d, d, :lo12:sym` | `bl sym` / `b sym` |
| AArch64 far | `adrp d, :got:sym` + `ldr d, [d, :got_lo12:sym]` | the far address into `x16`, then `blr`/`br x16` |
| RISC-V 64 near | `lla d, sym` | `call sym` / `jump sym, x31` |
| RISC-V 64 far | `lga d, sym` | the far address into `x31`, then `jalr` |

## 1. Memory operations

### Scratch registers

An address *needs folding* when one memory operand cannot encode it, so
the backend computes it into a scratch register first. On AArch64 that is
an index whose scale is neither 1 nor the access size, an index together
with an offset, an offset outside both the scaled unsigned 12-bit and the
unscaled ±256 forms, or an absolute address. On RISC-V 64
it is any index, an offset outside ±2 KiB, or an absolute address. x86-64
never folds.

Loads and stores: `move`, `loadi`, `loadp`, `loadq`, `zxi2q`, `storei`,
`storep`, `storeq`, `storeh`, `storeb`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | value stored to memory is an immediate that does not fit the store (64-bit: signed 32 bits), a label, or memory |
| AArch64 | `x16` | address needs folding |
| AArch64 | `x17` | value stored to memory is an immediate (any value) or memory |
| RISC-V 64 | `x31` | address needs folding; value stored to memory is an immediate (any value) |
| RISC-V 64 | `x29` | immediate stored through an address that needs folding |

Atomic loads: `atomicloadb`, `atomicloadh`, `atomicloadi`, `atomicloadq`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | `x16` | address has any offset or index (`ldar` takes only `[Xn]`) |
| RISC-V 64 | `x31` | address needs folding |

Extending loads and extensions: `loadis`, `loadb`, `loadbsi`, `loadbsq`,
`loadh`, `loadhsi`, `loadhsq`, `sxb2i`, `sxh2i`, `sxb2q`, `sxb2p`,
`sxh2q`, `sxi2q`, `zxb2i`, `zxh2i`, `zxb2q`, `zxh2q`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | `x16` | source is memory (loaded into `x16`, then extended) or an immediate |
| RISC-V 64 | `x31` | source is memory (loaded into `x31`, then extended) or an immediate |

Transfers: `transferi`, `transferp`, `transferq`. The shared expansion
stages every non-register source through the first scratch register.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | source is memory, an immediate, or a label |
| AArch64 | `x16` | source is memory, an immediate, or a label; memory destination needs folding |
| RISC-V 64 | `x31` | source is memory, an immediate, or a label; either address needs folding |
| RISC-V 64 | `x29` | staged source stored through a destination address that needs folding |

Float and vector moves: `loadf`, `loadd`, `moved`, `storef`, `stored`,
`loadv`, `storev`, `movev`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | `x16` | address needs folding |
| RISC-V 64 | `x31` | address needs folding (`loadv`/`storev`: either 8-byte half) |
| RISC-V 64 | `f31` | `storev` through an address that needs folding |

Address computation: `leai`, `leap`, `pcrtoaddr`, `globaladdr`, `la`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | `x16` | address is anything but a bare base register (a label or extern goes straight into the destination) |
| RISC-V 64 | `x31` | unindexed address whose offset is outside ±2 KiB and whose base is the destination |

Pair loads and stores: `loadpairq`, `loadpairp`, `loadpairi`,
`loadpaird`, `loadpairv`, `storepairq`, `storepairp`, `storepairi`,
`storepaird`, `storepairv`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | integer pair load whose first destination is the base or index and whose second destination is the same register or the other address register |
| AArch64 | `x16` | address has an index, is absolute, or its offset is not a multiple of the element size within ±64 elements; integer pair load into the same register twice |
| AArch64 | `v31` | `loadpaird`/`loadpairv` into the same register twice |
| RISC-V 64 | `x31` | address has an index, is absolute, or either half's offset is outside ±2 KiB |

Stack operations: `push`, `pop`, `pushv`, `popv`, `pushCalleeSaves`,
`popCalleeSaves`, `peek`, `poke`. `pushv`, `popv`, `pushCalleeSaves`, and
`popCalleeSaves` never clobber scratch registers. RISC-V 64 `push`/`pop`
accept only registers.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | `push` of an immediate that does not fit signed 32 bits, or of a label |
| AArch64 | `x16` | `push` of an immediate or memory operand in the lower slot of a pair; memory operand address needs folding; `peek`/`poke` offset is not a multiple of 8 in 0..32760 |
| AArch64 | `x17` | `push` of an immediate or memory operand in the upper slot of a pair; `pop` into memory |
| RISC-V 64 | `x31` | `peek`/`poke` offset is outside ±2 KiB |

Thread-local slots: `tls_loadb`, `tls_loadh`, `tls_loadi`, `tls_loadp`
(`tls_loadq`), `tls_storeb`, `tls_storeh`, `tls_storei`, `tls_storep`
(`tls_storeq`), `tls_leap`. The offset being "out of range" means
not a multiple of the access size in `0..4096 * size` for AArch64
loads/stores, outside ±4095 for AArch64 `tls_leap`, and outside ±2 KiB on
RISC-V 64. On x86-64 the offset has to fit a signed 32-bit displacement.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | `x16` | always (holds the thread pointer) |
| AArch64 | `x17` | offset out of range |
| RISC-V 64 | `x31` | offset out of range |
| RISC-V 64 | `x29`, `f31` | `tls_store*` with the offset out of range |

### `move O1, O2`

```text
X[O1] = X[O2];
```

### `loadi O1, O2`

```text
bits(64) address = X[O2];
X[O1] = ZeroExtend(Mem[address, 4], 64);
```

### `loadp O1, O2`

```text
bits(64) address = X[O2];
X[O1] = Mem[address, 8];
```

### `loadq O1, O2`

```text
bits(64) address = X[O2];
X[O1] = Mem[address, 8];
```

### `atomicloadb O1, O2`

```text
bits(64) address = X[O2];
X[O1] = ZeroExtend(Acquire(Mem[address, 1]), 64);
```

### `atomicloadh O1, O2`

```text
bits(64) address = X[O2];
X[O1] = ZeroExtend(Acquire(Mem[address, 2]), 64);
```

### `atomicloadi O1, O2`

```text
bits(64) address = X[O2];
X[O1] = ZeroExtend(Acquire(Mem[address, 4]), 64);
```

### `atomicloadq O1, O2`

```text
bits(64) address = X[O2];
X[O1] = Acquire(Mem[address, 8]);
```

### `loadis O1, O2`

```text
bits(64) address = X[O2];
X[O1] = SignExtend(Mem[address, 4], 64);
```

### `loadb O1, O2`

```text
bits(64) address = X[O2];
X[O1] = ZeroExtend(Mem[address, 1], 64);
```

### `loadbsi O1, O2`

```text
bits(64) address = X[O2];
X[O1] = SignExtend(Mem[address, 1], 64);
```

### `loadbsq O1, O2`

```text
bits(64) address = X[O2];
X[O1] = SignExtend(Mem[address, 1], 64);
```

### `loadh O1, O2`

```text
bits(64) address = X[O2];
X[O1] = ZeroExtend(Mem[address, 2], 64);
```

### `loadhsi O1, O2`

```text
bits(64) address = X[O2];
X[O1] = SignExtend(Mem[address, 2], 64);
```

### `loadhsq O1, O2`

```text
bits(64) address = X[O2];
X[O1] = SignExtend(Mem[address, 2], 64);
```

### `storei O1, O2`

```text
bits(64) address = X[O1];
Mem[address, 4] = X[O2]<31:0>;
```

### `storep O1, O2`

```text
bits(64) address = X[O1];
Mem[address, 8] = X[O2];
```

### `storeq O1, O2`

```text
bits(64) address = X[O1];
Mem[address, 8] = X[O2];
```

### `storeh O1, O2`

```text
bits(64) address = X[O1];
Mem[address, 2] = X[O2]<15:0>;
```

### `storeb O1, O2`

```text
bits(64) address = X[O1];
Mem[address, 1] = X[O2]<7:0>;
```

### `transferi O1, O2`

```text
bits(64) address = X[O2];
X[O1]<31:0> = Mem[address, 4];
```

The upper 32 bits of `X[O1]` are unspecified, unlike `loadi`.

### `transferp O1, O2`

```text
bits(64) address = X[O2];
X[O1] = Mem[address, 8];
```

### `transferq O1, O2`

```text
bits(64) address = X[O2];
X[O1] = Mem[address, 8];
```

### `sxb2i O1, O2`

```text
bits(32) result = SignExtend(X[O2]<7:0>, 32);
X[O1] = ZeroExtend(result, 64);
```

### `sxh2i O1, O2`

```text
bits(32) result = SignExtend(X[O2]<15:0>, 32);
X[O1] = ZeroExtend(result, 64);
```

### `sxb2q O1, O2`

```text
X[O1] = SignExtend(X[O2]<7:0>, 64);
```

### `sxb2p O1, O2`

```text
X[O1] = SignExtend(X[O2]<7:0>, 64);
```

### `sxh2q O1, O2`

```text
X[O1] = SignExtend(X[O2]<15:0>, 64);
```

### `sxi2q O1, O2`

```text
X[O1] = SignExtend(X[O2]<31:0>, 64);
```

### `zxb2i O1, O2`

```text
bits(32) result = ZeroExtend(X[O2]<7:0>, 32);
X[O1] = ZeroExtend(result, 64);
```

### `zxh2i O1, O2`

```text
bits(32) result = ZeroExtend(X[O2]<15:0>, 32);
X[O1] = ZeroExtend(result, 64);
```

### `zxb2q O1, O2`

```text
X[O1] = ZeroExtend(X[O2]<7:0>, 64);
```

### `zxh2q O1, O2`

```text
X[O1] = ZeroExtend(X[O2]<15:0>, 64);
```

### `zxi2q O1, O2`

```text
X[O1] = ZeroExtend(X[O2]<31:0>, 64);
```

### `loadf O1, O2`

```text
bits(64) address = X[O2];
V[O1]<31:0> = Mem[address, 4];
```

### `loadd O1, O2`

```text
bits(64) address = X[O2];
V[O1]<63:0> = Mem[address, 8];
```

### `moved O1, O2`

```text
V[O1]<63:0> = V[O2]<63:0>;
```

### `storef O1, O2`

```text
bits(64) address = X[O1];
Mem[address, 4] = V[O2]<31:0>;
```

### `stored O1, O2`

```text
bits(64) address = X[O1];
Mem[address, 8] = V[O2]<63:0>;
```

### `loadv O1, O2`

```text
bits(64) address = X[O2];
V[O1] = Mem[address, 16];
```

### `storev O1, O2`

```text
bits(64) address = X[O1];
Mem[address, 16] = V[O2];
```

### `movev O1, O2`

```text
V[O1] = V[O2];
```

### `leai O1, O2`

```text
X[O1] = ZeroExtend(EffectiveAddress(O2)<31:0>, 64);
```

### `leap O1, O2`

```text
X[O1] = EffectiveAddress(O2);
```

### `pcrtoaddr O1, O2`

```text
X[O1] = PC + SInt(O2);
```

`O2` is a PC-relative immediate offset.

### `globaladdr O1, O2`

```text
X[O1] = GlobalAddress(O2);
```

`O2` names a label or an [external symbol](#external-symbols), resolved at link or load time.

### `la O1, O2`

```text
X[O1] = EffectiveAddress(O2);
```

### `loadqinc O1, O2, O3`

```text
bits(64) address = X[O2];
X[O1] = Mem[address, 8];
X[O2] = address + X[O3];
```

Scratch:

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | increment does not fit signed 32 bits |
| AArch64 | `x17` | increment is outside ±4095 |
| RISC-V 64 | `x31` | increment is outside ±2 KiB |

### `loadpairq O1, O2, O3`

```text
bits(64) address = X[O3];
(X[O1], X[O2]) = Mem[address, 16] as (bits(64), bits(64));
```

### `loadpairp O1, O2, O3`

```text
bits(64) address = X[O3];
(X[O1], X[O2]) = Mem[address, 16] as (bits(64), bits(64));
```

### `loadpairi O1, O2, O3`

```text
bits(64) address = X[O3];
(bits(32) lo, bits(32) hi) = Mem[address, 8] as (bits(32), bits(32));
X[O1] = ZeroExtend(lo, 64);
X[O2] = ZeroExtend(hi, 64);
```

### `loadpaird O1, O2, O3`

```text
bits(64) address = X[O3];
(V[O1]<63:0>, V[O2]<63:0>) = Mem[address, 16] as (bits(64), bits(64));
```

### `loadpairv O1, O2, O3`

```text
bits(64) address = X[O3];
(V[O1], V[O2]) = Mem[address, 32] as (bits(128), bits(128));
```

### `storepairq O1, O2, O3`

```text
bits(64) address = X[O1];
Mem[address, 16] = (X[O2], X[O3]) as bits(128);
```

### `storepairp O1, O2, O3`

```text
bits(64) address = X[O1];
Mem[address, 16] = (X[O2], X[O3]) as bits(128);
```

### `storepairi O1, O2, O3`

```text
bits(64) address = X[O1];
Mem[address, 8] = (X[O2]<31:0>, X[O3]<31:0>) as bits(64);
```

### `storepaird O1, O2, O3`

```text
bits(64) address = X[O1];
Mem[address, 16] = (V[O2]<63:0>, V[O3]<63:0>) as bits(128);
```

### `storepairv O1, O2, O3`

```text
bits(64) address = X[O1];
Mem[address, 32] = (V[O2], V[O3]) as bits(256);
```

### `push O1, ..., On`

```text
for each operand Oi in O1..On do
    SP = SP - 8;
    Mem[SP, 8] = X[Oi];
endfor
```

### `pop O1, ..., On`

```text
for each operand Oi in On..O1 do
    X[Oi] = Mem[SP, 8];
    SP = SP + 8;
endfor
```

Each operand takes an 8-byte slot and the last operand ends up at `[sp]`, so `peek 0` reads it
on every target. AArch64 keeps `sp` 16-byte aligned (Linux enables the hardware check), so there a
single `push` or `pop` moves `sp` by `8 * n` rounded up to 16, where `n` is its operand count. The
operands keep the layout above and an odd count leaves a padding slot on top. Pop with the same
operand count you pushed with. Operands pair up into `stp`/`ldp`, and immediates and memory operands
stage through `x16`/`x17`. Memory operands based on `sp` are rejected on AArch64.

On rloop, `push` and `pop` read and write memory at `sp`, which the host points at a stack it owns.

### `pushv O1`

```text
SP = SP - 16;
Mem[SP, 16] = V[O1];
```

### `popv O1`

```text
V[O1] = Mem[SP, 16];
SP = SP + 16;
```

### `pushCalleeSaves O1, ..., On`

```text
for each callee-saved operand Oi in O1..On do
    SP = SP - 8;
    Mem[SP, 8] = X[Oi];
endfor
```

### `popCalleeSaves O1, ..., On`

```text
for each callee-saved operand Oi in On..O1 do
    X[Oi] = Mem[SP, 8];
    SP = SP + 8;
endfor
```

Lays operands out like `push` and `pop`, including the AArch64 rounding.

### `peek O1, O2`

```text
X[O1] = Mem[SP + 8 * UInt(O2), 8];
```

### `poke O1, O2`

```text
Mem[SP + 8 * UInt(O1), 8] = X[O2];
```

### `tls_loadb O1, O2` / `tls_loadh` / `tls_loadi` / `tls_loadp` (`tls_loadq` alias)

```text
X[O1] = ZeroExtend(Mem[TLSBase() + 8 * O2, size], 64);
```

`size` is 1/2/4/8 by suffix. `O2` is an immediate slot index, so the
address is `TLSBase() + 8 * O2`.

### `tls_storeb O1, O2` / `tls_storeh` / `tls_storei` / `tls_storep` (`tls_storeq` alias)

```text
Mem[TLSBase() + 8 * O1, size] = X[O2]<8*size-1:0>;
```


### `tls_leap O1, O2`

```text
X[O1] = TLSBase() + 8 * O2;
```

Materializes the slot address. 

### Thread-local slots across operating systems

Every slot is 8 bytes at `TLSBase() + 8 * idx`. The base itself is
platform-defined, and each backend reads it the fast way:

- Linux/BSD x86-64: `mov reg, fs:[off]` (`fs` set by `arch_prctl`).
- Windows x64: `mov reg, gs:[off]` (the TEB slot). Select it with the
  `WINDOWS` setting (`if WINDOWS` in `offlineasm!` source); Linux/BSD is
  the default.
- AArch64 (Linux/BSD/macOS): `mrs tmp, tpidr_el0` then `ldr/str`.
- RISC-V 64: `ld/sd` directly off `tp` (`x4`).

The JIT (`onlineasm`) picks `fs` vs `gs` from its `Abi`
(`Abi::Windows` means `gs`). The portable `rloop` backend does not
support thread-local slots.

Named OS thread-locals (ELF `initial-exec`, Mach-O TLV, Windows
`_tls_index` slots) have no link-time address a JIT can resolve, so
there is no named-symbol form, and you have to resolve the variable
address manually once per thread, and store it in a reserved TLS slot via
`tls_storep`.

## 2. Integer arithmetic and bitwise logic

### Scratch registers

Integer ALU: `addi`, `addp`, `addq`, `subi`, `subp`, `subq`, `muli`, `mulp`, `mulq`, `andi`, `andp`, `andq`, `ori`, `orp`, `orq`, `orh`, `xori`, `xorp`, `xorq`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | memory destination in the two-operand form, with a memory source, or for `mul*`; immediate that does not fit the 32-bit immediate field; memory operand addressed through the destination register |
| AArch64 | `x16` | memory address that must be folded (index scale other than the access size, index plus offset, offset out of range); memory destination with a memory, unencodable-immediate or `sp` right operand; memory operand addressed through the destination register |
| AArch64 | `x17` | memory destination; memory source; immediate the instruction cannot encode (every `mul*` immediate); `sub*` whose right operand is the destination or `sp` |
| RISC-V 64 | `x31` | memory destination; memory source; memory address that must be folded; immediate outside signed 12 bits (every `mul*` immediate); `sub*` whose right operand is the destination; `orh` always |
| RISC-V 64 | `x29` | memory destination whose address must be folded; second memory operand addressed through the destination register |

Flag-setting ALU: `addis`, `subis`, `oris`, `addqs`, `subqs`, `addps`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | as for the integer ALU; `sub*` whose right operand is the destination register |
| AArch64 | `x16`, `x17` | as for the integer ALU |
| RISC-V 64 | `x29`, `x31` | always (`oris`: `x29` only with a memory destination) |
| RISC-V 64 | `x30` | always to receives the emulated flags |

On RISC-V 64, `addis` and `subis` also push and pop a 16-byte stack slot.

Negate and complement: `negi`, `negp`, `negq`, `noti`, `notq`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | never |
| AArch64 | `x16` | memory address that must be folded |
| AArch64 | `x17` | memory operand |
| RISC-V 64 | - | never (memory operands are rejected) |

Shifts and rotates: `lshifti`, `lshiftp`, `lshiftq`, `rshifti`, `rshiftp`, `rshiftq`, `urshifti`, `urshiftp`, `urshiftq`, `lrotatei`, `lrotateq`, `rrotatei`, `rrotateq`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | memory destination |
| AArch64 | `x16` | memory destination |
| AArch64 | `x17` | `lrotate*` by a register count |
| RISC-V 64 | `x31` | memory destination; every rotate |
| RISC-V 64 | `x29` | memory destination whose address must be folded |

On x86-64 a register count is swapped into `cl` and back, so `rcx` is preserved; shifting `rcx` itself by another register is rejected.

Byte swap: `bswapi`, `bswapq`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | never (register operands only) |
| AArch64 | `x16` | memory or immediate source |
| AArch64 | `x17` | memory destination |
| RISC-V 64 | `x29`, `x31` | always (register operands only) |

Add and subtract with carry: `adcq`, `sbcq`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | immediate outside signed 32 bits; memory destination with a memory source |
| AArch64 | `x16` | memory or immediate source; memory address that must be folded |
| AArch64 | `x17` | memory destination |
| RISC-V 64 | `x29`, `x30` | always, also receive emulated flags in `x30`  |
| RISC-V 64 | `x31` | memory destination |

On RISC-V 64 both also push and pop a 48-byte stack slot.

Multiply high: `umulhq`, `smulhq`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | never (immediate factors are rejected) |
| AArch64 | `x16` | memory or immediate factor |
| RISC-V 64 | `x31` | memory or immediate factor |

Widening multiply: `smulli`, `umulli`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | always |
| AArch64 | - | never |
| RISC-V 64 | `x29`, `x31` | always |

Three-operand divide and remainder: `divi`, `divis`, `divq`, `divqs`, `remi`, `remis`, `remq`, `remqs`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | immediate divisor; divisor in or addressed through `rax`/`rdx`; destination `rax`/`rdx` |
| AArch64 | `x16` | memory or immediate divisor; memory address that must be folded |
| AArch64 | `x17` | `rem*` always |
| RISC-V 64 | `x31` | memory or immediate dividend or divisor |

On x86-64 `rax` and `rdx` are pushed before the divide and popped after it. On RISC-V 64, a dividend and divisor that both need staging also push and pop an 8-byte stack slot.

Accumulator divide: `idivi`, `udivi`, `idivq`, `udivq`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | immediate divisor |
| AArch64 | `x16`, `x17` | always |
| RISC-V 64 | `x31` | always (memory and immediate divisors are rejected) |

Sign extension into the pair: `cdqi`, `cqoq` clobber no scratch register on any target.

Set on less than: `slt`, `sltu`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | immediate left operand; memory left operand with an immediate or memory right operand; immediate outside signed 32 bits |
| AArch64 | `x16` | memory left operand (an immediate left operand is swapped to the right) |
| AArch64 | `x17` | memory right operand; right immediate outside -4095..4095; memory destination |
| RISC-V 64 | `x31` | memory or immediate operand |
| RISC-V 64 | `x29` | memory destination |

On RISC-V 64, a memory left operand with an immediate right operand also pushes and pops an 8-byte stack slot.

Conditional move: `movz`, `movn`, `cmov`, `cmovz`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | memory or immediate source |
| AArch64 | `x16` | memory or immediate source |
| RISC-V 64 | `x31` | memory source whose address must be folded |

Bit counts: `popcnti`, `popcntq`, `tzcnti`, `tzcntq`, `lzcnti`, `lzcntq`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | never |
| AArch64 | `x16` | `popcnt*` always; `tzcnt*`/`lzcnt*` with a memory or immediate source |
| AArch64 | `x17` | `tzcnt*` always |
| AArch64 | `v31` | `popcnt*` always |
| RISC-V 64 | `x29`, `x31` | always |

Floating-point bitwise: `andf`, `andd`, `orf`, `ord`

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | never (immediate sources are rejected) |
| AArch64 | `v31` | memory or immediate source |
| AArch64 | `x16` | immediate source; memory address that must be folded |
| RISC-V 64 | `x29`, `x31` | always |
| RISC-V 64 | `f31` | memory source |

### `addi O1, O2, O3`

```text
X[O1]<31:0> = X[O2]<31:0> + X[O3]<31:0>;
```

### `addp O1, O2, O3`

```text
X[O1] = X[O2] + X[O3];
```

### `addq O1, O2, O3`

```text
X[O1] = X[O2] + X[O3];
```

### `subi O1, O2, O3`

```text
X[O1]<31:0> = X[O2]<31:0> - X[O3]<31:0>;
```

### `subp O1, O2, O3`

```text
X[O1] = X[O2] - X[O3];
```

### `subq O1, O2, O3`

```text
X[O1] = X[O2] - X[O3];
```

### `muli O1, O2, O3`

```text
X[O1]<31:0> = X[O2]<31:0> * X[O3]<31:0>;
```

### `mulp O1, O2, O3`

```text
X[O1] = X[O2] * X[O3];
```

### `mulq O1, O2, O3`

```text
X[O1] = X[O2] * X[O3];
```

### `andi O1, O2, O3`

```text
X[O1]<31:0> = X[O2]<31:0> AND X[O3]<31:0>;
```

### `andp O1, O2, O3`

```text
X[O1] = X[O2] AND X[O3];
```

### `andq O1, O2, O3`

```text
X[O1] = X[O2] AND X[O3];
```

### `ori O1, O2, O3`

```text
X[O1]<31:0> = X[O2]<31:0> OR X[O3]<31:0>;
```

### `orp O1, O2, O3`

```text
X[O1] = X[O2] OR X[O3];
```

### `orq O1, O2, O3`

```text
X[O1] = X[O2] OR X[O3];
```

### `orh O1, O2, O3`

```text
X[O1]<15:0> = X[O2]<15:0> OR X[O3]<15:0>;
```

### `xori O1, O2, O3`

```text
X[O1]<31:0> = X[O2]<31:0> EOR X[O3]<31:0>;
```

### `xorp O1, O2, O3`

```text
X[O1] = X[O2] EOR X[O3];
```

### `xorq O1, O2, O3`

```text
X[O1] = X[O2] EOR X[O3];
```

### `andf O1, O2, O3`

```text
V[O1]<31:0> = V[O2]<31:0> AND V[O3]<31:0>;
```

### `andd O1, O2, O3`

```text
V[O1]<63:0> = V[O2]<63:0> AND V[O3]<63:0>;
```

### `orf O1, O2, O3`

```text
V[O1]<31:0> = V[O2]<31:0> OR V[O3]<31:0>;
```

### `ord O1, O2, O3`

```text
V[O1]<63:0> = V[O2]<63:0> OR V[O3]<63:0>;
```

### `negi O1`

```text
X[O1]<31:0> = -X[O1]<31:0>;
```

### `negp O1`

```text
X[O1] = -X[O1];
```

### `negq O1`

```text
X[O1] = -X[O1];
```

### `noti O1`

```text
X[O1]<31:0> = NOT(X[O1]<31:0>);
```

### `notq O1`

```text
X[O1] = NOT(X[O1]);
```

### `lshifti O1, O2`

```text
X[O1]<31:0> = LSL(X[O1]<31:0>, UInt(X[O2]<5:0>));
```

### `lshiftp O1, O2`

```text
X[O1] = LSL(X[O1], UInt(X[O2]<5:0>));
```

### `lshiftq O1, O2`

```text
X[O1] = LSL(X[O1], UInt(X[O2]<5:0>));
```

### `rshifti O1, O2`

```text
X[O1]<31:0> = ASR(X[O1]<31:0>, UInt(X[O2]<5:0>));
```

### `rshiftp O1, O2`

```text
X[O1] = ASR(X[O1], UInt(X[O2]<5:0>));
```

### `rshiftq O1, O2`

```text
X[O1] = ASR(X[O1], UInt(X[O2]<5:0>));
```

### `urshifti O1, O2`

```text
X[O1]<31:0> = LSR(X[O1]<31:0>, UInt(X[O2]<5:0>));
```

### `urshiftp O1, O2`

```text
X[O1] = LSR(X[O1], UInt(X[O2]<5:0>));
```

### `urshiftq O1, O2`

```text
X[O1] = LSR(X[O1], UInt(X[O2]<5:0>));
```

### `lrotatei O1, O2`

```text
X[O1]<31:0> = RotateLeft(X[O1]<31:0>, UInt(X[O2]<4:0>));
```

### `lrotateq O1, O2`

```text
X[O1] = RotateLeft(X[O1], UInt(X[O2]<5:0>));
```

### `rrotatei O1, O2`

```text
X[O1]<31:0> = RotateRight(X[O1]<31:0>, UInt(X[O2]<4:0>));
```

### `rrotateq O1, O2`

```text
X[O1] = RotateRight(X[O1], UInt(X[O2]<5:0>));
```

### `bswapi O1, O2`

```text
X[O1]<31:0> = ByteReverse(X[O2]<31:0>);
```

### `bswapq O1, O2`

```text
X[O1] = ByteReverse(X[O2]);
```

### `adcq O1, O2`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], X[O2], FLAG.C);
X[O1] = result;
FLAG = nzcv;
```

### `sbcq O1, O2`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], NOT(X[O2]), FLAG.C);
X[O1] = result;
FLAG = nzcv;
```

### `umulhq O1`

```text
bits(128) product = ZeroExtend(X[t0], 128) * ZeroExtend(X[O1], 128);
X[t0] = product<63:0>;
X[t2] = product<127:64>;
```

### `smulhq O1`

```text
bits(128) product = SignExtend(X[t0], 128) * SignExtend(X[O1], 128);
X[t0] = product<63:0>;
X[t2] = product<127:64>;
```

### `smulli O1, O2, O3`

```text
bits(64) product = SignExtend(X[O2]<31:0>, 64) * SignExtend(X[O3]<31:0>, 64);
X[O1] = product;
```

### `umulli O1, O2, O3`

```text
bits(64) product = ZeroExtend(X[O2]<31:0>, 64) * ZeroExtend(X[O3]<31:0>, 64);
X[O1] = product;
```

### `addqs O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O2], X[O3], '0');
X[O1] = result;
FLAG = nzcv;
```

### `subqs O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O2], NOT(X[O3]), '1');
X[O1] = result;
FLAG = nzcv;
```

### `addis O1, O2, O3`

```text
(bits(32) result, bits(4) nzcv) = AddWithCarry(X[O2]<31:0>, X[O3]<31:0>, '0');
X[O1]<31:0> = result;
FLAG = nzcv;
```

### `subis O1, O2, O3`

```text
(bits(32) result, bits(4) nzcv) = AddWithCarry(X[O2]<31:0>, NOT(X[O3]<31:0>), '1');
X[O1]<31:0> = result;
FLAG = nzcv;
```

### `oris O1, O2, O3`

```text
bits(32) result = X[O2]<31:0> OR X[O3]<31:0>;
X[O1]<31:0> = result;
FLAG.N = result<31>;
FLAG.Z = IsZeroBit(result);
```

### `addps O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O2], X[O3], '0');
X[O1] = result;
FLAG = nzcv;
```

### `addlshiftp O1, O2, O3, O4`

```text
X[O1] = X[O2] + LSL(X[O3], UInt(X[O4]<5:0>));
```

Scratch: x86-64 `r11` when the shift amount is greater than 3; never on AArch64 or RISC-V 64.

### `divi O1, O2, O3`

```text
X[O1]<31:0> = SInt(X[O2]<31:0>) DIV SInt(X[O3]<31:0>);
```

### `divis O1, O2, O3`

```text
X[O1]<31:0> = SInt(X[O2]<31:0>) DIV SInt(X[O3]<31:0>);
FLAG.Z = IsZeroBit(X[O1]<31:0>);
```

### `divq O1, O2, O3`

```text
X[O1] = SInt(X[O2]) DIV SInt(X[O3]);
```

### `divqs O1, O2, O3`

```text
X[O1] = SInt(X[O2]) DIV SInt(X[O3]);
FLAG.Z = IsZeroBit(X[O1]);
```

### `remi O1, O2, O3`

```text
X[O1]<31:0> = SInt(X[O2]<31:0>) MOD SInt(X[O3]<31:0>);
```

### `remis O1, O2, O3`

```text
X[O1]<31:0> = SInt(X[O2]<31:0>) MOD SInt(X[O3]<31:0>);
FLAG.Z = IsZeroBit(X[O1]<31:0>);
```

### `remq O1, O2, O3`

```text
X[O1] = SInt(X[O2]) MOD SInt(X[O3]);
```

### `remqs O1, O2, O3`

```text
X[O1] = SInt(X[O2]) MOD SInt(X[O3]);
FLAG.Z = IsZeroBit(X[O1]);
```

### `cdqi`

```text
bits(64) widened = SignExtend(X[t0]<31:0>, 64);
X[t0] = widened<31:0>;
X[t2] = widened<63:32>;
```

Splits the 64-bit sign extension of the low word of `X[t0]` across the `X[t2]:X[t0]` pair.

### `cqoq`

```text
bits(128) widened = SignExtend(X[t0], 128);
X[t0] = widened<63:0>;
X[t2] = widened<127:64>;
```

Splits the 128-bit sign extension of `X[t0]` across the `X[t2]:X[t0]` pair.

### `idivi O1`

```text
(X[t0], X[t2]) = (SInt(X[t0]) DIV SInt(X[O1]), SInt(X[t0]) MOD SInt(X[O1]));
```

### `udivi O1`

```text
(X[t0], X[t2]) = (UInt(X[t0]) DIV UInt(X[O1]), UInt(X[t0]) MOD UInt(X[O1]));
```

### `idivq O1`

```text
(X[t0], X[t2]) = (SInt(X[t0]) DIV SInt(X[O1]), SInt(X[t0]) MOD SInt(X[O1]));
```

### `udivq O1`

```text
(X[t0], X[t2]) = (UInt(X[t0]) DIV UInt(X[O1]), UInt(X[t0]) MOD UInt(X[O1]));
```

### `slt O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) < SInt(X[O3]) then 1 else 0;
```

### `sltu O1, O2, O3`

```text
X[O1] = if UInt(X[O2]) < UInt(X[O3]) then 1 else 0;
```

### `movz O1, O2, O3`

```text
if IsZeroBit(X[O3]) then
    X[O1] = X[O2];
endif
```

### `movn O1, O2, O3`

```text
if !IsZeroBit(X[O3]) then
    X[O1] = X[O2];
endif
```

### `cmov O1, O2, O3`

```text
if !IsZeroBit(X[O3]) then
    X[O1] = X[O2];
endif
```

### `cmovz O1, O2, O3`

```text
if IsZeroBit(X[O3]) then
    X[O1] = X[O2];
endif
```

### `bfiq O1, O2, O3, O4`

```text
X[O1] = BFXPreserve(X[O1], X[O2], UInt(O3), UInt(O4));
```

Scratch:

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | always |
| AArch64 | `x16` | always |
| AArch64 | `x17` | field width 64 (the masks are not logical immediates) |
| RISC-V 64 | `x31` | always |

`O3`/`O4` are the immediate low-bit position and width of the field taken from `X[O2]` and inserted into `X[O1]`.

### `popcnti O1, O2`

```text
X[O1] = ZeroExtend(BitCount(X[O2]<31:0>), 64);
```

### `popcntq O1, O2`

```text
X[O1] = ZeroExtend(BitCount(X[O2]), 64);
```

### `tzcnti O1, O2`

```text
X[O1] = ZeroExtend(CountTrailingZeroBits(X[O2]<31:0>), 64);
```

### `tzcntq O1, O2`

```text
X[O1] = ZeroExtend(CountTrailingZeroBits(X[O2]), 64);
```

### `lzcnti O1, O2`

```text
X[O1] = ZeroExtend(CountLeadingZeroBits(X[O2]<31:0>), 64);
```

### `lzcntq O1, O2`

```text
X[O1] = ZeroExtend(CountLeadingZeroBits(X[O2]), 64);
```

## 3. Floating-point arithmetic

### Scratch registers

"Address needs folding" means the memory operand cannot be encoded directly: on AArch64 an absolute address, an index plus a nonzero offset, an index scale other than 1 or the access size, or an out-of-range offset; on RISC-V 64 an absolute address, any index, or an offset outside 12 bits.

Binary arithmetic: `addf`, `addd`, `subf`, `subd`, `mulf`, `muld`, `divf`, `divd`, `fmin`, `fmax`, `dmin`, `dmax`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `xmm7` | `subf`/`subd`/`divf`/`divd` only: destination is the right source but not the left, and the left source is memory or AVX is off |
| AArch64 | `v31` | right source is memory, an immediate, or the destination; two-operand source is memory or an immediate |
| AArch64 | `x16` | immediate source; address needs folding |
| RISC-V 64 | `f31` | right source is memory, an immediate, or the destination; two-operand source is memory or an immediate |
| RISC-V 64 | `x31` | immediate source; address needs folding |

Fused multiply-add: `fmaddf`, `fmaddd`, `fmsubf`, `fmsubd`, `fnmaddf`, `fnmaddd`, `fnmsubf`, `fnmsubd`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `xmm7` | always (stages the first factor) |
| AArch64 | `v31` | a factor or the addend is memory or an immediate |
| AArch64 | `x16` | immediate operand; address needs folding |
| RISC-V 64 | `f31` | a factor or the addend is memory or an immediate |
| RISC-V 64 | `x31` | immediate operand; address needs folding |

Square root and rounding: `sqrtf`, `sqrtd`, `roundf`, `roundd`, `floorf`, `floord`, `ceilf`, `ceild`, `truncatef`, `truncated`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | `v31` | source is memory or an immediate |
| AArch64 | `x16` | immediate source; address needs folding |
| RISC-V 64 | `f31` | rounding ops: always; `sqrtf`/`sqrtd`: source is memory or an immediate |
| RISC-V 64 | `x31` | rounding ops: always; `sqrtf`/`sqrtd`: immediate source; address needs folding |
| RISC-V 64 | `x29` | rounding ops: always |

Absolute value and negation: `absf`, `absd`, `negf`, `negd`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | always (materializes the sign mask) |
| x86-64 | `xmm7` | memory source, or the source is the destination (the sign mask is built in the destination) |
| AArch64 | `v31` | source is memory or an immediate |
| AArch64 | `x16` | immediate source; address needs folding |
| RISC-V 64 | `f31` | source is memory or an immediate |
| RISC-V 64 | `x31` | immediate source; address needs folding |

Zeroing and vector lane extraction: `movdz`, `umovb`, `umovh`, `umovi`, `umovq`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | - | |
| RISC-V 64 | - | |

On RISC-V 64, `umovb`, `umovh`, and `umovi` spill the holding half of the source through 8 bytes pushed below `sp`, `sp` is restored afterwards.

### `addf O1, O2, O3`

```text
V[O1]<31:0> = V[O2]<31:0> + V[O3]<31:0>;
```

### `addd O1, O2, O3`

```text
V[O1]<63:0> = V[O2]<63:0> + V[O3]<63:0>;
```

### `subf O1, O2, O3`

```text
V[O1]<31:0> = V[O2]<31:0> - V[O3]<31:0>;
```

### `subd O1, O2, O3`

```text
V[O1]<63:0> = V[O2]<63:0> - V[O3]<63:0>;
```

### `mulf O1, O2, O3`

```text
V[O1]<31:0> = V[O2]<31:0> * V[O3]<31:0>;
```

### `muld O1, O2, O3`

```text
V[O1]<63:0> = V[O2]<63:0> * V[O3]<63:0>;
```

### `divf O1, O2, O3`

```text
V[O1]<31:0> = V[O2]<31:0> / V[O3]<31:0>;
```

### `divd O1, O2, O3`

```text
V[O1]<63:0> = V[O2]<63:0> / V[O3]<63:0>;
```

### `fmin O1, O2, O3`

```text
V[O1]<31:0> = Min(V[O2]<31:0>, V[O3]<31:0>);
```

### `fmax O1, O2, O3`

```text
V[O1]<31:0> = Max(V[O2]<31:0>, V[O3]<31:0>);
```

### `dmin O1, O2, O3`

```text
V[O1]<63:0> = Min(V[O2]<63:0>, V[O3]<63:0>);
```

### `dmax O1, O2, O3`

```text
V[O1]<63:0> = Max(V[O2]<63:0>, V[O3]<63:0>);
```

### `fmaddf O1, O2, O3, O4`

```text
V[O1]<31:0> = V[O2]<31:0> * V[O3]<31:0> + V[O4]<31:0>;
```

Requires FMA on x86-64.

### `fmaddd O1, O2, O3, O4`

```text
V[O1]<63:0> = V[O2]<63:0> * V[O3]<63:0> + V[O4]<63:0>;
```

Requires FMA on x86-64.

### `fmsubf O1, O2, O3, O4`

```text
V[O1]<31:0> = V[O2]<31:0> * V[O3]<31:0> - V[O4]<31:0>;
```

Requires FMA on x86-64.

### `fmsubd O1, O2, O3, O4`

```text
V[O1]<63:0> = V[O2]<63:0> * V[O3]<63:0> - V[O4]<63:0>;
```

Requires FMA on x86-64.

### `fnmaddf O1, O2, O3, O4`

```text
V[O1]<31:0> = -(V[O2]<31:0> * V[O3]<31:0>) + V[O4]<31:0>;
```

Requires FMA on x86-64.

### `fnmaddd O1, O2, O3, O4`

```text
V[O1]<63:0> = -(V[O2]<63:0> * V[O3]<63:0>) + V[O4]<63:0>;
```

Requires FMA on x86-64.

### `fnmsubf O1, O2, O3, O4`

```text
V[O1]<31:0> = -(V[O2]<31:0> * V[O3]<31:0>) - V[O4]<31:0>;
```

Requires FMA on x86-64.

### `fnmsubd O1, O2, O3, O4`

```text
V[O1]<63:0> = -(V[O2]<63:0> * V[O3]<63:0>) - V[O4]<63:0>;
```

Requires FMA on x86-64.

### `sqrtf O1, O2`

```text
V[O1]<31:0> = Sqrt(V[O2]<31:0>);
```

### `sqrtd O1, O2`

```text
V[O1]<63:0> = Sqrt(V[O2]<63:0>);
```

### `roundf O1, O2`

```text
V[O1]<31:0> = RoundToNearest(V[O2]<31:0>);
```

### `roundd O1, O2`

```text
V[O1]<63:0> = RoundToNearest(V[O2]<63:0>);
```

### `floorf O1, O2`

```text
V[O1]<31:0> = FloorToIntegral(V[O2]<31:0>);
```

### `floord O1, O2`

```text
V[O1]<63:0> = FloorToIntegral(V[O2]<63:0>);
```

### `ceilf O1, O2`

```text
V[O1]<31:0> = CeilToIntegral(V[O2]<31:0>);
```

### `ceild O1, O2`

```text
V[O1]<63:0> = CeilToIntegral(V[O2]<63:0>);
```

### `truncatef O1, O2`

```text
V[O1]<31:0> = TruncateToIntegral(V[O2]<31:0>);
```

### `truncated O1, O2`

```text
V[O1]<63:0> = TruncateToIntegral(V[O2]<63:0>);
```

### `absf O1, O2`

```text
V[O1]<31:0> = Abs(V[O2]<31:0>);
```

### `absd O1, O2`

```text
V[O1]<63:0> = Abs(V[O2]<63:0>);
```

### `negf O1, O2`

```text
V[O1]<31:0> = -V[O2]<31:0>;
```

### `negd O1, O2`

```text
V[O1]<63:0> = -V[O2]<63:0>;
```

### `movdz O1`

```text
V[O1]<63:0> = 0.0;
```

### `umovb O1, O2, O3`

```text
X[O1] = ZeroExtend(V[O2]<UInt(O3) * 8 + 7 : UInt(O3) * 8>, 64);
```

### `umovh O1, O2, O3`

```text
X[O1] = ZeroExtend(V[O2]<UInt(O3) * 16 + 15 : UInt(O3) * 16>, 64);
```

### `umovi O1, O2, O3`

```text
X[O1] = ZeroExtend(V[O2]<UInt(O3) * 32 + 31 : UInt(O3) * 32>, 64);
```

### `umovq O1, O2, O3`

```text
X[O1] = V[O2]<UInt(O3) * 64 + 63 : UInt(O3) * 64>;
```

## 4. Conversions

### Scratch registers

Float-to-int truncations: `truncatef2is`, `truncated2is`, `truncatef2i`, `truncatef2qs`, `truncated2i`, `truncated2qs`, `td2i`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | - |
| AArch64 | `x16` | always (overflow/NaN result fixup); memory address needs folding |
| AArch64 | `v31` | source is memory or an immediate |
| RISC-V 64 | `x31` | always (overflow result fixup); memory address needs folding |
| RISC-V 64 | `f31` | source is memory or an immediate |

Unsigned-range truncations: `truncatef2q`, `truncated2q`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11`, `xmm7` | always |
| AArch64 | `x16`, `v31` | always |
| RISC-V 64 | `x31`, `f31` | always |

Int-to-float conversions: `ci2d`, `ci2ds`, `ci2f`, `ci2fs`, `cq2fs`, `cq2ds`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | - |
| AArch64 | `x16` | source is memory or an immediate |
| RISC-V 64 | `x31` | source is memory or an immediate |

Unsigned quad-to-float conversions: `cq2f`, `cq2d`. The caller-supplied `O3` is also clobbered.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | source is negative (halving path) |
| AArch64 | `x16` | source is negative (halving path); source is memory |
| RISC-V 64 | `x31` | source is negative (halving path); source is memory |

Float-to-float conversions: `cd2f`, `cf2d`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | - |
| AArch64 | `v31` | source is memory or an immediate |
| AArch64 | `x16` | memory address needs folding; immediate source |
| RISC-V 64 | `f31` | source is memory or an immediate |
| RISC-V 64 | `x31` | memory address needs folding; immediate source |

Bit-casts: `fq2d`, `fd2q`, `fi2f`, `ff2i`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | - |
| AArch64 | - | - |
| RISC-V 64 | - | - |

### `truncatef2is O1, O2`

```text
X[O1] = SignExtend(FPToFixed(V[O2]<31:0>, 32, RoundTowardsZero), 64);
```

### `truncated2is O1, O2`

```text
X[O1] = SignExtend(FPToFixed(V[O2]<63:0>, 32, RoundTowardsZero), 64);
```

### `truncatef2i O1, O2`

```text
X[O1] = ZeroExtend(FPToFixed(V[O2]<31:0>, 32, RoundTowardsZero), 64);
```

### `truncatef2qs O1, O2`

```text
X[O1] = FPToFixed(V[O2]<31:0>, 64, RoundTowardsZero);
```

### `truncated2i O1, O2`

```text
X[O1] = ZeroExtend(FPToFixed(V[O2]<63:0>, 32, RoundTowardsZero), 64);
```

### `truncated2qs O1, O2`

```text
X[O1] = FPToFixed(V[O2]<63:0>, 64, RoundTowardsZero);
```

### `truncatef2q O1, O2`

```text
X[O1] = FPToFixed(V[O2]<31:0>, 64, RoundTowardsZero);
```

### `truncated2q O1, O2`

```text
X[O1] = FPToFixed(V[O2]<63:0>, 64, RoundTowardsZero);
```

### `ci2d O1, O2`

```text
V[O2]<63:0> = FixedToFP(SInt(X[O1]<31:0>), 64);
```

### `ci2ds O1, O2`

```text
V[O2]<63:0> = FixedToFP(SInt(X[O1]<31:0>), 64);
```

### `ci2f O1, O2`

```text
V[O2]<31:0> = FixedToFP(SInt(X[O1]<31:0>), 32);
```

### `ci2fs O1, O2`

```text
V[O2]<31:0> = FixedToFP(SInt(X[O1]<31:0>), 32);
```

### `cq2fs O1, O2`

```text
V[O2]<31:0> = FixedToFP(SInt(X[O1]), 32);
```

### `cq2f O1, O2`

```text
V[O1]<31:0> = FixedToFP(SInt(X[O2]), 32);
```

`O3` names the scratch register the lowering may use.

### `cq2d O1, O2`

```text
V[O1]<63:0> = FixedToFP(SInt(X[O2]), 64);
```

`O3` names the scratch register the lowering may use.

### `cq2ds O1, O2`

```text
V[O2]<63:0> = FixedToFP(SInt(X[O1]), 64);
```

### `cd2f O1, O2`

```text
V[O1]<31:0> = FPConvert(V[O2]<63:0>, 32);
```

### `cf2d O1, O2`

```text
V[O1]<63:0> = FPConvert(V[O2]<31:0>, 64);
```

### `fq2d O1, O2`

```text
V[O1]<63:0> = V[O2];
```

Reinterprets the 64 bits of `X[O2]` as an `f64` bit pattern.

### `fd2q O1, O2`

```text
X[O1] = V[O2]<63:0>;
```

Reinterprets the 64 bits of the `f64` register `V[O2]` as an integer bit pattern.

### `fi2f O1, O2`

```text
V[O1]<31:0> = X[O2]<31:0>;
```

Reinterprets the low 32 bits of `X[O2]` as an `f32` bit pattern.

### `ff2i O1, O2`

```text
X[O1] = ZeroExtend(V[O2]<31:0>, 64);
```

Reinterprets the `f32` bit pattern of `V[O2]` as an integer.

### `btd2i O1, O2, O3`

```text
X[O1] = FPToFixed(V[O2]<63:0>, 32, RoundTowardsZero);
if X[O1] == 0x80000000 then
    BranchTo(O3);
endif
```

Scratch: same as the float-to-int truncations, plus AArch64 `x17` always (the `0x80000000` compare immediate).

### `td2i O1, O2`

```text
X[O1] = ZeroExtend(FPToFixed(V[O2]<63:0>, 32, RoundTowardsZero), 64);
```

### `bcd2i O1, O2, O3`

```text
X[O1] = ZeroExtend(FPToFixed(V[O2]<63:0>, 32, RoundTowardsZero), 64);
if InexactConversion() then
    BranchTo(O3);
endif
```

Scratch: same as the float-to-int truncations, plus x86-64 `xmm7`, AArch64 `v31`, and RISC-V 64 `f31` always (round-trip compare).

## 5. Comparing and testing values

### Scratch registers

No opcode in this section touches the RISC-V 64 flags register `x30`.

Integer compare and set: `cieq`, `cineq`, `cia`, `ciaeq`, `cib`, `cibeq`, `cigt`, `cigteq`, `cilt`, `cilteq`, and the same conditions for `cb*`, `cp*`, `cq*`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | O2 is an immediate (except `0` against a register in `eq`/`neq` forms); O3 is an immediate too wide for the operand size (outside signed 32 bits for `cp*`/`cq*`); O2 is memory and O3 is an immediate or memory |
| AArch64 | `x16` | O2 is memory; O2 is an immediate and O3 is memory; both are immediates; `cbgt`, `cbgteq`, `cblt`, `cblteq` (always); an address needs synthesis |
| AArch64 | `x17` | O3 is memory and O2 is not an immediate; an immediate outside `-4095..4095`; `cbgt`, `cbgteq`, `cblt`, `cblteq` (always); memory destination |
| RISC-V 64 | `x31` | O2 or O3 is an immediate (any value) or memory; an address needs synthesis |
| RISC-V 64 | `x29` | memory destination |

On RISC-V 64, when both O2 and O3 need staging, O2 is saved on the stack below `sp` instead of in a second scratch register, and the 8- and 32-bit forms (`ci*`, `cb*`) sign- or zero-extend register operands O2 and O3 to 64 bits in place.

Float compare and set: `cfeq`, `cfneq`, `cfnequn`, `cfgt`, `cfgteq`, `cflt`, `cflteq`, and the same conditions for `cd*`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `xmm7` | the operand `ucomis*` takes first is memory: O2 for `cfneq`, `cfgt`, `cfgteq`; O3 for `cfeq`, `cfnequn`, `cflt`, `cflteq` |
| AArch64 | `v31` | a source is memory or an immediate |
| AArch64 | `x16` | a source is an immediate; an address needs synthesis |
| AArch64 | `x17` | memory destination |
| RISC-V 64 | `x29` | always |
| RISC-V 64 | `x31` | `cfneq`, `cdneq` (always); a source is an immediate; an address needs synthesis |
| RISC-V 64 | `f31` | a source is memory or an immediate |

Test and set: `tis`, `tiz`, `tinz`, `tps`, `tpz`, `tpnz`, `tqs`, `tqz`, `tqnz`, `tbs`, `tbz`, `tbnz`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | a mask must be a register or an encodable immediate |
| AArch64 | `x16` | O2 is memory or an immediate; an address needs synthesis |
| AArch64 | `x17` | the mask is not a register; `tbs`, `tbz`, `tbnz` (always); memory destination |
| RISC-V 64 | `x29` | always |
| RISC-V 64 | `x31` | O2 is memory or an immediate; the mask is not a register; an address needs synthesis |

On AArch64 a mask applies to a register O2 in place (`and O2, O2, mask`), so O2 itself is clobbered.

### `cieq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<31:0>) == SInt(X[O3]<31:0>) then 1 else 0;
```

### `cineq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<31:0>) != SInt(X[O3]<31:0>) then 1 else 0;
```

### `cia O1, O2, O3`

```text
X[O1] = if UInt(X[O2]<31:0>) > UInt(X[O3]<31:0>) then 1 else 0;
```

### `ciaeq O1, O2, O3`

```text
X[O1] = if UInt(X[O2]<31:0>) >= UInt(X[O3]<31:0>) then 1 else 0;
```

### `cib O1, O2, O3`

```text
X[O1] = if UInt(X[O2]<31:0>) < UInt(X[O3]<31:0>) then 1 else 0;
```

### `cibeq O1, O2, O3`

```text
X[O1] = if UInt(X[O2]<31:0>) <= UInt(X[O3]<31:0>) then 1 else 0;
```

### `cigt O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<31:0>) > SInt(X[O3]<31:0>) then 1 else 0;
```

### `cigteq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<31:0>) >= SInt(X[O3]<31:0>) then 1 else 0;
```

### `cilt O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<31:0>) < SInt(X[O3]<31:0>) then 1 else 0;
```

### `cilteq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<31:0>) <= SInt(X[O3]<31:0>) then 1 else 0;
```

### `cbeq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<7:0>) == SInt(X[O3]<7:0>) then 1 else 0;
```

### `cbneq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<7:0>) != SInt(X[O3]<7:0>) then 1 else 0;
```

### `cba O1, O2, O3`

```text
X[O1] = if UInt(X[O2]<7:0>) > UInt(X[O3]<7:0>) then 1 else 0;
```

### `cbaeq O1, O2, O3`

```text
X[O1] = if UInt(X[O2]<7:0>) >= UInt(X[O3]<7:0>) then 1 else 0;
```

### `cbb O1, O2, O3`

```text
X[O1] = if UInt(X[O2]<7:0>) < UInt(X[O3]<7:0>) then 1 else 0;
```

### `cbbeq O1, O2, O3`

```text
X[O1] = if UInt(X[O2]<7:0>) <= UInt(X[O3]<7:0>) then 1 else 0;
```

### `cbgt O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<7:0>) > SInt(X[O3]<7:0>) then 1 else 0;
```

### `cbgteq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<7:0>) >= SInt(X[O3]<7:0>) then 1 else 0;
```

### `cblt O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<7:0>) < SInt(X[O3]<7:0>) then 1 else 0;
```

### `cblteq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]<7:0>) <= SInt(X[O3]<7:0>) then 1 else 0;
```

### `cpeq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) == SInt(X[O3]) then 1 else 0;
```

### `cpneq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) != SInt(X[O3]) then 1 else 0;
```

### `cpa O1, O2, O3`

```text
X[O1] = if UInt(X[O2]) > UInt(X[O3]) then 1 else 0;
```

### `cpaeq O1, O2, O3`

```text
X[O1] = if UInt(X[O2]) >= UInt(X[O3]) then 1 else 0;
```

### `cpb O1, O2, O3`

```text
X[O1] = if UInt(X[O2]) < UInt(X[O3]) then 1 else 0;
```

### `cpbeq O1, O2, O3`

```text
X[O1] = if UInt(X[O2]) <= UInt(X[O3]) then 1 else 0;
```

### `cpgt O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) > SInt(X[O3]) then 1 else 0;
```

### `cpgteq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) >= SInt(X[O3]) then 1 else 0;
```

### `cplt O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) < SInt(X[O3]) then 1 else 0;
```

### `cplteq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) <= SInt(X[O3]) then 1 else 0;
```

### `cqeq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) == SInt(X[O3]) then 1 else 0;
```

### `cqneq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) != SInt(X[O3]) then 1 else 0;
```

### `cqa O1, O2, O3`

```text
X[O1] = if UInt(X[O2]) > UInt(X[O3]) then 1 else 0;
```

### `cqaeq O1, O2, O3`

```text
X[O1] = if UInt(X[O2]) >= UInt(X[O3]) then 1 else 0;
```

### `cqb O1, O2, O3`

```text
X[O1] = if UInt(X[O2]) < UInt(X[O3]) then 1 else 0;
```

### `cqbeq O1, O2, O3`

```text
X[O1] = if UInt(X[O2]) <= UInt(X[O3]) then 1 else 0;
```

### `cqgt O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) > SInt(X[O3]) then 1 else 0;
```

### `cqgteq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) >= SInt(X[O3]) then 1 else 0;
```

### `cqlt O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) < SInt(X[O3]) then 1 else 0;
```

### `cqlteq O1, O2, O3`

```text
X[O1] = if SInt(X[O2]) <= SInt(X[O3]) then 1 else 0;
```

### `cfeq O1, O2, O3`

```text
X[O1] = if V[O2]<31:0> == V[O3]<31:0> then 1 else 0;
```

### `cfneq O1, O2, O3`

```text
X[O1] = if V[O2]<31:0> != V[O3]<31:0> then 1 else 0;
```

### `cfnequn O1, O2, O3`

```text
X[O1] = if IsUnordered(V[O2]<31:0>, V[O3]<31:0>) || V[O2]<31:0> != V[O3]<31:0> then 1 else 0;
```

### `cfgt O1, O2, O3`

```text
X[O1] = if V[O2]<31:0> > V[O3]<31:0> then 1 else 0;
```

### `cfgteq O1, O2, O3`

```text
X[O1] = if V[O2]<31:0> >= V[O3]<31:0> then 1 else 0;
```

### `cflt O1, O2, O3`

```text
X[O1] = if V[O2]<31:0> < V[O3]<31:0> then 1 else 0;
```

### `cflteq O1, O2, O3`

```text
X[O1] = if V[O2]<31:0> <= V[O3]<31:0> then 1 else 0;
```

### `cdeq O1, O2, O3`

```text
X[O1] = if V[O2]<63:0> == V[O3]<63:0> then 1 else 0;
```

### `cdneq O1, O2, O3`

```text
X[O1] = if V[O2]<63:0> != V[O3]<63:0> then 1 else 0;
```

### `cdnequn O1, O2, O3`

```text
X[O1] = if IsUnordered(V[O2]<63:0>, V[O3]<63:0>) || V[O2]<63:0> != V[O3]<63:0> then 1 else 0;
```

### `cdgt O1, O2, O3`

```text
X[O1] = if V[O2]<63:0> > V[O3]<63:0> then 1 else 0;
```

### `cdgteq O1, O2, O3`

```text
X[O1] = if V[O2]<63:0> >= V[O3]<63:0> then 1 else 0;
```

### `cdlt O1, O2, O3`

```text
X[O1] = if V[O2]<63:0> < V[O3]<63:0> then 1 else 0;
```

### `cdlteq O1, O2, O3`

```text
X[O1] = if V[O2]<63:0> <= V[O3]<63:0> then 1 else 0;
```

### `tis O1, O2`

```text
X[O1] = if SInt(X[O2]<31:0>) < 0 then 1 else 0;
```

### `tiz O1, O2`

```text
X[O1] = if IsZeroBit(X[O2]<31:0>) then 1 else 0;
```

### `tinz O1, O2`

```text
X[O1] = if !IsZeroBit(X[O2]<31:0>) then 1 else 0;
```

### `tps O1, O2`

```text
X[O1] = if SInt(X[O2]<63:0>) < 0 then 1 else 0;
```

### `tpz O1, O2`

```text
X[O1] = if IsZeroBit(X[O2]<63:0>) then 1 else 0;
```

### `tpnz O1, O2`

```text
X[O1] = if !IsZeroBit(X[O2]<63:0>) then 1 else 0;
```

### `tqs O1, O2`

```text
X[O1] = if SInt(X[O2]<63:0>) < 0 then 1 else 0;
```

### `tqz O1, O2`

```text
X[O1] = if IsZeroBit(X[O2]<63:0>) then 1 else 0;
```

### `tqnz O1, O2`

```text
X[O1] = if !IsZeroBit(X[O2]<63:0>) then 1 else 0;
```

### `tbs O1, O2`

```text
X[O1] = if SInt(X[O2]<7:0>) < 0 then 1 else 0;
```

### `tbz O1, O2`

```text
X[O1] = if IsZeroBit(X[O2]<7:0>) then 1 else 0;
```

### `tbnz O1, O2`

```text
X[O1] = if !IsZeroBit(X[O2]<7:0>) then 1 else 0;
```

## 6. Branches and control flow

### Scratch registers

Integer compare branches: `bieq`, `bineq`, `bia`, `biaeq`, `bib`, `bibeq`, `bigt`, `bigteq`, `bilt`, `bilteq`, and the same conditions for `bb*`, `bp*`, `bq*`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | O1 is an immediate (except `0` against a register in `eq`/`neq` forms); O2 is an immediate too wide for the operand size (outside signed 32 bits for `bp*`/`bq*`); O1 is memory and O2 is an immediate or memory |
| AArch64 | `x16` | O1 is memory; O1 is an immediate and O2 is memory; both are immediates; `bbgt`, `bbgteq`, `bblt`, `bblteq` (always); an address needs synthesis |
| AArch64 | `x17` | O2 is memory and O1 is not an immediate; an immediate outside `-4095..4095`; `bbgt`, `bbgteq`, `bblt`, `bblteq` (always) |
| RISC-V 64 | `x31` | O1 or O2 is an immediate (any value) or memory; `bigt`, `bigteq`, `bilt`, `bilteq`, `bbgt`, `bbgteq`, `bblt`, `bblteq` (always); an address needs synthesis |
| RISC-V 64 | `x29` | both O1 and O2 are immediates or memory; `bigt`, `bigteq`, `bilt`, `bilteq`, `bbgt`, `bbgteq`, `bblt`, `bblteq` (always) |

On RISC-V 64 the signed 8- and 32-bit forms sign-extend both sides into `x31` and `x29` even when they are registers.

Test branches: `btis`, `btiz`, `btinz`, `btps`, `btpz`, `btpnz`, `btqs`, `btqz`, `btqnz`, `btbs`, `btbz`, `btbnz`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | a mask must be a register or an encodable immediate |
| AArch64 | `x16` | O1 is memory or an immediate; an address needs synthesis |
| AArch64 | `x17` | the mask is not a register; `btbs`, `btbz`, `btbnz` with a mask or a memory O1 |
| RISC-V 64 | `x31` | O1 is memory or an immediate; the mask is not a register; an address needs synthesis |
| RISC-V 64 | `x29` | a mask is given (except a register mask over a memory or immediate O1); `btis`, `btps`, `btqs`, `btbs` (always) |

Without a mask, a register O1 needs no scratch on AArch64 (`cbz`, `cbnz`, `tbnz`), and neither does a zero or non-zero test of a register on RISC-V 64. On AArch64 a mask applies to a register O1 in place (`and O1, O1, mask`), so O1 itself is clobbered.

Arithmetic branches: `baddio`, `baddis`, `baddiz`, `baddinz`, and the same flags for `baddp*`, `baddq*`, `bsubi*`, `bsubp*`, `bsubq*`, `bmuli*`, `bmulp*`, `bmulq*`, `bori*`, `borp*`, `borq*`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | an immediate outside signed 32 bits; a memory source with a memory destination; `bmul*` with a memory destination; `dst = lhs - dst`; a memory operand addressed through the destination register |
| AArch64 | `x16` | `bmulio`, `bmulpo`, `bmulqo` (always); `bmul*`/`bor*` `s`/`z`/`nz` forms with a memory destination; a memory source or unencodable immediate with a memory destination; a memory operand addressed through the destination register; an address needs synthesis |
| AArch64 | `x17` | `bmulio`, `bmulpo`, `bmulqo` (always); a memory source; an immediate the instruction cannot encode (any `bmul*` immediate); memory destination; `dst = lhs - dst`; a second memory operand addressed through the destination register |
| RISC-V 64 | `x30` | `badd*o`, `bsub*o`, `bmul*o` (always) |
| RISC-V 64 | `x31` | `baddio`, `bsubio`, `bmulio`, `bmulpo`, `bmulqo` (always); `baddis`, `bsubis`, `bmulis`, `boris` with a register destination; a memory source or destination; an immediate outside 12 bits (any `bmul*` immediate); `dst = lhs - dst`; a memory operand addressed through the destination register; an address needs synthesis |
| RISC-V 64 | `x29` | `badd*o`, `bsub*o` unless the source is a 12-bit immediate; `bmulio` (always); `bmulpo`, `bmulqo` when the source is not a register; a memory destination whose address needs synthesis; a second memory operand addressed through the destination register |

`bmulpo` and `bmulqo` on AArch64 also use 16 bytes below `sp` when both factors are staged.

Float branches: `bdeq`, `bdneq`, `bdgt`, `bdgteq`, `bdlt`, `bdlteq`, `bdequn`, `bdnequn`, `bdgtun`, `bdgtequn`, `bdltun`, `bdltequn`, `bfeq`, `bfgt`, `bfgteq`, `bflt`, `bfgtun`, `bfgtequn`, `bfltun`, `bfltequn`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `xmm7` | the operand `ucomis*` takes first is memory: O1, or O2 for `bdlt`, `bdlteq`, `bdltun`, `bdltequn`, `bflt`, `bfltun`, `bfltequn` |
| AArch64 | `v31` | a source is memory or an immediate |
| AArch64 | `x16` | a source is an immediate; an address needs synthesis |
| RISC-V 64 | `x31` | always |
| RISC-V 64 | `x29` | `bdequn`, `bdgtun`, `bdgtequn`, `bdltun`, `bdltequn`, `bfgtun`, `bfgtequn`, `bfltun`, `bfltequn` (always) |
| RISC-V 64 | `f31` | a source is memory or an immediate |

AArch64 and RISC-V 64 reject two non-register sources.

Flag branches: `bo`, `bs`, `bz`, `bnz`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | - | |
| RISC-V 64 | `x31` | always (the flag bit is masked out of `x30`) |

Jumps and calls: `jmp`, `call`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | absolute-address target |
| AArch64 | `x16` | memory-indirect, absolute-address, or far extern target |
| RISC-V 64 | `x31` | memory-indirect, absolute-address, or far extern target; `jmp` to a near extern |

`ret`, `break`, and `nop` clobber no scratch register on any target.

### `bieq O1, O2, O3`

```text
if SInt(X[O1]<31:0>) == SInt(X[O2]<31:0>) then
    BranchTo(O3);
endif
```

### `bineq O1, O2, O3`

```text
if SInt(X[O1]<31:0>) != SInt(X[O2]<31:0>) then
    BranchTo(O3);
endif
```

### `bia O1, O2, O3`

```text
if UInt(X[O1]<31:0>) > UInt(X[O2]<31:0>) then
    BranchTo(O3);
endif
```

### `biaeq O1, O2, O3`

```text
if UInt(X[O1]<31:0>) >= UInt(X[O2]<31:0>) then
    BranchTo(O3);
endif
```

### `bib O1, O2, O3`

```text
if UInt(X[O1]<31:0>) < UInt(X[O2]<31:0>) then
    BranchTo(O3);
endif
```

### `bibeq O1, O2, O3`

```text
if UInt(X[O1]<31:0>) <= UInt(X[O2]<31:0>) then
    BranchTo(O3);
endif
```

### `bigt O1, O2, O3`

```text
if SInt(X[O1]<31:0>) > SInt(X[O2]<31:0>) then
    BranchTo(O3);
endif
```

### `bigteq O1, O2, O3`

```text
if SInt(X[O1]<31:0>) >= SInt(X[O2]<31:0>) then
    BranchTo(O3);
endif
```

### `bilt O1, O2, O3`

```text
if SInt(X[O1]<31:0>) < SInt(X[O2]<31:0>) then
    BranchTo(O3);
endif
```

### `bilteq O1, O2, O3`

```text
if SInt(X[O1]<31:0>) <= SInt(X[O2]<31:0>) then
    BranchTo(O3);
endif
```

### `bbeq O1, O2, O3`

```text
if SInt(X[O1]<7:0>) == SInt(X[O2]<7:0>) then
    BranchTo(O3);
endif
```

### `bbneq O1, O2, O3`

```text
if SInt(X[O1]<7:0>) != SInt(X[O2]<7:0>) then
    BranchTo(O3);
endif
```

### `bba O1, O2, O3`

```text
if UInt(X[O1]<7:0>) > UInt(X[O2]<7:0>) then
    BranchTo(O3);
endif
```

### `bbaeq O1, O2, O3`

```text
if UInt(X[O1]<7:0>) >= UInt(X[O2]<7:0>) then
    BranchTo(O3);
endif
```

### `bbb O1, O2, O3`

```text
if UInt(X[O1]<7:0>) < UInt(X[O2]<7:0>) then
    BranchTo(O3);
endif
```

### `bbbeq O1, O2, O3`

```text
if UInt(X[O1]<7:0>) <= UInt(X[O2]<7:0>) then
    BranchTo(O3);
endif
```

### `bbgt O1, O2, O3`

```text
if SInt(X[O1]<7:0>) > SInt(X[O2]<7:0>) then
    BranchTo(O3);
endif
```

### `bbgteq O1, O2, O3`

```text
if SInt(X[O1]<7:0>) >= SInt(X[O2]<7:0>) then
    BranchTo(O3);
endif
```

### `bblt O1, O2, O3`

```text
if SInt(X[O1]<7:0>) < SInt(X[O2]<7:0>) then
    BranchTo(O3);
endif
```

### `bblteq O1, O2, O3`

```text
if SInt(X[O1]<7:0>) <= SInt(X[O2]<7:0>) then
    BranchTo(O3);
endif
```

### `bpeq O1, O2, O3`

```text
if SInt(X[O1]) == SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bpneq O1, O2, O3`

```text
if SInt(X[O1]) != SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bpa O1, O2, O3`

```text
if UInt(X[O1]) > UInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bpaeq O1, O2, O3`

```text
if UInt(X[O1]) >= UInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bpb O1, O2, O3`

```text
if UInt(X[O1]) < UInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bpbeq O1, O2, O3`

```text
if UInt(X[O1]) <= UInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bpgt O1, O2, O3`

```text
if SInt(X[O1]) > SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bpgteq O1, O2, O3`

```text
if SInt(X[O1]) >= SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bplt O1, O2, O3`

```text
if SInt(X[O1]) < SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bplteq O1, O2, O3`

```text
if SInt(X[O1]) <= SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bqeq O1, O2, O3`

```text
if SInt(X[O1]) == SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bqneq O1, O2, O3`

```text
if SInt(X[O1]) != SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bqa O1, O2, O3`

```text
if UInt(X[O1]) > UInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bqaeq O1, O2, O3`

```text
if UInt(X[O1]) >= UInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bqb O1, O2, O3`

```text
if UInt(X[O1]) < UInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bqbeq O1, O2, O3`

```text
if UInt(X[O1]) <= UInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bqgt O1, O2, O3`

```text
if SInt(X[O1]) > SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bqgteq O1, O2, O3`

```text
if SInt(X[O1]) >= SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bqlt O1, O2, O3`

```text
if SInt(X[O1]) < SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `bqlteq O1, O2, O3`

```text
if SInt(X[O1]) <= SInt(X[O2]) then
    BranchTo(O3);
endif
```

### `btis O1, O2`

```text
if SInt(X[O1]<31:0>) < 0 then
    BranchTo(O2);
endif
```

### `btiz O1, O2`

```text
if IsZeroBit(X[O1]<31:0>) then
    BranchTo(O2);
endif
```

### `btinz O1, O2`

```text
if !IsZeroBit(X[O1]<31:0>) then
    BranchTo(O2);
endif
```

### `btps O1, O2`

```text
if SInt(X[O1]<63:0>) < 0 then
    BranchTo(O2);
endif
```

### `btpz O1, O2`

```text
if IsZeroBit(X[O1]<63:0>) then
    BranchTo(O2);
endif
```

### `btpnz O1, O2`

```text
if !IsZeroBit(X[O1]<63:0>) then
    BranchTo(O2);
endif
```

### `btqs O1, O2`

```text
if SInt(X[O1]<63:0>) < 0 then
    BranchTo(O2);
endif
```

### `btqz O1, O2`

```text
if IsZeroBit(X[O1]<63:0>) then
    BranchTo(O2);
endif
```

### `btqnz O1, O2`

```text
if !IsZeroBit(X[O1]<63:0>) then
    BranchTo(O2);
endif
```

### `btbs O1, O2`

```text
if SInt(X[O1]<7:0>) < 0 then
    BranchTo(O2);
endif
```

### `btbz O1, O2`

```text
if IsZeroBit(X[O1]<7:0>) then
    BranchTo(O2);
endif
```

### `btbnz O1, O2`

```text
if !IsZeroBit(X[O1]<7:0>) then
    BranchTo(O2);
endif
```

### `baddio O1, O2, O3`

```text
(bits(32) result, bits(4) nzcv) = AddWithCarry(X[O1]<31:0>, X[O2]<31:0>, '0');
X[O1]<31:0> = result;
if nzcv.V == '1' then
    BranchTo(O3);
endif
```

### `baddis O1, O2, O3`

```text
(bits(32) result, bits(4) nzcv) = AddWithCarry(X[O1]<31:0>, X[O2]<31:0>, '0');
X[O1]<31:0> = result;
if nzcv.N == '1' then
    BranchTo(O3);
endif
```

### `baddiz O1, O2, O3`

```text
(bits(32) result, bits(4) nzcv) = AddWithCarry(X[O1]<31:0>, X[O2]<31:0>, '0');
X[O1]<31:0> = result;
if nzcv.Z == '1' then
    BranchTo(O3);
endif
```

### `baddinz O1, O2, O3`

```text
(bits(32) result, bits(4) nzcv) = AddWithCarry(X[O1]<31:0>, X[O2]<31:0>, '0');
X[O1]<31:0> = result;
if nzcv.Z != '1' then
    BranchTo(O3);
endif
```

### `baddpo O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], X[O2], '0');
X[O1] = result;
if nzcv.V == '1' then
    BranchTo(O3);
endif
```

### `baddps O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], X[O2], '0');
X[O1] = result;
if nzcv.N == '1' then
    BranchTo(O3);
endif
```

### `baddpz O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], X[O2], '0');
X[O1] = result;
if nzcv.Z == '1' then
    BranchTo(O3);
endif
```

### `baddpnz O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], X[O2], '0');
X[O1] = result;
if nzcv.Z != '1' then
    BranchTo(O3);
endif
```

### `baddqo O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], X[O2], '0');
X[O1] = result;
if nzcv.V == '1' then
    BranchTo(O3);
endif
```

### `baddqs O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], X[O2], '0');
X[O1] = result;
if nzcv.N == '1' then
    BranchTo(O3);
endif
```

### `baddqz O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], X[O2], '0');
X[O1] = result;
if nzcv.Z == '1' then
    BranchTo(O3);
endif
```

### `baddqnz O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], X[O2], '0');
X[O1] = result;
if nzcv.Z != '1' then
    BranchTo(O3);
endif
```

### `bsubio O1, O2, O3`

```text
(bits(32) result, bits(4) nzcv) = AddWithCarry(X[O1]<31:0>, NOT(X[O2]<31:0>), '1');
X[O1]<31:0> = result;
if nzcv.V == '1' then
    BranchTo(O3);
endif
```

### `bsubis O1, O2, O3`

```text
(bits(32) result, bits(4) nzcv) = AddWithCarry(X[O1]<31:0>, NOT(X[O2]<31:0>), '1');
X[O1]<31:0> = result;
if nzcv.N == '1' then
    BranchTo(O3);
endif
```

### `bsubiz O1, O2, O3`

```text
(bits(32) result, bits(4) nzcv) = AddWithCarry(X[O1]<31:0>, NOT(X[O2]<31:0>), '1');
X[O1]<31:0> = result;
if nzcv.Z == '1' then
    BranchTo(O3);
endif
```

### `bsubinz O1, O2, O3`

```text
(bits(32) result, bits(4) nzcv) = AddWithCarry(X[O1]<31:0>, NOT(X[O2]<31:0>), '1');
X[O1]<31:0> = result;
if nzcv.Z != '1' then
    BranchTo(O3);
endif
```

### `bmulio O1, O2, O3`

```text
(bits(32) result, bit overflow) = MulWithOverflow(X[O1]<31:0>, X[O2]<31:0>);
X[O1]<31:0> = result;
if overflow == '1' then
    BranchTo(O3);
endif
```

### `bmulis O1, O2, O3`

```text
(bits(32) result, bit overflow) = MulWithOverflow(X[O1]<31:0>, X[O2]<31:0>);
X[O1]<31:0> = result;
if result<31> == '1' then
    BranchTo(O3);
endif
```

### `bmuliz O1, O2, O3`

```text
(bits(32) result, bit overflow) = MulWithOverflow(X[O1]<31:0>, X[O2]<31:0>);
X[O1]<31:0> = result;
if IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `bmulinz O1, O2, O3`

```text
(bits(32) result, bit overflow) = MulWithOverflow(X[O1]<31:0>, X[O2]<31:0>);
X[O1]<31:0> = result;
if !IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `bsubqo O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], NOT(X[O2]), '1');
X[O1] = result;
if nzcv.V == '1' then
    BranchTo(O3);
endif
```

### `bsubqs O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], NOT(X[O2]), '1');
X[O1] = result;
if nzcv.N == '1' then
    BranchTo(O3);
endif
```

### `bsubqz O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], NOT(X[O2]), '1');
X[O1] = result;
if nzcv.Z == '1' then
    BranchTo(O3);
endif
```

### `bsubqnz O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], NOT(X[O2]), '1');
X[O1] = result;
if nzcv.Z != '1' then
    BranchTo(O3);
endif
```

### `bsubpo O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], NOT(X[O2]), '1');
X[O1] = result;
if nzcv.V == '1' then
    BranchTo(O3);
endif
```

### `bsubps O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], NOT(X[O2]), '1');
X[O1] = result;
if nzcv.N == '1' then
    BranchTo(O3);
endif
```

### `bsubpz O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], NOT(X[O2]), '1');
X[O1] = result;
if nzcv.Z == '1' then
    BranchTo(O3);
endif
```

### `bsubpnz O1, O2, O3`

```text
(bits(64) result, bits(4) nzcv) = AddWithCarry(X[O1], NOT(X[O2]), '1');
X[O1] = result;
if nzcv.Z != '1' then
    BranchTo(O3);
endif
```

### `bmulqo O1, O2, O3`

```text
(bits(64) result, bit overflow) = MulWithOverflow(X[O1], X[O2]);
X[O1] = result;
if overflow == '1' then
    BranchTo(O3);
endif
```

### `bmulqs O1, O2, O3`

```text
(bits(64) result, bit overflow) = MulWithOverflow(X[O1], X[O2]);
X[O1] = result;
if result<63> == '1' then
    BranchTo(O3);
endif
```

### `bmulqz O1, O2, O3`

```text
(bits(64) result, bit overflow) = MulWithOverflow(X[O1], X[O2]);
X[O1] = result;
if IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `bmulqnz O1, O2, O3`

```text
(bits(64) result, bit overflow) = MulWithOverflow(X[O1], X[O2]);
X[O1] = result;
if !IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `bmulpo O1, O2, O3`

```text
(bits(64) result, bit overflow) = MulWithOverflow(X[O1], X[O2]);
X[O1] = result;
if overflow == '1' then
    BranchTo(O3);
endif
```

### `bmulps O1, O2, O3`

```text
(bits(64) result, bit overflow) = MulWithOverflow(X[O1], X[O2]);
X[O1] = result;
if result<63> == '1' then
    BranchTo(O3);
endif
```

### `bmulpz O1, O2, O3`

```text
(bits(64) result, bit overflow) = MulWithOverflow(X[O1], X[O2]);
X[O1] = result;
if IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `bmulpnz O1, O2, O3`

```text
(bits(64) result, bit overflow) = MulWithOverflow(X[O1], X[O2]);
X[O1] = result;
if !IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `borqo O1, O2, O3`

```text
bits(64) result = X[O1] OR X[O2];
X[O1] = result;
// bitwise OR cannot overflow: this branch is never taken
if FALSE then
    BranchTo(O3);
endif
```

### `borqs O1, O2, O3`

```text
bits(64) result = X[O1] OR X[O2];
X[O1] = result;
if result<63> == '1' then
    BranchTo(O3);
endif
```

### `borqz O1, O2, O3`

```text
bits(64) result = X[O1] OR X[O2];
X[O1] = result;
if IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `borqnz O1, O2, O3`

```text
bits(64) result = X[O1] OR X[O2];
X[O1] = result;
if !IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `borpo O1, O2, O3`

```text
bits(64) result = X[O1] OR X[O2];
X[O1] = result;
// bitwise OR cannot overflow: this branch is never taken
if FALSE then
    BranchTo(O3);
endif
```

### `borps O1, O2, O3`

```text
bits(64) result = X[O1] OR X[O2];
X[O1] = result;
if result<63> == '1' then
    BranchTo(O3);
endif
```

### `borpz O1, O2, O3`

```text
bits(64) result = X[O1] OR X[O2];
X[O1] = result;
if IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `borpnz O1, O2, O3`

```text
bits(64) result = X[O1] OR X[O2];
X[O1] = result;
if !IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `borio O1, O2, O3`

```text
bits(32) result = X[O1]<31:0> OR X[O2]<31:0>;
X[O1]<31:0> = result;
// bitwise OR cannot overflow: this branch is never taken
if FALSE then
    BranchTo(O3);
endif
```

### `boris O1, O2, O3`

```text
bits(32) result = X[O1]<31:0> OR X[O2]<31:0>;
X[O1]<31:0> = result;
if result<31> == '1' then
    BranchTo(O3);
endif
```

### `boriz O1, O2, O3`

```text
bits(32) result = X[O1]<31:0> OR X[O2]<31:0>;
X[O1]<31:0> = result;
if IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `borinz O1, O2, O3`

```text
bits(32) result = X[O1]<31:0> OR X[O2]<31:0>;
X[O1]<31:0> = result;
if !IsZeroBit(result) then
    BranchTo(O3);
endif
```

### `bdeq O1, O2, O3`

```text
if V[O1]<63:0> == V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdneq O1, O2, O3`

```text
if V[O1]<63:0> != V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdgt O1, O2, O3`

```text
if V[O1]<63:0> > V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdgteq O1, O2, O3`

```text
if V[O1]<63:0> >= V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdlt O1, O2, O3`

```text
if V[O1]<63:0> < V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdlteq O1, O2, O3`

```text
if V[O1]<63:0> <= V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdequn O1, O2, O3`

```text
if IsUnordered(V[O1]<63:0>, V[O2]<63:0>) || V[O1]<63:0> == V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdnequn O1, O2, O3`

```text
if IsUnordered(V[O1]<63:0>, V[O2]<63:0>) || V[O1]<63:0> != V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdgtun O1, O2, O3`

```text
if IsUnordered(V[O1]<63:0>, V[O2]<63:0>) || V[O1]<63:0> > V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdgtequn O1, O2, O3`

```text
if IsUnordered(V[O1]<63:0>, V[O2]<63:0>) || V[O1]<63:0> >= V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdltun O1, O2, O3`

```text
if IsUnordered(V[O1]<63:0>, V[O2]<63:0>) || V[O1]<63:0> < V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bdltequn O1, O2, O3`

```text
if IsUnordered(V[O1]<63:0>, V[O2]<63:0>) || V[O1]<63:0> <= V[O2]<63:0> then
    BranchTo(O3);
endif
```

### `bfeq O1, O2, O3`

```text
if V[O1]<31:0> == V[O2]<31:0> then
    BranchTo(O3);
endif
```

### `bfgt O1, O2, O3`

```text
if V[O1]<31:0> > V[O2]<31:0> then
    BranchTo(O3);
endif
```

### `bfgteq O1, O2, O3`

```text
if V[O1]<31:0> >= V[O2]<31:0> then
    BranchTo(O3);
endif
```

### `bflt O1, O2, O3`

```text
if V[O1]<31:0> < V[O2]<31:0> then
    BranchTo(O3);
endif
```

### `bfgtun O1, O2, O3`

```text
if IsUnordered(V[O1]<31:0>, V[O2]<31:0>) || V[O1]<31:0> > V[O2]<31:0> then
    BranchTo(O3);
endif
```

### `bfgtequn O1, O2, O3`

```text
if IsUnordered(V[O1]<31:0>, V[O2]<31:0>) || V[O1]<31:0> >= V[O2]<31:0> then
    BranchTo(O3);
endif
```

### `bfltun O1, O2, O3`

```text
if IsUnordered(V[O1]<31:0>, V[O2]<31:0>) || V[O1]<31:0> < V[O2]<31:0> then
    BranchTo(O3);
endif
```

### `bfltequn O1, O2, O3`

```text
if IsUnordered(V[O1]<31:0>, V[O2]<31:0>) || V[O1]<31:0> <= V[O2]<31:0> then
    BranchTo(O3);
endif
```

### `bo O1`

```text
if FLAG.V == '1' then
    BranchTo(O1);
endif
```

### `bs O1`

```text
if FLAG.N == '1' then
    BranchTo(O1);
endif
```

### `bz O1`

```text
if FLAG.Z == '1' then
    BranchTo(O1);
endif
```

### `bnz O1`

```text
if FLAG.Z == '0' then
    BranchTo(O1);
endif
```

### `jmp O1`

```text
BranchTo(O1);
```

Accepts `#[patch]` in `onlineasm`. `O1` may be an [external symbol](#external-symbols).

### `call O1`

```text
LR = PC;
BranchTo(O1);
```

Accepts `#[patch]` in `onlineasm`. `O1` may be an [external symbol](#external-symbols).

On RISC-V 64, `call` keeps `ra`: it spills `ra` to a 16-byte slot below `sp` around the transfer,
so the callee starts with `sp` 16 bytes lower and `ra` is unchanged when the call returns. On x86-64
the callee starts 8 bytes lower (the pushed return address). On AArch64 `sp` is unchanged and `LR` is
overwritten.

On rloop, a label target (or a register holding a label address from `leap`) is an interpreted
call: `LR` gets the return point and `ret` goes back to it, as on AArch64 and RISC-V. Any other target
is a native function address, called through the host's `call_native` hook with `t0`/`t1` as
arguments and its result in `t0`/`t1`. Portable code therefore saves `lr` around calls on every
target except x86-64, rloop included.

### `ret`

```text
BranchTo(LR);
```

### `break`

```text
Trap();
```

### `nop`

```text
// no operation
```

## 7. Atomics, fences, and system operations

### Scratch registers

Fetch-and-add, fetch-and-subtract, and exchange: `atomicxchgadd{b,h,i,q}`, `atomicxchgsub{b,h,i,q}`, `atomicxchg{b,h,i,q}`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | `x16` | address has an offset or an index (LSE atomics take only `[Xn]`) |
| RISC-V 64 | `x31` | always (holds the address) |
| RISC-V 64 | `x29`, `x30`, 32-byte stack frame | `b`/`h` widths (`lr.w`/`sc.w` merge loop) |

Fetch-and-or and fetch-and-xor: `atomicxchgor{b,h,i,q}`, `atomicxchgxor{b,h,i,q}`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | always (`lock cmpxchg` retry loop; `rax` is saved and restored on the stack) |
| AArch64 | `x16` | address has an offset or an index |
| RISC-V 64 | `x31` | always (holds the address) |
| RISC-V 64 | `x29`, `x30`, 32-byte stack frame | `b`/`h` widths (`lr.w`/`sc.w` merge loop) |

Fetch-and-clear: `atomicxchgclear{b,h,i,q}`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | `r11` | always (complemented source; `lock cmpxchg` retry loop; `rax` is saved and restored on the stack) |
| AArch64 | `x16` | always (complemented source); an address with an offset or index also folds into `x16` and overwrites it, so use a bare base register |
| RISC-V 64 | `x31`, `x29` | always (complemented source staged in `x29`, address in `x31`) |
| RISC-V 64 | `x30`, 32-byte stack frame | `b`/`h` widths (`lr.w`/`sc.w` merge loop) |

Compare-and-swap: `atomicweakcas{b,h,i,q}`, `batomicweakcas{b,h,i,q}`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | (`t0` is `rax`, the operand-visible expected/old value of `lock cmpxchg`) |
| AArch64 | `x17` | always (saves the expected value across `casal`) |
| AArch64 | `x16` | address has an offset or an index |
| RISC-V 64 | `x31`, `x29`, `x30` | always (`lr`/`sc` loop: address, compare/status, loaded word) |
| RISC-V 64 | 32-byte stack frame | `b`/`h` widths |

Load-linked: `loadlinkacq{b,h,i,q}`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | `x16` | address has an offset or an index |
| RISC-V 64 | `x31` | always (holds the address) |
| RISC-V 64 | `x29` | `b`/`h` widths (shift) |

Store-conditional: `storecondrel{b,h,i,q}`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | `x16` | address has an offset or an index |
| AArch64 | `x16`, `x17` | the status register is also the source or an address register |
| RISC-V 64 | `x31` | always (holds the address) |
| RISC-V 64 | `x29`, `x30`, 32-byte stack frame | `b`/`h` widths (`lr.w`/`sc.w` merge loop) |

On x86-64 the conditional store is one `lock cmpxchg` against `t0` (`rax`), which holds the current memory value when the store fails. On RISC-V 64 the `b`/`h` forms also overwrite the source register `O3` with the shift amount.

Fences and spin hint: `memfence`, `fence`, `pause`.

| target | clobbers | when |
| --- | --- | --- |
| x86-64 | - | |
| AArch64 | - | |
| RISC-V 64 | - | |

### `atomicxchgaddb O1, O2`

```text
bits(64) address = X[O1];
bits(8) old = Acquire(Mem[address, 1]);
Release(Mem[address, 1]) = old + X[O2]<7:0>;
X[O2]<7:0> = old;
```

### `atomicxchgaddh O1, O2`

```text
bits(64) address = X[O1];
bits(16) old = Acquire(Mem[address, 2]);
Release(Mem[address, 2]) = old + X[O2]<15:0>;
X[O2]<15:0> = old;
```

### `atomicxchgaddi O1, O2`

```text
bits(64) address = X[O1];
bits(32) old = Acquire(Mem[address, 4]);
Release(Mem[address, 4]) = old + X[O2]<31:0>;
X[O2]<31:0> = old;
```

### `atomicxchgaddq O1, O2`

```text
bits(64) address = X[O1];
bits(64) old = Acquire(Mem[address, 8]);
Release(Mem[address, 8]) = old + X[O2];
X[O2] = old;
```

### `atomicxchgsubb O1, O2`

```text
bits(64) address = X[O1];
bits(8) old = Acquire(Mem[address, 1]);
Release(Mem[address, 1]) = old - X[O2]<7:0>;
X[O2]<7:0> = old;
```

### `atomicxchgsubh O1, O2`

```text
bits(64) address = X[O1];
bits(16) old = Acquire(Mem[address, 2]);
Release(Mem[address, 2]) = old - X[O2]<15:0>;
X[O2]<15:0> = old;
```

### `atomicxchgsubi O1, O2`

```text
bits(64) address = X[O1];
bits(32) old = Acquire(Mem[address, 4]);
Release(Mem[address, 4]) = old - X[O2]<31:0>;
X[O2]<31:0> = old;
```

### `atomicxchgsubq O1, O2`

```text
bits(64) address = X[O1];
bits(64) old = Acquire(Mem[address, 8]);
Release(Mem[address, 8]) = old - X[O2];
X[O2] = old;
```

### `atomicxchgb O1, O2`

```text
bits(64) address = X[O1];
bits(8) old = Acquire(Mem[address, 1]);
Release(Mem[address, 1]) = X[O2]<7:0>;
X[O2]<7:0> = old;
```

### `atomicxchgh O1, O2`

```text
bits(64) address = X[O1];
bits(16) old = Acquire(Mem[address, 2]);
Release(Mem[address, 2]) = X[O2]<15:0>;
X[O2]<15:0> = old;
```

### `atomicxchgi O1, O2`

```text
bits(64) address = X[O1];
bits(32) old = Acquire(Mem[address, 4]);
Release(Mem[address, 4]) = X[O2]<31:0>;
X[O2]<31:0> = old;
```

### `atomicxchgq O1, O2`

```text
bits(64) address = X[O1];
bits(64) old = Acquire(Mem[address, 8]);
Release(Mem[address, 8]) = X[O2];
X[O2] = old;
```

### `atomicxchgclearb O1, O2`

```text
bits(64) address = X[O1];
bits(8) old = Acquire(Mem[address, 1]);
Release(Mem[address, 1]) = old AND NOT(X[O2]<7:0>);
X[O2]<7:0> = old;
```

### `atomicxchgclearh O1, O2`

```text
bits(64) address = X[O1];
bits(16) old = Acquire(Mem[address, 2]);
Release(Mem[address, 2]) = old AND NOT(X[O2]<15:0>);
X[O2]<15:0> = old;
```

### `atomicxchgcleari O1, O2`

```text
bits(64) address = X[O1];
bits(32) old = Acquire(Mem[address, 4]);
Release(Mem[address, 4]) = old AND NOT(X[O2]<31:0>);
X[O2]<31:0> = old;
```

### `atomicxchgclearq O1, O2`

```text
bits(64) address = X[O1];
bits(64) old = Acquire(Mem[address, 8]);
Release(Mem[address, 8]) = old AND NOT(X[O2]);
X[O2] = old;
```

### `atomicxchgorb O1, O2`

```text
bits(64) address = X[O1];
bits(8) old = Acquire(Mem[address, 1]);
Release(Mem[address, 1]) = old OR X[O2]<7:0>;
X[O2]<7:0> = old;
```

### `atomicxchgorh O1, O2`

```text
bits(64) address = X[O1];
bits(16) old = Acquire(Mem[address, 2]);
Release(Mem[address, 2]) = old OR X[O2]<15:0>;
X[O2]<15:0> = old;
```

### `atomicxchgori O1, O2`

```text
bits(64) address = X[O1];
bits(32) old = Acquire(Mem[address, 4]);
Release(Mem[address, 4]) = old OR X[O2]<31:0>;
X[O2]<31:0> = old;
```

### `atomicxchgorq O1, O2`

```text
bits(64) address = X[O1];
bits(64) old = Acquire(Mem[address, 8]);
Release(Mem[address, 8]) = old OR X[O2];
X[O2] = old;
```

### `atomicxchgxorb O1, O2`

```text
bits(64) address = X[O1];
bits(8) old = Acquire(Mem[address, 1]);
Release(Mem[address, 1]) = old EOR X[O2]<7:0>;
X[O2]<7:0> = old;
```

### `atomicxchgxorh O1, O2`

```text
bits(64) address = X[O1];
bits(16) old = Acquire(Mem[address, 2]);
Release(Mem[address, 2]) = old EOR X[O2]<15:0>;
X[O2]<15:0> = old;
```

### `atomicxchgxori O1, O2`

```text
bits(64) address = X[O1];
bits(32) old = Acquire(Mem[address, 4]);
Release(Mem[address, 4]) = old EOR X[O2]<31:0>;
X[O2]<31:0> = old;
```

### `atomicxchgxorq O1, O2`

```text
bits(64) address = X[O1];
bits(64) old = Acquire(Mem[address, 8]);
Release(Mem[address, 8]) = old EOR X[O2];
X[O2] = old;
```

### `atomicweakcasb O1, O2, O3`

```text
bits(64) address = X[O1];
bits(8) old = Acquire(Mem[address, 1]);
if old == X[O2]<7:0> then
    Release(Mem[address, 1]) = X[O3]<7:0>;
endif
X[t0] = ZeroExtend(old, 64);
```

### `atomicweakcash O1, O2, O3`

```text
bits(64) address = X[O1];
bits(16) old = Acquire(Mem[address, 2]);
if old == X[O2]<15:0> then
    Release(Mem[address, 2]) = X[O3]<15:0>;
endif
X[t0] = ZeroExtend(old, 64);
```

### `atomicweakcasi O1, O2, O3`

```text
bits(64) address = X[O1];
bits(32) old = Acquire(Mem[address, 4]);
if old == X[O2]<31:0> then
    Release(Mem[address, 4]) = X[O3]<31:0>;
endif
X[t0] = ZeroExtend(old, 64);
```

### `atomicweakcasq O1, O2, O3`

```text
bits(64) address = X[O1];
bits(64) old = Acquire(Mem[address, 8]);
if old == X[O2] then
    Release(Mem[address, 8]) = X[O3];
endif
X[t0] = ZeroExtend(old, 64);
```

### `batomicweakcasb O1, O2, O3, O4`

```text
bits(64) address = X[O1];
bits(8) old = Acquire(Mem[address, 1]);
if old == X[O2]<7:0> then
    Release(Mem[address, 1]) = X[O3]<7:0>;
else
    BranchTo(O4);
endif
X[t0] = ZeroExtend(old, 64);
```

### `batomicweakcash O1, O2, O3, O4`

```text
bits(64) address = X[O1];
bits(16) old = Acquire(Mem[address, 2]);
if old == X[O2]<15:0> then
    Release(Mem[address, 2]) = X[O3]<15:0>;
else
    BranchTo(O4);
endif
X[t0] = ZeroExtend(old, 64);
```

### `batomicweakcasi O1, O2, O3, O4`

```text
bits(64) address = X[O1];
bits(32) old = Acquire(Mem[address, 4]);
if old == X[O2]<31:0> then
    Release(Mem[address, 4]) = X[O3]<31:0>;
else
    BranchTo(O4);
endif
X[t0] = ZeroExtend(old, 64);
```

### `batomicweakcasq O1, O2, O3, O4`

```text
bits(64) address = X[O1];
bits(64) old = Acquire(Mem[address, 8]);
if old == X[O2] then
    Release(Mem[address, 8]) = X[O3];
else
    BranchTo(O4);
endif
X[t0] = ZeroExtend(old, 64);
```

### `loadlinkacqb O1, O2`

```text
bits(64) address = X[O2];
X[O1] = ZeroExtend(AcquireExclusive(Mem[address, 1]), 64);
```

### `loadlinkacqh O1, O2`

```text
bits(64) address = X[O2];
X[O1] = ZeroExtend(AcquireExclusive(Mem[address, 2]), 64);
```

### `loadlinkacqi O1, O2`

```text
bits(64) address = X[O2];
X[O1] = ZeroExtend(AcquireExclusive(Mem[address, 4]), 64);
```

### `loadlinkacqq O1, O2`

```text
bits(64) address = X[O2];
X[O1] = ZeroExtend(AcquireExclusive(Mem[address, 8]), 64);
```

### `storecondrelb O1, O2, O3`

```text
bits(64) address = X[O1];
boolean succeeded = ReleaseExclusive(Mem[address, 1]) = X[O3]<7:0>;
X[O2] = if succeeded then 0 else 1;
```

### `storecondrelh O1, O2, O3`

```text
bits(64) address = X[O1];
boolean succeeded = ReleaseExclusive(Mem[address, 2]) = X[O3]<15:0>;
X[O2] = if succeeded then 0 else 1;
```

### `storecondreli O1, O2, O3`

```text
bits(64) address = X[O1];
boolean succeeded = ReleaseExclusive(Mem[address, 4]) = X[O3]<31:0>;
X[O2] = if succeeded then 0 else 1;
```

### `storecondrelq O1, O2, O3`

```text
bits(64) address = X[O1];
boolean succeeded = ReleaseExclusive(Mem[address, 8]) = X[O3];
X[O2] = if succeeded then 0 else 1;
```

### `memfence`

```text
Barrier(Full);
```

### `fence`

```text
Barrier(Sync);
```

### `pause`

```text
SpinLoopHint();
```

## 8. Directives, annotations, and the interpreter loop

### Scratch registers

No entry in this section clobbers a scratch register on any target. The `rloop*` entries lower only on the `rloop` backend, which has no native registers.

### `emit O1, ..., On`

```text
EmitRawText(O1, O2, ..., On);
```

`offlineasm` only.

### `tagCodePtr`

```text
// no-op annotation; consumed by lowering, has no runtime effect
```

### `tagReturnAddress`

```text
// no-op annotation; consumed by lowering, has no runtime effect
```

### `untagReturnAddress`

```text
// no-op annotation; consumed by lowering, has no runtime effect
```

### `removeCodePtrTag`

```text
// no-op annotation; consumed by lowering, has no runtime effect
```

### `untagArrayPtr`

```text
// no-op annotation; consumed by lowering, has no runtime effect
```

### `removeArrayPtrTag`

```text
// no-op annotation; consumed by lowering, has no runtime effect
```

### `rloopCrash`

```text
Trap();
```

`rloop` backend only.

### `rloopCallNativeFunction O1`

```text
CallNative(O1);
SuspendLoop();
```

`rloop` backend only.

### `rloopCallNative O1`

```text
CallNative(O1);
```

`rloop` backend only.

### `rloopCallSlowPath O1`

```text
CallSlowPath(O1);
```

`rloop` backend only.

### `rloopCallSlowPath3 O1`

```text
CallSlowPath(O1);
```

`rloop` backend only.

### `rloopCallSlowPath4 O1`

```text
CallSlowPath(O1);
```

`rloop` backend only.

### `rloopCallSlowPathVoid O1`

```text
CallSlowPath(O1);
```

`rloop` backend only.

### `rloopDo`

```text
// annotation passthrough
```

`rloop` backend only.

## Availability

Every entry above is accepted by both assemblers, except these families.

- Offlineasm only: `emit`.
- Offlineasm's `rloop` backend only: `rloopCrash`, `rloopCallNativeFunction`, `rloopCallNative`, `rloopCallSlowPath`, `rloopCallSlowPath3`, `rloopCallSlowPath4`, `rloopCallSlowPathVoid`, `rloopDo`.
