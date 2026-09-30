// A small register-based bytecode interpreter in the style of WebKit's
// LLInt. `main.rs` compiles this file twice: once with `backend = native`
// (machine code through `global_asm!`) and once with `backend = rloop` (a
// Rust dispatch loop). The source is the same for both.
//
// Machine state:
//   PC     the current bytecode instruction (a pointer to its first word)
//   IBASE  the context block: jump tables, lengths and host hooks
//   cfr    the current bytecode frame (see "Frames" below)
//   sp     the machine stack pointer; bytecode frames live on it
//
// Bytecode is a sequence of 64-bit words: an opcode followed by its
// operands. Register operands are stored pre-scaled as byte offsets from
// `cfr` (register r is -8 * (r + 1) - 16), so reading one is a single
// `loadq t, [cfr, off, 1]`. Jump and call targets are word offsets from
// the start of the instruction.
//
// Frames. A bytecode call is a machine call: `call` pushes a header and
// runs the callee's handlers with a real `call`, and the callee's `ret`
// is a real `ret` back into the caller's `call` handler. On rloop the same
// `call`/`ret` go through `lr`. A frame, from `cfr` down:
//   8[cfr]   the caller's call instruction (0 for the outermost frame)
//   0[cfr]   the caller's cfr
//   -8[cfr]  the return address: pushed by `call` on x86-64, stored from
//            `lr` by `enter` on AArch64 and rloop
//   -16[cfr] padding; on RISC-V, `call` spills the caller's `ra` into
//            -16..0[cfr] itself and `ra` survives calls, so nothing to save
//   -24[cfr] register 0, then register 1 below it, and so on
//
// Two dispatch styles share every handler body (each body is a macro that
// takes the dispatch macro as an argument):
//   token threaded   the opcode word indexes a jump table:
//                    `loadq t0, [PC]` then `jmp [IBASE, t0, 8]`
//   direct threaded  a link pass first rewrites every opcode word to its
//                    handler's address, then dispatch is `jmp [PC]`
// Both tables are filled at entry with `leap` of the handler labels. On
// the native backend they hold code addresses; on rloop they hold `Opcode`
// numbers, and `jmp` through memory dispatches on those.

// The first label is the rloop entry point, so no label may precede
// `_llint_entry`. Constants and macros are fine.

if X86_64
    // System V: rdi, rsi, rdx.
    const a0 = t6
    const a1 = t1
    const a2 = t2
else
    // AArch64, RISC-V and rloop: t0, t1, t2. rloop's `call_native` hook
    // also passes t0/t1.
    const a0 = t0
    const a1 = t1
    const a2 = t2
end

const PC = csr0
const IBASE = csr1

const NUM_OPCODES = 11
const TOKEN_TABLE = 0
const THREADED_TABLE = NUM_OPCODES * 8
const LENGTHS = NUM_OPCODES * 16
const HOST_PRINT = NUM_OPCODES * 24
const CODE_WORDS = NUM_OPCODES * 24 + 8

macro forEachOpcode(m)
    m(0, _llint_op_enter, _llint_op_enter_t, 2)
    m(1, _llint_op_movi, _llint_op_movi_t, 3)
    m(2, _llint_op_mov, _llint_op_mov_t, 3)
    m(3, _llint_op_add, _llint_op_add_t, 4)
    m(4, _llint_op_sub, _llint_op_sub_t, 4)
    m(5, _llint_op_mul, _llint_op_mul_t, 4)
    m(6, _llint_op_jlt, _llint_op_jlt_t, 4)
    m(7, _llint_op_jmp, _llint_op_jmp_t, 2)
    m(8, _llint_op_call, _llint_op_call_t, 5)
    m(9, _llint_op_ret, _llint_op_ret_t, 2)
    m(10, _llint_op_print, _llint_op_print_t, 2)
end

macro initOpcode(index, token, threaded, length)
    leap t0, token
    storeq (TOKEN_TABLE + index * 8)[IBASE], t0
    leap t0, threaded
    storeq (THREADED_TABLE + index * 8)[IBASE], t0
    move t0, length
    storeq (LENGTHS + index * 8)[IBASE], t0
end

macro dispatchToken(length)
    addp PC, length * 8
    loadq t0, [PC]
    jmp [IBASE, t0, 8]
end

macro dispatchThreaded(length)
    addp PC, length * 8
    jmp [PC]
end

// Load the handler for the instruction at PC into `dst`, for `call`.
macro tokenHandler(dst)
    loadq dst, [PC]
    loadq dst, [IBASE, dst, 8]
end

macro threadedHandler(dst)
    loadq dst, [PC]
end

// Loads the register named by operand `index` (1-based word index) into
// `dst`. `dst` doubles as the scratch for the operand word.
macro loadOperand(dst, index)
    loadq dst, (index * 8)[PC]
    loadq dst, [cfr, dst, 1]
end

macro storeOperand(index, value, scratch)
    loadq scratch, (index * 8)[PC]
    storeq [cfr, scratch, 1], value
end

// Adds the word offset in `offset` to PC.
macro jumpBy(offset, dispatch)
    lshiftq offset, 3
    addp PC, offset
    dispatch(0)
end

// Entry/exit. Saves what this code uses from the callee-saved set: PC,
// IBASE and cfr, plus `lr` everywhere except x86-64, since `call` writes it
// on AArch64, RISC-V and rloop. Either way `sp` ends up 16-byte aligned for
// the host calls (x86-64's return address is the fourth slot). On rloop the
// pushes land on the host-provided stack.
macro prologue()
    if X86_64
        push csr0, csr1, cfr
    else
        push csr0, csr1, cfr, lr
    end
end

macro epilogue()
    if X86_64
        pop csr0, csr1, cfr
    else
        pop csr0, csr1, cfr, lr
    end
end

// llint_entry(code: *mut u64, context: *mut u64, threaded: u64) -> u64
global _llint_entry
_llint_entry:
    prologue()
    move PC, a0
    move IBASE, a1
    move t3, a2

    forEachOpcode(initOpcode)

    btqz t3, .token

    // Link pass: rewrite each opcode word to its direct-threaded handler.
    move t1, PC
    loadq t2, CODE_WORDS[IBASE]
    lshiftq t2, 3
    addp t2, PC
.link:
    bpaeq t1, t2, .linked
    loadq t0, [t1]
    loadq t4, LENGTHS[IBASE, t0, 8]
    loadq t0, THREADED_TABLE[IBASE, t0, 8]
    storeq [t1], t0
    lshiftq t4, 3
    addp t1, t4
    jmp .link
.linked:
    threadedHandler(t0)
    jmp .run
.token:
    tokenHandler(t0)
.run:
    // Call the program like any bytecode function, from a frame with no
    // caller. Its `ret` comes back here with the result in t0.
    move t1, 0
    push t1, t1
    move cfr, sp
    call t0
    addp sp, 16
    epilogue()
    ret

// Handler bodies. Each takes the dispatch macro to finish with.

// enter nregs: the first instruction of every function. Reserves the
// registers (rounded to 16 bytes) below the return-address slot, saves `lr`
// into that slot where `call` left it there, and copies the arguments named
// by the caller's call instruction into r0, r1, ...
macro opEnter(dispatch)
    loadq t0, 8[PC]
    lshiftq t0, 3
    addq t0, 15
    andq t0, -16
    move t1, cfr
    subp t1, 16
    subp t1, t0
    move sp, t1
    if ARM64 or RLOOP
        storeq -8[cfr], lr
    end

    loadq t1, 8[cfr]
    btqz t1, .copied
    loadq t0, 24[t1]
    loadq t2, 32[t1]
    loadq t3, 0[cfr]
    move t4, -24
.copy:
    btqz t0, .copied
    loadq t5, [t3, t2, 1]
    storeq [cfr, t4, 1], t5
    subq t2, 8
    subq t4, 8
    subq t0, 1
    jmp .copy
.copied:
    dispatch(2)
end

// movi dst, imm
macro opMovi(dispatch)
    loadq t1, 16[PC]
    storeOperand(1, t1, t0)
    dispatch(3)
end

// mov dst, src
macro opMov(dispatch)
    loadOperand(t1, 2)
    storeOperand(1, t1, t0)
    dispatch(3)
end

// op dst, lhs, rhs, where `op` is a two-operand macro.
macro opBinary(op, dispatch)
    loadOperand(t1, 2)
    loadOperand(t2, 3)
    op(t1, t2)
    storeOperand(1, t1, t0)
    dispatch(4)
end

macro addValues(dst, src)
    addq dst, src
end

macro subValues(dst, src)
    subq dst, src
end

macro mulValues(dst, src)
    mulq dst, src
end

macro opAdd(dispatch)
    opBinary(addValues, dispatch)
end

macro opSub(dispatch)
    opBinary(subValues, dispatch)
end

macro opMul(dispatch)
    opBinary(mulValues, dispatch)
end

// jlt lhs, rhs, offset: signed compare.
macro opJlt(dispatch)
    loadOperand(t1, 1)
    loadOperand(t2, 2)
    bqlt t1, t2, .taken
    dispatch(4)
.taken:
    loadq t0, 24[PC]
    jumpBy(t0, dispatch)
end

// jmp offset
macro opJmp(dispatch)
    loadq t0, 8[PC]
    jumpBy(t0, dispatch)
end

// call dst, offset, argc, firstArg
//
// Pushes the header (this instruction, the caller's cfr), makes it the
// callee's cfr and `call`s the callee's first handler. The callee's
// `enter` finishes the frame and `ret` returns here with the result in t0.
macro opCall(dispatch, handler)
    push PC, cfr
    move cfr, sp
    loadq t0, 16[PC]
    lshiftq t0, 3
    addp PC, t0
    handler(t0)
    call t0
    pop PC, cfr
    storeOperand(1, t0, t1)
    dispatch(5)
end

// ret src: the result goes in t0, `sp` goes back to where the caller's
// `call` left it and `ret` returns into the caller's `call` handler.
macro opRet(dispatch)
    loadOperand(t0, 1)
    move sp, cfr
    if X86_64
        subp sp, 8
    elsif RISCV64
        subp sp, 16
    else
        loadq lr, -8[cfr]
    end
    ret
end

// print src: hand the value to the host.
macro opPrint(dispatch)
    loadOperand(a0, 1)
    move a1, 0
    // A native function pointer: a machine call on the native backends,
    // the host's `call_native` thunk on rloop.
    loadq t2, HOST_PRINT[IBASE]
    call t2
    dispatch(2)
end

// Every handler twice, once per dispatch style.
_llint_op_enter:
    opEnter(dispatchToken)
_llint_op_movi:
    opMovi(dispatchToken)
_llint_op_mov:
    opMov(dispatchToken)
_llint_op_add:
    opAdd(dispatchToken)
_llint_op_sub:
    opSub(dispatchToken)
_llint_op_mul:
    opMul(dispatchToken)
_llint_op_jlt:
    opJlt(dispatchToken)
_llint_op_jmp:
    opJmp(dispatchToken)
_llint_op_call:
    opCall(dispatchToken, tokenHandler)
_llint_op_ret:
    opRet(dispatchToken)
_llint_op_print:
    opPrint(dispatchToken)

_llint_op_enter_t:
    opEnter(dispatchThreaded)
_llint_op_movi_t:
    opMovi(dispatchThreaded)
_llint_op_mov_t:
    opMov(dispatchThreaded)
_llint_op_add_t:
    opAdd(dispatchThreaded)
_llint_op_sub_t:
    opSub(dispatchThreaded)
_llint_op_mul_t:
    opMul(dispatchThreaded)
_llint_op_jlt_t:
    opJlt(dispatchThreaded)
_llint_op_jmp_t:
    opJmp(dispatchThreaded)
_llint_op_call_t:
    opCall(dispatchThreaded, threadedHandler)
_llint_op_ret_t:
    opRet(dispatchThreaded)
_llint_op_print_t:
    opPrint(dispatchThreaded)
