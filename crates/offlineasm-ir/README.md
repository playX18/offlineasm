# offlineasm-ir

The IR shared by `offlineasm` and `onlineasm`. It holds `Inst` and
`Op`, the register definitions with each target's vreg-to-physical table, and
`expand`. `expand` lowers one mnemonic invocation to core instructions.

```text
spelling --> Mnemonic--> expand() + Ops --> Expansion --backend--> machine code | asm text
```

`offlineasm` lowers each instruction with `expand` and prints assembly text.
`onlineasm` lowers with `expand` and encodes machine code.

Depend on `offlineasm` or `onlineasm` instead unless you are building another
backend.
