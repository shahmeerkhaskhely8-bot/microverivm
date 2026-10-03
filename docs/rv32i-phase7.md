# RV32I Formalization: Phase 7 Exception and Trap Handling

Phase 7 adds exception classification, trap entry/return, and exception-aware
bounded execution as a layer over the existing instruction, execution, and
system-integration modules. The implementation is in
`coq/RiscV/TrapHandling.v`; `coq/RiscV/SystemIntegration.v` lifts its
properties to loaded binary images. The core instruction AST and ordinary
instruction-step definitions are unchanged.

## Exception classification

The extension defines these causes:

| Condition | Cause | Trap value |
| --- | --- | --- |
| Exact ECALL encoding `0x00000073` | Environment call | Zero |
| Decoder returns illegal or unsupported | Illegal instruction | The 32-bit instruction encoding |
| LW effective address is not four-byte aligned | Load address misaligned | Effective address |
| SW effective address is not four-byte aligned | Store address misaligned | Effective address |
| Aligned LW/SW address is outside modeled word memory | Load/store access fault | Effective address |
| Taken BEQ, JAL, or JALR target is not four-byte aligned | Instruction address misaligned | Target address |

Misalignment is checked before memory bounds, so an unaligned out-of-range
access is classified as an alignment fault. Aligned accesses that do not name
a word in the finite memory are classified as access faults. ECALL is
recognized by its exact encoding before the subset decoder classifies it as
unsupported. The machine-return encoding `0x30200073` is handled by this
extension without adding it to the instruction AST.

## Trap entry and return

`rv32_system_state` pairs the existing execution state with a stack of
`rv32_trap_frame` records. When a running system state fetches an encoding
classified as an exception, the system transition:

1. records the faulting PC, cause, and trap value in a new top frame;
2. redirects the PC to the caller-supplied, aligned handler PC;
3. leaves registers and data memory unchanged; and
4. keeps the machine running so handler instructions can execute.

The handler may change the saved return PC with `rv32_update_saved_pc`.
Executing the exact machine-return encoding with an active frame pops that
frame and resumes at its saved PC, preserving handler-updated registers and
memory. Executing machine return without a frame raises an illegal-instruction
trap. A stack of frames makes nested traps explicit.

This is an extension-level handler interface, not a complete privileged
architecture: machine privilege modes, `mtvec`/`mepc`/`mcause`/`mtval` CSRs,
interrupts, delegation, and platform-specific exception codes are not modeled.
The handler PC is a parameter and must itself be a valid aligned `rv32_pc`.
Trap entry/return and frame update do not modify the core machine or
instruction definitions.

## Execution guarantees

`rv32_system_step_result` defines the exception-aware transition function;
`rv32_system_step` relates states to its successful results.
`rv32_system_execute_n` runs at most the requested fuel, and
`rv32_system_steps_n` records its exact transition count. The module proves:

- deterministic one-step system transitions;
- safety preservation for trap entry, trap return, ordinary execution, and
  bounded runs;
- equal-length system-trace determinism;
- a bounded exact-trace witness for every bounded run;
- exact fault PC recording, handler redirection, and undefined return without
  an active frame; and
- the machine-return-without-frame illegal-trap behavior.

The safety invariant is the Phase 5 aligned-PC, immutable-x0, and
well-formed-word-memory invariant on the core execution state. Trap frame PCs
are aligned by their `rv32_pc` type. Instruction fetch itself cannot encounter
a misaligned PC because the machine PC is aligned by construction; the
instruction-address-misaligned cause covers misaligned control-transfer
targets.

`rv32_run_application_with_traps` in `SystemIntegration.v` combines the binary
image model, the initial execution state, the supplied handler PC, and the
exception-aware bounded runner. The ELF/binary parsing boundary remains the
Phase 6 word-segment contract.

## Verification

Run from the repository root:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\check-coq.ps1
```

The gate compiles all configured modules and runs `coqchk`. Phase 7 is listed
after `Execution.v` and before `SystemIntegration.v` in `_CoqProject`, the
PowerShell gate, the CI kernel-check list, and the Cargo package manifest.
