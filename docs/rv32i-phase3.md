# RV32I Formalization: Phase 3 Operational Semantics

Phase 3 adds a small-step execution model for the typed RV32I subset from
[Phase 2](rv32i-phase2.md). It operates on decoded instructions; the companion
`rv32_step_encoded` function composes decoding with execution and traps on
both malformed supported encodings and unsupported opcodes.

## Machine and memory model

`rv32_execution_state` pairs the Phase 1 architectural state with a finite
data-memory image of words, represented by a Coq list. Effective addresses
remain 32-bit byte addresses: an address is valid only when it is divisible
by four and its quotient by four indexes an existing memory word. The selected
model traps on misaligned and out-of-bounds `LW`/`SW` addresses. Successful
loads and stores require a valid address; stores replace exactly one word and
preserve the memory image length.

Instructions may step only from `MachineRunning`. `MachineHalted` and
`MachineTrapped` states are stable. A trap sets the status to
`MachineTrapped`, leaves the PC and registers unchanged, and does not modify
memory. The state currently records the trapped status, not a detailed
architectural exception cause.

Memory bounds, preservation, and non-interference proofs are developed in
[Phase 4](rv32i-phase4.md).

## Instruction transitions

`coq/RiscV/Semantics.v` defines `rv32_step_state` and `rv32_step_encoded`.
Arithmetic uses the modulo-\(2^{32}\) operations from Phase 1. I-, B-, and
J-format immediates are sign-extended before addition. Sequential PC advance
wraps the aligned instruction index modulo \(2^{30}\), equivalent to adding
four bytes in the 32-bit address space. Branch and jump targets are computed
from the current PC plus the sign-extended byte offset.

- `ADD`, `SUB`, `ADDI`, `LUI`: write the computed value to `rd` (a write to
  x0 is ignored) and advance the PC by four.
- `LW`: load the word at `rs1 + sign_extend(imm12)`, then write `rd` and
  advance; invalid effective addresses trap.
- `SW`: store `rs2` at `rs1 + sign_extend(imm12)`, then advance; invalid
  effective addresses trap.
- `BEQ`: if the source values compare equal, branch by the sign-extended
  B-immediate; otherwise advance by four. A taken target that is not
  four-byte aligned traps.
- `JAL`: branch by the sign-extended J-immediate and write the sequential
  PC to `rd`. A misaligned target traps without changing the PC or registers.
- `JALR`: compute `rs1 + sign_extend(imm12)` modulo \(2^{32}\), clear bit 0,
  write the sequential PC to `rd`, and jump. If the resulting target is not
  four-byte aligned, execution traps without changing the PC or registers.
- Invalid and unsupported instruction words trap through `rv32_step_encoded`.

The existing typed AST also contains `LUI`; Phase 3 gives it semantics so the
operational model covers every constructor in that AST, in addition to the
instructions listed above.

## Closed properties

The module proves:

- the 32-bit PC space contains exactly \(2^{30}\) aligned instruction slots;
- PC advancement returns an aligned PC;
- misaligned data addresses are rejected by both load and store;
- successful stores preserve memory length;
- decoded-instruction and encoded-instruction step relations are deterministic;
- every step preserves the PC-alignment and hardwired-x0 invariants;
- malformed and unsupported instruction encodings trap while preserving PC
  and data memory.

PC alignment and x0 are structural invariants of the state and register-file
types. Dynamic branch/jump alignment and memory-boundary failures are handled
by the step functions as explicit transitions to `MachineTrapped`.

## Scope

This phase defines formal execution over the selected instruction subset. It
does not model a program image or instruction fetch, detailed exception
causes, CSRs, privilege modes, the complete RV32I base ISA, or refinement to
the legacy stack VM. The finite data-memory list is an abstract machine-state
parameter; it does not prescribe a physical memory size or an execution
environment interface.

## Verification

Run the integrated Coq compilation and kernel-validation gate from the
repository root:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\check-coq.ps1
```

The gate compiles all configured modules in dependency order and validates
the resulting proof objects with `coqchk`. Phase 3 is part of `_CoqProject`,
the PowerShell gate, the GitHub Actions kernel-check list, and the Cargo
package manifest.
