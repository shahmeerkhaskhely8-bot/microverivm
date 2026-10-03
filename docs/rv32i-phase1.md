# RV32I Formalization: Phase 1 Foundations

This document explains the foundational Coq modules for the RV32I migration. The modules establish a word type, a structurally x0-safe register file, and an aligned-PC machine-state type. They define architectural data structures and arithmetic only; they do **not** yet define RV32I instruction execution, traps, memory, CSRs, privilege modes, or a refinement relation to the existing MicroVeriVM stack machine.

Phase 2 adds a named instruction subset and encoding decoder; see the
[Phase 2 guide](rv32i-phase2.md). Instruction execution and refinement remain
out of scope.

## Specification assumptions

No separate RV32I specification document was present in the workspace when these definitions were added. The Phase 1 model therefore states its assumptions directly:

- XLEN is 32 bits; words range from 0 through \(2^{32}-1\).
- There are 32 architectural register indices, x0 through x31.
- x0 always reads as zero and ignores writes; the register-file payload stores only x1 through x31.
- This model uses base RV32I instruction alignment, IALIGN=32: instruction addresses are four-byte aligned. The compressed extension (IALIGN=16) is not modeled.

If a project-specific specification differs on any of these points, revise the definitions before adding instruction semantics.

## Module dependency diagram

```text
RiscV/Word.v
    |
    +--> RiscV/RegisterFile.v
                |
                +--> RiscV/Machine.v
                |
                +--> RiscV/Instruction.v
                            |
                            +--> RiscV/Decoder.v
```

### `coq/RiscV/Word.v`

The type `rv32_word` is a dependent pair carrying a natural-number value and a proof that it is below \(2^{32}\). `rv32_word_wrap` constructs a word by modulo reduction. `rv32_add` and `rv32_sub` use that constructor to model modulo-\(2^{32}\) arithmetic.

Closed lemmas include:

- `rv32_modulus_is_two_to_32`: the word modulus is exactly \(2^{32}\);
- `rv32_word_range` and `rv32_word_wrap_range`: all constructed words are in range;
- `rv32_word_wrap_small`: wrapping a value already in range leaves it unchanged;
- `rv32_add_spec` and `rv32_sub_spec`: the arithmetic results are precisely the corresponding modular expressions;
- `rv32_add_max_one_wraps` and `rv32_sub_zero_one_wraps`: representative word-boundary results;
- `rv32_add_preserves_range` and `rv32_sub_preserves_range`: arithmetic returns valid words.

These properties specify mathematical word behavior. They do not yet prove correspondence with generated or compiled RV32 machine code.

### `coq/RiscV/RegisterFile.v`

`rv32_register_file` is exactly `Vector.t rv32_word 31`: there is no stored slot for x0. The index type has two forms:

- `RV32X0`, the fixed zero register;
- `RV32WritableIndex index`, where `index : Fin.t 31` addresses one of the 31 stored writable registers.

`rv32_read_register` returns `rv32_word_zero` for x0 and reads the vector for a writable index. `rv32_write_register` returns the original file for x0 and replaces the selected writable entry otherwise. This makes the x0 behavior structural rather than a convention callers must maintain.

`rv32_register_index_number` maps an index to its architectural number, from zero through 31. `rv32_register_index_in_range` proves that every index inhabiting the type has a number in that interval. The lemmas `rv32_x0_reads_zero`, `rv32_write_x0_is_immutable`, and `rv32_x0_remains_zero_after_any_write` establish the hardwired-zero property.

### `coq/RiscV/Machine.v`

The PC is represented by `rv32_pc`, a 32-bit word paired with a proof that its value is divisible by `rv32_instruction_alignment`, defined as four. Thus any value stored in the machine state's PC is aligned by construction. `rv32_pc_zero` gives a valid aligned initial PC.

`machine_status` distinguishes `MachineRunning`, `MachineHalted`, and `MachineTrapped`. `rv321_state` contains the aligned PC, the explicit 31-register file, and the execution status. The requested identifier `rv321_state` is retained; `rv32i_state` is also provided as an intuitively named alias.

`rv321_state_pc_is_aligned` projects the alignment guarantee for any state. `rv321_initial_state` initializes the PC to zero, all writable registers to zero, and status to running.

## Build and verify

From the repository root, run the full project gate:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\check-coq.ps1
```

The gate compiles all 30 configured modules, including the 16 modules under `coq/RiscV/`, and runs `coqchk` across the full module list. The Phase 1 modules can also be compiled independently in dependency order:

```powershell
$coqc = "C:\path\to\rocq\bin\coqc.exe"
& $coqc -q -w "+default" -Q coq MicroVeriVM coq\RiscV\Word.v
& $coqc -q -w "+default" -Q coq MicroVeriVM coq\RiscV\RegisterFile.v
& $coqc -q -w "+default" -Q coq MicroVeriVM coq\RiscV\Machine.v
```

Replace the example compiler path with the installed Rocq `coqc.exe` location. Each command must exit with status zero and produce no diagnostics.

## Subsequent phases

The RV32I instruction AST and decoder are documented in [Phase 2](rv32i-phase2.md),
operational semantics and control-flow behavior in [Phase 3](rv32i-phase3.md),
memory safety in [Phase 4](rv32i-phase4.md), and finite execution traces in
[Phase 5](rv32i-phase5.md). Each phase states its architectural preconditions
and proves its guarantees with closed Coq terms. System-level binary-image
integration is covered in [Phase 6](rv32i-phase6.md), and exception-aware
execution is covered in [Phase 7](rv32i-phase7.md).
