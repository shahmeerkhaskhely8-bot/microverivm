# RV32I Formalization: Phase 5 Multi-Step Execution

Phase 5 lifts the small-step semantics and safety properties from
[Phases 3-4](rv32i-phase3.md) and [Phase 4](rv32i-phase4.md) to finite
program executions. The definitions and proofs are in
`coq/RiscV/Execution.v`.

## Program and traces

An `rv32_program` is a list of encoded instruction words. Instruction fetch
uses the current aligned byte PC divided by four as an index into that list.
`rv32_program_step` relates running states when a word is present at the
current PC and `rv32_step_encoded` produces the successor. Invalid or
unsupported encodings still make progress: the encoded step traps as specified
by the Phase 3 semantics. Fetch beyond the end of the finite program has no
program transition.

`rv32_program_steps` is the reflexive-transitive closure of this transition
relation. `rv32_program_steps_n` records the exact number of successful
program transitions. The exact-length relation lifts to the reflexive-
transitive closure and is deterministic: for a given program, initial state,
and transition count, all traces have the same final state.

The executable bounded runner `rv32_execute_n` takes at most the requested
number of steps. It stops early and returns the current state if execution is
halted or trapped, or if the PC is outside the program. Every bounded run is
proved to correspond to the reflexive-transitive transition closure.

## Progress and determinism

Small-step progress is correctly conditional on the program being able to
fetch an instruction: any running state with a successful fetch has a
successor. This holds even for an invalid or unsupported encoding, because
such encodings transition to `MachineTrapped`. A nonempty program whose first
word is fetchable from the initial state therefore has an initial successor.
At a halted/trapped state or beyond the end of the finite program, execution
has no further program transition and the bounded runner stops.

The one-step program relation is deterministic, since fetch selects one
encoding and encoded-step execution is a total function. Exact-length
multi-step traces are deterministic by induction. The unindexed reflexive-
transitive closure is not claimed to have a unique endpoint across traces of
different lengths (for example, loops may revisit states).

## Multi-step safety

The execution invariant combines:

- four-byte PC alignment;
- immutable x0 reads as zero;
- well-formedness of every word in finite data memory.

The invariant is preserved by each program transition, by arbitrary finite
transition traces, and by bounded execution from the initial state. Memory
length is also preserved across each transition, every finite trace, and
bounded execution. Since memory elements have the dependent `rv32_word` type,
every memory list is well-formed by construction.

## Verification

Run from the repository root:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\check-coq.ps1
```

The gate compiles the configured modules in dependency order and validates
them with `coqchk`. `Execution.v` follows `MemorySafety.v` in `_CoqProject`,
the PowerShell gate, the GitHub Actions module list, and the Cargo package
manifest. System-level image loading and bounded application properties are
covered in [Phase 6](rv32i-phase6.md).
Exception-aware trap traces are covered in [Phase 7](rv32i-phase7.md).
