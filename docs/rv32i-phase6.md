# RV32I Formalization: Phase 6 System Integration

Phase 6 lifts the verified instruction and trace model into an application
start/run interface. The definitions and proofs are in
`coq/RiscV/SystemIntegration.v`.

## Binary-image boundary

`rv32_binary_image` contains two lists of 32-bit words: text encodings and
initial data memory. Text entries use `rv32_word`, so each encoding is a
32-bit value by construction. `rv32_load_binary_text` converts this text
segment to the `rv32_program` representation consumed by the decoder and
program-fetch relation.

The image is the output contract of an external loader, such as an ELF loader:
the text segment must already be split into aligned 32-bit instruction words,
and data must already be represented as machine words. ELF headers, sections,
relocations, byte ordering, and byte-to-word decoding are not defined or
verified here. This boundary makes no claim about the correctness of any
external loader.

`rv32_start_application` connects the loaded image's data memory to the
verified initial machine state: PC zero, zeroed registers with immutable x0,
and running status. The executable `rv32_run_application` loads the text
encodings and performs at most the requested number of program steps.

## Integration guarantees

The module proves:

- loading preserves the text instruction count and every loaded encoding is
  within the 32-bit word range;
- a nonempty loaded text segment fetches its first encoding at the initial PC;
- every nonempty application has an initial program-step successor;
- every application starts in the machine safety invariant (aligned PC,
  immutable x0, and well-formed word memory);
- application steps are deterministic and preserve that invariant;
- a successful application step agrees with one execution of the bounded
  runner;
- each bounded application result is a program trace and has an exact-step
  trace whose step count does not exceed the supplied fuel;
- bounded application execution preserves safety and data-memory length; and
- outcomes of equal-length application traces from the same initial state are
  identical.

The step-count result allows early termination: execution may stop when the
machine is halted or trapped, or when the PC cannot fetch an instruction.
This is not a claim that every fuel unit produces a transition. Exact-length
trace determinism applies when the transition count is equal; it does not
equate traces of different lengths.

## Verification

Run from the repository root:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\check-coq.ps1
```

The gate compiles all configured modules and validates them using `coqchk`.
`SystemIntegration.v` follows `Execution.v` in `_CoqProject`, the PowerShell
gate, the GitHub Actions kernel-check list, and the Cargo package manifest.
Exception-aware trap routing over the application runner is developed in
[Phase 7](rv32i-phase7.md).
