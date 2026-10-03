# MicroVeriVM Repository Verification Snapshot

**Snapshot date:** October 3, 2026
**Scope:** Rust implementation, 30 configured Coq modules, local scripts, and GitHub Actions workflow definitions.

## Project structure

MicroVeriVM contains two distinct machine efforts:

1. A ten-instruction bounded stack VM implemented in `rust/src/`, with a corresponding Rust-shaped mathematical model and Coq correspondence development.
2. A separate RV32I formal model under `coq/RiscV/`, covering a named instruction subset, state and memory invariants, bounded execution, traps, privileged state, interrupts, retirement/PC event traces, and application integration.

The RV32I model receives word-sized text and data segments. ELF parsing, byte-to-word loading, and a proof that an external loader supplies a correct image are outside the model. The RV32I semantics is not claimed to refine the Rust stack-machine implementation.

## Coq development

The `_CoqProject` file and verification gate configure 30 Coq modules. This includes 16 modules under `coq/RiscV/`, from `Word.v` and `RegisterFile.v` through `ApplicationExecution.v`, `BisimulationRefinement.v`, and `SystemInvariants.v`, as well as the legacy stack-machine model, bridge, and extraction modules.

The RV32I application layer composes ordinary execution, trap-aware execution, and PC/event-tracked execution. Its theorems establish their respective safety invariants, bounded trace witnesses, event-count bounds, and equal-length trace determinism. The `BisimulationRefinement.v` results concern the Rust-shaped stack model and its separate Rocq semantics: they prove step and successful-trace correspondence in both directions under the stated relation. They do not prove refinement from the Rust source or RV32I-to-stack-machine equivalence.

The local gate scans Coq sources for `Admitted`, `admit`, `Axiom`, and `Abort`, sequentially compiles the configured modules, and runs `coqchk`. In this snapshot, all 30 modules compiled and `coqchk` validated the configured module list; the placeholder scan returned no matches.

## Rust implementation and quality gates

The Rust library is `no_std`, forbids unsafe code, and models a 256-word stack and 1024-word memory with fixed-size storage. It implements `CONST`, `ADD`, `SUB`, `DUP`, `DROP`, `LOAD`, `STORE`, `JMP`, `JZ`, and `HALT`. Arithmetic and sequential PC advancement use wrapping 32-bit operations.

The following gates passed in the recorded Windows environment:

```text
cargo fmt --all -- --check
cargo check --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked --all-targets
```

The unit and integration suites reported 12 passing tests and no failures. `scripts/phase0-gate.ps1` also passed.

## Scripts and CI

All four `scripts/*.ps1` files passed PowerShell parser validation. Both `scripts/run-pipeline.ps1` and `scripts/coq-compile-all.ps1` completed successfully. Static checks confirmed that the GitHub workflows reference the configured Coq modules and align Rust commands with the local quality gates.

The available environment did not include `actionlint` or a YAML parser; therefore, workflow validation was limited to source inspection and static command/module consistency checks, not a dedicated workflow linter or a live GitHub Actions run. `make` was also unavailable, so the Makefile targets were inspected but not executed.

## Scope and assurance limits

`coqchk` validates compiled Coq proof objects and their dependencies. It does not verify the Coq compiler or kernel implementation, the Rust compiler, the Rust source-to-model connection, binary loading, or external execution platforms. Rust build, lint, and test results are independent evidence and are not part of the Coq proof.

This snapshot records successful repository checks, not a claim of absolute correctness or complete RV32I conformance. The formal results are limited to their stated models, premises, and supported instruction subset.
