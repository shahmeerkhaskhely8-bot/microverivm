# MicroVeriVM — Phase 13 Integration Test Summary

Phase 13 adds an end-to-end Rust integration harness at
`tests/end_to_end.rs`. The harness drives the public `execute::step` API with
the Phase 2 instruction set and validates the Phase 3–6 machine components as
one execution path.

## Coverage

The integration harness validates:

- All ten instructions: `CONST`, `ADD`, `SUB`, `DUP`, `DROP`, `LOAD`, `STORE`,
  `JMP`, `JZ`, and `HALT`.
- Normal PC increment, jump targets, conditional jumps, and halt status.
- Word arithmetic wrapping at `WORD_MODULUS`.
- Stack underflow and overflow behavior.
- Memory out-of-bounds behavior for load and store.
- Preservation of a stack value when `STORE` rejects an invalid address.
- Invalid program-counter handling.
- Halted-state no-op behavior.

## Verification commands

Run from the repository root:

```text
cargo fmt --all -- --check
cargo check --locked --all-targets
cargo test --locked --all-targets
```

The integration harness is an executable test of the Rust stack VM. It is
independent of the Coq RV32I model and does not establish a refinement between
the Rust implementation and either formal machine. Standard Coq extraction
erases proof propositions; the existence of `coq/Extraction.v` is not by
itself evidence of an extracted, verified interpreter.

For the repository's current combined Rust and Coq verification status, see
the [verification snapshot](final-project-summary.md). The current gates use
locked dependencies and include all Cargo targets and all 30 configured Coq
modules.

## Scope

No VM semantics, Rust execution code, Coq syntax, Coq semantics, or proof files
were changed in Phase 13.
