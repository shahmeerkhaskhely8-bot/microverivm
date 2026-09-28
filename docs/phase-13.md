# MicroVeriVM — Phase 13 Verification Summary

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
cargo fmt --check
cargo check
cargo test
```

The integration harness is the Phase 13 end-to-end executable check. Coq
artifacts remain the formal specification/proof boundary. The current Phase 12
extraction setup emits executable syntax/state/arithmetic definitions; the
inductive `step`, trace, equivalence, and proof relations live in `Prop` and
are therefore erased by standard Coq extraction rather than emitted as an
unchecked interpreter.

## Scope

No VM semantics, Rust execution code, Coq syntax, Coq semantics, or proof files
were changed in Phase 13.
