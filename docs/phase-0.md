# MicroVeriVM — Phase 0

Phase 0 initializes the repository boundary without implementing a virtual
machine.

## Invariants

- The Rust library is `#![no_std]`.
- Unsafe Rust is forbidden with `#![forbid(unsafe_code)]`.
- The crate has no dependencies and performs no heap allocation.
- No VM instructions, state, interpreter, compiler, or execution logic is
  present.
- Coq, tests, scripts, and documentation directories are established for later
  phases.

## Gate

Run `make phase0` on systems with Make, or run
`powershell -NoProfile -ExecutionPolicy Bypass -File scripts/phase0-gate.ps1`
directly on Windows.
