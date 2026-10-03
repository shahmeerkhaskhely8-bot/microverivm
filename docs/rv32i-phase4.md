# RV32I Formalization: Phase 4 Memory Safety

Phase 4 adds memory and register safety properties over the operational model
from [Phase 3](rv32i-phase3.md). The proofs are in
`coq/RiscV/MemorySafety.v`; they extend the semantics without changing the
foundational word, register-file, or machine-state types.

## Address validity and bounds

Data memory is a finite list of 32-bit words. RV32I effective addresses are
byte addresses; only four-byte-aligned addresses whose word index is inside
the list are valid. The semantics reject misaligned addresses, and list
indexing or functional store returns `None` when an access is out of bounds.

For every successful load and store, `rv32_memory_address_valid` holds. A
successful store writes its requested value at exactly the selected word
index, preserves the memory length, and leaves every distinct list index
unchanged. Consequently, an index that was outside the original memory
remains outside and reads as `None` after a successful store. A successful
load does not mutate memory.

## Step-level properties

The module proves that:

- `LW` leaves data memory unchanged when the read succeeds;
- `SW` leaves every non-target memory index unchanged when the write
  succeeds;
- successful `SW` preserves memory length, while failed `LW`/`SW` steps trap
  atomically without partially changing registers;
- every decoded-instruction step preserves memory length;
- every encoded-instruction step preserves memory length, including traps
  for unsupported or malformed encodings;
- register reads are always 32-bit words, every memory element is a 32-bit
  word, and the existing step theorems preserve PC alignment and hardwired
  x0.

Non-interference is stated in terms of list indices: if the queried index
differs from the store's word index, its `nth_error` result is unchanged.
Aligned byte addresses map to those word indices by division by four.
Unaligned byte addresses are rejected before the list is read or modified.

## Trust and scope

All claims are proved in Rocq without project axioms or proof placeholders and
are checked by the repository's `coqchk` gate. These are properties of the
formal list-backed memory model, not a mechanized proof of the separately
maintained Rust implementation. The model does not specify physical memory,
concurrency, MMIO, or aliasing between external devices.

## Verification

From the repository root:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\check-coq.ps1
```

This compiles all configured modules in dependency order and validates their
proof objects with `coqchk`. `MemorySafety.v` is listed after
`RiscV/Semantics.v` in `_CoqProject`, the PowerShell gate, GitHub Actions,
and the Cargo package manifest.

Multi-step execution and trace preservation are covered in
[Phase 5](rv32i-phase5.md).
