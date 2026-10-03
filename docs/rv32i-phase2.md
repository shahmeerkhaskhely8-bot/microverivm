# RV32I Formalization: Phase 2 Instruction Subset and Decoder

Phase 2 builds on the word, register-file, and machine-state definitions in
[Phase 1](rv32i-phase1.md). It adds a typed instruction AST and a separate
32-bit encoding decoder. This is an explicitly selected subset, not a claim to
cover the entire RV32I base ISA.

## Supported instruction subset

| Format | Instructions |
| --- | --- |
| R | `ADD`, `SUB` |
| I | `ADDI`, `LW`, `JALR` |
| S | `SW` |
| B | `BEQ` |
| U | `LUI` |
| J | `JAL` |

The AST in `coq/RiscV/Instruction.v` uses the existing finite architectural
register-index type. Immediate values are bounded raw instruction fields;
they are not prematurely treated as signed machine integers. This keeps field
placement separate from interpretation.

## Module responsibilities

### `coq/RiscV/Instruction.v`

Defines `rv32_instruction`, the six-format classification, and bounded raw
immediate subtypes: 12, 13, 20, and 21 bits. `rv32_format_of_instruction`
classifies each constructor. A closed theorem establishes that every AST
constructor belongs to one of the six declared formats.

### `coq/RiscV/Decoder.v`

The decoder is organized into independent steps:

1. `rv32_extract_bits` extracts a field by right shift and modulo; its range
   theorem proves the result fits the requested field width.
2. `rv32_decode_rd`, `rv32_decode_rs1`, and `rv32_decode_rs2` build values of
   the finite register-index type. Their range theorems establish indices
   from x0 through x31.
3. The I/S/B/U/J immediate extractors state the format-specific bit placement.
   I and U use contiguous fields; S, B, and J reconstruct their split fields.
   Range proofs establish that these reconstructed values fit the AST's
   bounded immediate types.
4. `rv32_sign_extend_12`, `rv32_sign_extend_13`, and
   `rv32_sign_extend_21` interpret the raw fields as 32-bit words. Positive
   and negative lemmas establish the resulting unsigned word value on each
   side of the sign-bit boundary.
5. `rv32_encode` and `rv32_decode_candidate` are separate from bit extraction.
   The final `rv32_decode` checks the 32-bit word bound, supported instruction
   fields, and exact canonical re-encoding. It distinguishes malformed
   encodings of supported opcodes (`RV32IllegalEncoding`) from opcodes outside
   the selected subset (`RV32UnsupportedEncoding`).

`rv32_accepted_encoding_round_trips` proves that every result classified as
`RV32Decoded` carries an encoding equality: re-encoding its instruction
produces the original word. Register validity for each accepted instruction
constructor is also proved. These theorems concern the decoder/encoder
contract; they do not establish instruction execution semantics.

## Scope and subsequent phase

The decoder alone does not model execution, data memory, traps, CSRs,
privilege, or refinement to the legacy stack VM. Unsupported base instructions
are deliberately outside the selected subset and are reported distinctly from
malformed encodings of supported opcodes. The execution model and its
misaligned-target behavior are specified in the [Phase 3 guide](rv32i-phase3.md).

## Verification

From the repository root, run the full compile and kernel-check gate:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\check-coq.ps1
```

The gate compiles the configured modules in dependency order and validates
them with `coqchk`. The two phase modules can also be compiled directly after
Phase 1:

```powershell
$coqc = "C:\path\to\rocq\bin\coqc.exe"
& $coqc -q -w "+default" -Q coq MicroVeriVM coq\RiscV\Instruction.v
& $coqc -q -w "+default" -Q coq MicroVeriVM coq\RiscV\Decoder.v
```

Replace the sample compiler path with the local Rocq installation. Both
modules are included in `_CoqProject`, the PowerShell verification gate, the
GitHub Actions kernel-check list, and the crate's published-file manifest.
