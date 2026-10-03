(* Typed abstract syntax for the supported RV32I base instruction subset. *)

From Stdlib Require Import NArith.NArith.
From MicroVeriVM Require Import RiscV.RegisterFile.

Open Scope N_scope.

Definition rv32_imm12 := { bits : N | bits < 4096 }.
Definition rv32_imm13 := { bits : N | bits < 8192 }.
Definition rv32_imm20 := { bits : N | bits < 1048576 }.
Definition rv32_imm21 := { bits : N | bits < 2097152 }.

Definition rv32_imm12_bits (immediate : rv32_imm12) : N :=
  proj1_sig immediate.

Definition rv32_imm13_bits (immediate : rv32_imm13) : N :=
  proj1_sig immediate.

Definition rv32_imm20_bits (immediate : rv32_imm20) : N :=
  proj1_sig immediate.

Definition rv32_imm21_bits (immediate : rv32_imm21) : N :=
  proj1_sig immediate.

Inductive rv32_instruction : Type :=
| RV32_ADD (rd rs1 rs2 : rv32_register_index)
| RV32_SUB (rd rs1 rs2 : rv32_register_index)
| RV32_ADDI (rd rs1 : rv32_register_index) (immediate : rv32_imm12)
| RV32_LW (rd rs1 : rv32_register_index) (immediate : rv32_imm12)
| RV32_SW (rs1 rs2 : rv32_register_index) (immediate : rv32_imm12)
| RV32_BEQ (rs1 rs2 : rv32_register_index) (immediate : rv32_imm13)
| RV32_LUI (rd : rv32_register_index) (immediate : rv32_imm20)
| RV32_JAL (rd : rv32_register_index) (immediate : rv32_imm21)
| RV32_JALR (rd rs1 : rv32_register_index) (immediate : rv32_imm12).

Inductive rv32_instruction_format : Type :=
| RV32FormatR
| RV32FormatI
| RV32FormatS
| RV32FormatB
| RV32FormatU
| RV32FormatJ.

Definition rv32_format_of_instruction
    (instruction : rv32_instruction) : rv32_instruction_format :=
  match instruction with
  | RV32_ADD _ _ _ | RV32_SUB _ _ _ => RV32FormatR
  | RV32_ADDI _ _ _ | RV32_LW _ _ _ | RV32_JALR _ _ _ => RV32FormatI
  | RV32_SW _ _ _ => RV32FormatS
  | RV32_BEQ _ _ _ => RV32FormatB
  | RV32_LUI _ _ => RV32FormatU
  | RV32_JAL _ _ => RV32FormatJ
  end.

Theorem rv32_subset_covers_six_formats :
  forall instruction,
    match rv32_format_of_instruction instruction with
    | RV32FormatR
    | RV32FormatI
    | RV32FormatS
    | RV32FormatB
    | RV32FormatU
    | RV32FormatJ => True
    end.
Proof.
  intros instruction.
  destruct instruction; exact I.
Qed.
