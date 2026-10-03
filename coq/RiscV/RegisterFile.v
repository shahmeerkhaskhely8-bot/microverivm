(* RV32I register file: x0 is immutable and x1-x31 are writable. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import Lia.
From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Vectors.Vector.
From MicroVeriVM Require Import RiscV.Word.

Definition rv32_writable_registers := Vector.t rv32_word 31.

Definition rv32_register_file := rv32_writable_registers.

Inductive rv32_register_index : Type :=
| RV32X0
| RV32WritableIndex (index : Fin.t 31).

Definition rv32_register_index_number
    (index : rv32_register_index) : nat :=
  match index with
  | RV32X0 => 0
  | RV32WritableIndex writable_index =>
      S (proj1_sig (Fin.to_nat writable_index))
  end.

Definition rv32_read_register
    (registers : rv32_register_file)
    (index : rv32_register_index) : rv32_word :=
  match index with
  | RV32X0 => rv32_word_zero
  | RV32WritableIndex writable_index =>
      Vector.nth registers writable_index
  end.

Definition rv32_write_register
    (registers : rv32_register_file)
    (index : rv32_register_index)
    (value : rv32_word) : rv32_register_file :=
  match index with
  | RV32X0 => registers
  | RV32WritableIndex writable_index =>
      Vector.replace registers writable_index value
  end.

Theorem rv32_register_index_in_range :
  forall index : rv32_register_index,
    0 <= rv32_register_index_number index <= 31.
Proof.
  intros index.
  destruct index as [|writable_index].
  - simpl. lia.
  - simpl.
    change
      (0 <= S (proj1_sig (Fin.to_nat writable_index)) <= 31).
    pose proof (proj2_sig (Fin.to_nat writable_index)) as Hindex_bound.
    change (proj1_sig (Fin.to_nat writable_index) < 31) in Hindex_bound.
    lia.
Qed.

Theorem rv32_x0_reads_zero :
  forall registers,
    rv32_read_register registers RV32X0 = rv32_word_zero.
Proof.
  reflexivity.
Qed.

Theorem rv32_write_x0_is_immutable :
  forall registers value,
    rv32_write_register registers RV32X0 value = registers.
Proof.
  reflexivity.
Qed.

Theorem rv32_x0_remains_zero_after_any_write :
  forall registers index value,
    rv32_read_register
      (rv32_write_register registers index value) RV32X0 =
      rv32_word_zero.
Proof.
  intros registers [|writable_index] value; reflexivity.
Qed.
