(* RV32I architectural PC and machine state. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Vectors.Vector.
From MicroVeriVM Require Import RiscV.Word.
From MicroVeriVM Require Import RiscV.RegisterFile.

Definition rv32_instruction_alignment : N := 4.

Definition rv32_pc_aligned (pc : rv32_word) : Prop :=
  N.modulo (rv32_word_value pc) rv32_instruction_alignment = 0.

Definition rv32_pc := { pc : rv32_word | rv32_pc_aligned pc }.

Definition rv32_pc_zero : rv32_pc.
Proof.
  refine (exist _ rv32_word_zero _).
  unfold rv32_pc_aligned, rv32_instruction_alignment.
  vm_compute.
  reflexivity.
Defined.

Definition rv32_pc_word (pc : rv32_pc) : rv32_word :=
  proj1_sig pc.

Theorem rv32_pc_alignment_holds :
  forall pc : rv32_pc,
    rv32_pc_aligned (rv32_pc_word pc).
Proof.
  intros [pc Haligned].
  exact Haligned.
Qed.

Inductive machine_status : Type :=
| MachineRunning
| MachineHalted
| MachineTrapped.

Record rv321_state : Type := {
  rv321_pc : rv32_pc;
  rv321_registers : rv32_register_file;
  rv321_status : machine_status
}.

Definition rv32i_state := rv321_state.

Definition rv32_zero_register_file : rv32_register_file :=
  Vector.const rv32_word_zero 31.

Definition rv321_initial_state : rv321_state :=
  {| rv321_pc := rv32_pc_zero;
     rv321_registers := rv32_zero_register_file;
     rv321_status := MachineRunning |}.

Theorem rv321_state_pc_is_aligned :
  forall state,
    rv32_pc_aligned (rv32_pc_word (rv321_pc state)).
Proof.
  intros [pc registers status].
  apply rv32_pc_alignment_holds.
Qed.
