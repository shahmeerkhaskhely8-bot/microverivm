(* Memory bounds, preservation, and non-interference for RV32I steps. *)

From Stdlib Require Import List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import RiscV.Word.
From MicroVeriVM Require Import RiscV.RegisterFile.
From MicroVeriVM Require Import RiscV.Machine.
From MicroVeriVM Require Import RiscV.Instruction.
From MicroVeriVM Require Import RiscV.Decoder.
From MicroVeriVM Require Import RiscV.Semantics.

Import ListNotations.
Open Scope N_scope.

Theorem rv32_register_read_is_a_valid_word :
  forall registers index,
    rv32_word_value (rv32_read_register registers index) < rv32_modulus.
Proof.
  intros registers index.
  apply rv32_word_range.
Qed.

Theorem rv32_memory_words_are_valid :
  forall memory value,
    In value memory ->
    rv32_word_value value < rv32_modulus.
Proof.
  intros memory value Hin.
  apply rv32_word_range.
Qed.

Theorem rv32_memory_store_nth_error_at_index :
  forall index value memory updated,
    rv32_memory_store index value memory = Some updated ->
    nth_error updated index = Some value.
Proof.
  induction index as [|index IH]; intros value memory updated Hstore;
    destruct memory as [|head tail]; simpl in Hstore; try discriminate.
  - inversion Hstore.
    reflexivity.
  - destruct (rv32_memory_store index value tail) as [updated_tail|]
      eqn:Htail; try discriminate.
    inversion Hstore.
    simpl.
    eapply IH.
    exact Htail.
Qed.

Theorem rv32_memory_store_nth_error_unchanged_other :
  forall index value memory updated other,
    rv32_memory_store index value memory = Some updated ->
    other <> index ->
    nth_error updated other = nth_error memory other.
Proof.
  induction index as [|index IH];
    intros value memory updated other Hstore Hother;
    destruct memory as [|head tail]; simpl in Hstore; try discriminate.
  - destruct other as [|other].
    + lia.
    + inversion Hstore.
      reflexivity.
  - destruct (rv32_memory_store index value tail) as [updated_tail|]
      eqn:Htail; try discriminate.
    inversion Hstore.
    destruct other as [|other].
    + reflexivity.
    + simpl.
      eapply IH.
      * exact Htail.
      * intros Hequal.
        apply Hother.
        now f_equal.
Qed.

Theorem rv32_memory_store_word_nth_error_at_address :
  forall memory address value updated,
    rv32_memory_store_word memory address value = Some updated ->
    nth_error updated
      (N.to_nat (N.div (rv32_word_value address) 4)) = Some value.
Proof.
  intros memory address value updated Hstore.
  unfold rv32_memory_store_word in Hstore.
  destruct (N.eqb (N.modulo (rv32_word_value address) 4) 0);
    try discriminate.
  eapply rv32_memory_store_nth_error_at_index.
  exact Hstore.
Qed.

Theorem rv32_memory_store_word_nth_error_unchanged_other :
  forall memory address value updated other,
    rv32_memory_store_word memory address value = Some updated ->
    other <> N.to_nat (N.div (rv32_word_value address) 4) ->
    nth_error updated other = nth_error memory other.
Proof.
  intros memory address value updated other Hstore Hother.
  unfold rv32_memory_store_word in Hstore.
  destruct (N.eqb (N.modulo (rv32_word_value address) 4) 0);
    try discriminate.
  eapply rv32_memory_store_nth_error_unchanged_other.
  - exact Hstore.
  - exact Hother.
Qed.

Theorem rv32_memory_store_preserves_out_of_bounds :
  forall index value memory updated other,
    rv32_memory_store index value memory = Some updated ->
    (length memory <= other)%nat ->
    nth_error updated other = None.
Proof.
  intros index value memory updated other Hstore Hout.
  apply (proj2 (nth_error_None updated other)).
  rewrite (rv32_memory_store_preserves_length
    index value memory updated Hstore).
  exact Hout.
Qed.

Theorem rv32_memory_store_word_preserves_out_of_bounds :
  forall memory address value updated other,
    rv32_memory_store_word memory address value = Some updated ->
    (length memory <= other)%nat ->
    nth_error updated other = None.
Proof.
  intros memory address value updated other Hstore Hout.
  eapply rv32_memory_store_preserves_out_of_bounds.
  - unfold rv32_memory_store_word in Hstore.
    destruct (N.eqb (N.modulo (rv32_word_value address) 4) 0);
      try discriminate.
    exact Hstore.
  - exact Hout.
Qed.

Theorem rv32_memory_success_requires_aligned_in_bounds_address :
  forall memory address value,
    rv32_memory_load memory address = Some value ->
    rv32_memory_address_valid memory address.
Proof.
  apply rv32_memory_load_success_is_in_bounds.
Qed.

Theorem rv32_memory_store_success_requires_aligned_in_bounds_address :
  forall memory address value updated,
    rv32_memory_store_word memory address value = Some updated ->
    rv32_memory_address_valid memory address.
Proof.
  apply rv32_memory_store_success_is_valid.
Qed.

Theorem rv32_lw_step_preserves_memory :
  forall state rd rs1 immediate,
    rv321_status (rv32_core_state state) = MachineRunning ->
    rv32_memory_load
      (rv32_data_memory state)
      (rv32_effective_address
        (rv32_read_register
          (rv321_registers (rv32_core_state state)) rs1)
        immediate) <> None ->
    rv32_data_memory
      (rv32_step_state (RV32_LW rd rs1 immediate) state) =
    rv32_data_memory state.
Proof.
  intros [core memory] rd rs1 immediate Hrunning Hload.
  destruct core as [pc registers status].
  simpl in *.
  unfold rv32_step_state.
  simpl.
  rewrite Hrunning.
  unfold rv32_step_running.
  simpl.
  destruct
    (rv32_memory_load memory
      (rv32_effective_address
        (rv32_read_register registers rs1) immediate))
    as [loaded|] eqn:Hloaded.
  - reflexivity.
  - contradiction.
Qed.

Theorem rv32_sw_step_preserves_other_memory_locations :
  forall state rs1 rs2 immediate updated other,
    rv321_status (rv32_core_state state) = MachineRunning ->
    rv32_memory_store_word
      (rv32_data_memory state)
      (rv32_effective_address
        (rv32_read_register
          (rv321_registers (rv32_core_state state)) rs1)
        immediate)
      (rv32_read_register
        (rv321_registers (rv32_core_state state)) rs2) =
      Some updated ->
    other <>
      N.to_nat
        (N.div
          (rv32_word_value
            (rv32_effective_address
              (rv32_read_register
                (rv321_registers (rv32_core_state state)) rs1)
              immediate))
          4) ->
    nth_error
      (rv32_data_memory
        (rv32_step_state (RV32_SW rs1 rs2 immediate) state))
      other =
    nth_error (rv32_data_memory state) other.
Proof.
  intros [core memory] rs1 rs2 immediate updated other
    Hrunning Hstore Hother.
  destruct core as [pc registers status].
  simpl in *.
  unfold rv32_step_state.
  simpl.
  rewrite Hrunning.
  unfold rv32_step_running.
  simpl.
  rewrite Hstore.
  change (nth_error updated other = nth_error memory other).
  exact
    (rv32_memory_store_word_nth_error_unchanged_other
      memory
      (rv32_effective_address (rv32_read_register registers rs1) immediate)
      (rv32_read_register registers rs2)
      updated other Hstore Hother).
Qed.

Theorem rv32_sw_step_preserves_memory_length :
  forall state rs1 rs2 immediate,
    rv321_status (rv32_core_state state) = MachineRunning ->
    length
      (rv32_data_memory
        (rv32_step_state (RV32_SW rs1 rs2 immediate) state)) =
    length (rv32_data_memory state).
Proof.
  intros [core memory] rs1 rs2 immediate Hrunning.
  destruct core as [pc registers status].
  simpl in *.
  unfold rv32_step_state.
  simpl.
  rewrite Hrunning.
  unfold rv32_step_running.
  simpl.
  destruct
    (rv32_memory_store_word memory
      (rv32_effective_address
        (rv32_read_register registers rs1) immediate)
      (rv32_read_register registers rs2))
    as [updated|] eqn:Hstore.
  - simpl.
    eapply rv32_memory_store_word_preserves_length.
    exact Hstore.
  - reflexivity.
Qed.

Theorem rv32_lw_fault_is_atomic :
  forall state rd rs1 immediate,
    rv321_status (rv32_core_state state) = MachineRunning ->
    rv32_memory_load
      (rv32_data_memory state)
      (rv32_effective_address
        (rv32_read_register
          (rv321_registers (rv32_core_state state)) rs1)
        immediate) = None ->
    rv32_step_state (RV32_LW rd rs1 immediate) state =
      rv32_trap_state state.
Proof.
  intros [core memory] rd rs1 immediate Hrunning Hload.
  destruct core as [pc registers status].
  simpl in *.
  unfold rv32_step_state.
  simpl.
  rewrite Hrunning.
  unfold rv32_step_running.
  simpl.
  rewrite Hload.
  reflexivity.
Qed.

Theorem rv32_sw_fault_is_atomic :
  forall state rs1 rs2 immediate,
    rv321_status (rv32_core_state state) = MachineRunning ->
    rv32_memory_store_word
      (rv32_data_memory state)
      (rv32_effective_address
        (rv32_read_register
          (rv321_registers (rv32_core_state state)) rs1)
        immediate)
      (rv32_read_register
        (rv321_registers (rv32_core_state state)) rs2) = None ->
    rv32_step_state (RV32_SW rs1 rs2 immediate) state =
      rv32_trap_state state.
Proof.
  intros [core memory] rs1 rs2 immediate Hrunning Hstore.
  destruct core as [pc registers status].
  simpl in *.
  unfold rv32_step_state.
  simpl.
  rewrite Hrunning.
  unfold rv32_step_running.
  simpl.
  rewrite Hstore.
  reflexivity.
Qed.

Theorem rv32_lw_fault_preserves_registers :
  forall state rd rs1 immediate,
    rv321_status (rv32_core_state state) = MachineRunning ->
    rv32_memory_load
      (rv32_data_memory state)
      (rv32_effective_address
        (rv32_read_register
          (rv321_registers (rv32_core_state state)) rs1)
        immediate) = None ->
    rv321_registers
      (rv32_core_state (rv32_step_state (RV32_LW rd rs1 immediate) state)) =
    rv321_registers (rv32_core_state state).
Proof.
  intros state rd rs1 immediate Hrunning Hload.
  rewrite (rv32_lw_fault_is_atomic state rd rs1 immediate Hrunning Hload).
  reflexivity.
Qed.

Theorem rv32_sw_fault_preserves_registers :
  forall state rs1 rs2 immediate,
    rv321_status (rv32_core_state state) = MachineRunning ->
    rv32_memory_store_word
      (rv32_data_memory state)
      (rv32_effective_address
        (rv32_read_register
          (rv321_registers (rv32_core_state state)) rs1)
        immediate)
      (rv32_read_register
        (rv321_registers (rv32_core_state state)) rs2) = None ->
    rv321_registers
      (rv32_core_state (rv32_step_state (RV32_SW rs1 rs2 immediate) state)) =
    rv321_registers (rv32_core_state state).
Proof.
  intros state rs1 rs2 immediate Hrunning Hstore.
  rewrite
    (rv32_sw_fault_is_atomic state rs1 rs2 immediate Hrunning Hstore).
  reflexivity.
Qed.

Theorem rv32_step_state_preserves_memory_length :
  forall instruction state,
    length (rv32_data_memory (rv32_step_state instruction state)) =
    length (rv32_data_memory state).
Proof.
  intros instruction state.
  destruct state as [core memory].
  destruct core as [pc registers status].
  unfold rv32_step_state.
  destruct instruction; destruct status; simpl;
    try reflexivity;
    unfold rv32_step_running;
    simpl;
    repeat match goal with
    | |- context [rv32_memory_store_word ?memory ?address ?value] =>
        destruct (rv32_memory_store_word memory address value)
          as [updated|] eqn:Hstore
    end;
    simpl;
    try reflexivity.
  - destruct
      (rv32_memory_load memory
        (rv32_effective_address
          (rv32_read_register registers rs1) immediate));
      reflexivity.
  - eapply rv32_memory_store_word_preserves_length.
    eassumption.
  - destruct
      (rv32_word_value (rv32_read_register registers rs1) =?
       rv32_word_value (rv32_read_register registers rs2));
      [destruct (rv32_pc_offset pc (rv32_sign_extend_13 immediate))|
      ]; reflexivity.
  - destruct (rv32_pc_offset pc (rv32_sign_extend_21 immediate));
      reflexivity.
  - destruct
      (rv32_pc_from_word
        (rv32_jalr_target (rv32_read_register registers rs1)
          (rv32_sign_extend_12 immediate)));
      reflexivity.
Qed.

Theorem rv32_step_encoded_preserves_memory_length :
  forall encoding state,
    length (rv32_data_memory (rv32_step_encoded encoding state)) =
    length (rv32_data_memory state).
Proof.
  intros encoding state.
  unfold rv32_step_encoded.
  destruct (rv321_status (rv32_core_state state));
    try reflexivity.
  destruct (rv32_decode encoding) as [instruction decoded canonical
    | |]; simpl.
  - apply rv32_step_state_preserves_memory_length.
  - reflexivity.
  - reflexivity.
Qed.
