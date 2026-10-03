(* Small-step operational semantics for the modeled RV32I instruction subset. *)

From Stdlib Require Import List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import RiscV.Word.
From MicroVeriVM Require Import RiscV.RegisterFile.
From MicroVeriVM Require Import RiscV.Machine.
From MicroVeriVM Require Import RiscV.Instruction.
From MicroVeriVM Require Import RiscV.Decoder.

Set Warnings "-deprecated-syntactic-definition".

Import ListNotations.
Open Scope N_scope.

Definition rv32_memory := list rv32_word.

Record rv32_execution_state : Type := {
  rv32_core_state : rv321_state;
  rv32_data_memory : rv32_memory
}.

Definition rv32_state_with
    (state : rv32_execution_state)
    (pc : rv32_pc)
    (registers : rv32_register_file)
    (status : machine_status)
    (memory : rv32_memory) : rv32_execution_state :=
  {| rv32_core_state :=
       {| rv321_pc := pc;
          rv321_registers := registers;
          rv321_status := status |};
     rv32_data_memory := memory |}.

Definition rv32_trap_state (state : rv32_execution_state) :
    rv32_execution_state :=
  rv32_state_with state
    (rv321_pc (rv32_core_state state))
    (rv321_registers (rv32_core_state state))
    MachineTrapped
    (rv32_data_memory state).

Definition rv32_pc_from_word (word : rv32_word) : option rv32_pc :=
  match N.eq_dec
      (N.modulo (rv32_word_value word) rv32_instruction_alignment) 0 with
  | left aligned => Some (exist _ word aligned)
  | right _ => None
  end.

Definition rv32_pc_index_modulus : N := 1073741824.

Definition rv32_pc_from_index
    (index : N) (bound : index < rv32_pc_index_modulus) : rv32_pc.
Proof.
  refine (exist _ (rv32_word_wrap (index * 4)) _).
  unfold rv32_pc_aligned.
  rewrite rv32_word_wrap_small.
  - apply (proj2 (N.mod_divides (index * 4) 4 ltac:(discriminate))).
    exists index.
    replace (index * 4) with (4 * index) by nia.
    reflexivity.
  - change (index < 1073741824)%N in bound.
    unfold rv32_modulus.
    nia.
Defined.

Theorem rv32_pc_from_index_value :
  forall index bound,
    rv32_word_value
      (rv32_pc_word (rv32_pc_from_index index bound)) = index * 4.
Proof.
  intros index bound.
  unfold rv32_pc_from_index.
  cbn [rv32_pc_word rv32_word_value].
  apply rv32_word_wrap_small.
  change (index < 1073741824)%N in bound.
  unfold rv32_modulus.
  nia.
Qed.

Definition rv32_pc_advance (pc : rv32_pc) : rv32_pc :=
  let index := N.div (rv32_word_value (rv32_pc_word pc)) 4 in
  rv32_pc_from_index
    (N.modulo (index + 1) rv32_pc_index_modulus)
    (ltac:(apply N.mod_lt; discriminate)).

Theorem rv32_pc_index_modulus_times_four :
  rv32_pc_index_modulus * 4 = rv32_modulus.
Proof.
  reflexivity.
Qed.

Theorem rv32_pc_advance_is_aligned :
  forall pc,
    rv32_pc_aligned (rv32_pc_word (rv32_pc_advance pc)).
Proof.
  intros pc.
  apply rv32_pc_alignment_holds.
Qed.

Theorem rv32_pc_advance_is_modular_plus_four :
  forall pc,
    rv32_word_value (rv32_pc_word (rv32_pc_advance pc)) =
      N.modulo
        (rv32_word_value (rv32_pc_word pc) + 4)
        rv32_modulus.
Proof.
  intros [pc Hpc].
  unfold rv32_pc_advance.
  rewrite rv32_pc_from_index_value.
  change
    (N.modulo
       (N.div (rv32_word_value pc) 4 + 1)
       rv32_pc_index_modulus * 4 =
     N.modulo (rv32_word_value pc + 4) rv32_modulus).
  set (index := N.div (rv32_word_value pc) 4).
  assert (Haligned :
      N.modulo (rv32_word_value pc) 4 = 0).
  { exact Hpc. }
  assert (Hdecomp :
      rv32_word_value pc = 4 * index).
  {
    unfold index.
    pose proof
      (N.div_mod (rv32_word_value pc) 4 ltac:(discriminate)) as H.
    rewrite Haligned in H.
    nia.
  }
  assert (Hbound : index < rv32_pc_index_modulus).
  {
    pose proof (rv32_word_range pc) as Hrange.
    rewrite Hdecomp in Hrange.
    unfold rv32_modulus in Hrange.
    change (index < 1073741824)%N.
    nia.
  }
  rewrite Hdecomp.
  replace (4 * index + 4) with (4 * (index + 1)) by nia.
  replace rv32_modulus with (4 * rv32_pc_index_modulus)
    by (vm_compute; reflexivity).
  pose proof
    (N.mod_mul_r (4 * (index + 1)) 4 rv32_pc_index_modulus
      ltac:(discriminate) ltac:(discriminate)) as Hmod.
  rewrite Hmod.
  assert (Hremainder :
      N.modulo (4 * (index + 1)) 4 = 0).
  {
    replace (4 * (index + 1)) with ((index + 1) * 4) by nia.
    apply N.mod_mul.
    discriminate.
  }
  assert (Hquotient :
      N.div (4 * (index + 1)) 4 = index + 1).
  {
    replace (4 * (index + 1)) with ((index + 1) * 4) by nia.
    apply N.div_mul.
    discriminate.
  }
  rewrite Hremainder, Hquotient.
  nia.
Qed.

Definition rv32_last_aligned_pc : rv32_pc :=
  rv32_pc_from_index
    (rv32_pc_index_modulus - 1)
    (ltac:(unfold rv32_pc_index_modulus; lia)).

Theorem rv32_pc_advance_wraps_at_address_space_boundary :
  rv32_word_value
    (rv32_pc_word (rv32_pc_advance rv32_last_aligned_pc)) = 0.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition rv32_pc_offset
    (pc : rv32_pc) (offset : rv32_word) : option rv32_pc :=
  rv32_pc_from_word (rv32_add (rv32_pc_word pc) offset).

Definition rv32_jalr_target
    (base offset : rv32_word) : rv32_word :=
  rv32_word_wrap
    (N.div
      (rv32_word_value (rv32_add base offset))
      2 * 2).

Definition rv32_memory_address_valid
    (memory : rv32_memory) (address : rv32_word) : Prop :=
  N.modulo (rv32_word_value address) 4 = 0 /\
  (N.to_nat (N.div (rv32_word_value address) 4) < length memory)%nat.

Definition rv32_memory_load
    (memory : rv32_memory) (address : rv32_word) : option rv32_word :=
  if N.eqb (N.modulo (rv32_word_value address) 4) 0 then
    nth_error memory (N.to_nat (N.div (rv32_word_value address) 4))
  else None.

Fixpoint rv32_memory_store
    (index : nat) (value : rv32_word) (memory : rv32_memory)
    {struct index} : option rv32_memory :=
  match index, memory with
  | O, [] => None
  | O, _ :: tail => Some (value :: tail)
  | S previous, [] => None
  | S previous, head :: tail =>
      match rv32_memory_store previous value tail with
      | Some updated_tail => Some (head :: updated_tail)
      | None => None
      end
  end.

Theorem rv32_memory_store_preserves_length :
  forall index value memory updated,
    rv32_memory_store index value memory = Some updated ->
    length updated = length memory.
Proof.
  induction index as [|index IH]; intros value memory updated Hstore;
    destruct memory as [|head tail]; simpl in Hstore; try discriminate.
  - inversion Hstore.
    reflexivity.
  - destruct (rv32_memory_store index value tail) as [updated_tail|]
      eqn:Htail; try discriminate.
    inversion Hstore.
    simpl.
    f_equal.
    eapply IH.
    exact Htail.
Qed.

Theorem rv32_memory_store_success_is_in_bounds :
  forall index value memory updated,
    rv32_memory_store index value memory = Some updated ->
    (index < length memory)%nat.
Proof.
  induction index as [|index IH]; intros value memory updated Hstore;
    destruct memory as [|head tail]; simpl in Hstore; try discriminate.
  - simpl.
    lia.
  - destruct (rv32_memory_store index value tail) as [updated_tail|]
      eqn:Htail; try discriminate.
    inversion Hstore.
    simpl.
    specialize (IH value tail updated_tail Htail).
    lia.
Qed.

Definition rv32_memory_store_word
    (memory : rv32_memory) (address : rv32_word) (value : rv32_word) :
    option rv32_memory :=
  if N.eqb (N.modulo (rv32_word_value address) 4) 0 then
    rv32_memory_store
      (N.to_nat (N.div (rv32_word_value address) 4))
      value memory
  else None.

Theorem rv32_memory_store_word_preserves_length :
  forall memory address value updated,
    rv32_memory_store_word memory address value = Some updated ->
    length updated = length memory.
Proof.
  intros memory address value updated Hstore.
  unfold rv32_memory_store_word in Hstore.
  destruct (N.eqb (N.modulo (rv32_word_value address) 4) 0);
    try discriminate.
  eapply rv32_memory_store_preserves_length.
  exact Hstore.
Qed.

Theorem rv32_memory_load_success_is_in_bounds :
  forall memory address value,
    rv32_memory_load memory address = Some value ->
    rv32_memory_address_valid memory address.
Proof.
  intros memory address value Hload.
  unfold rv32_memory_load in Hload.
  destruct (N.eqb (N.modulo (rv32_word_value address) 4) 0)
    eqn:Haligned; try discriminate.
  apply N.eqb_eq in Haligned.
  split.
  - exact Haligned.
  - apply (proj1
      (nth_error_Some memory
        (N.to_nat (N.div (rv32_word_value address) 4)))).
    rewrite Hload.
    discriminate.
Qed.

Theorem rv32_memory_store_success_is_valid :
  forall memory address value updated,
    rv32_memory_store_word memory address value = Some updated ->
    rv32_memory_address_valid memory address.
Proof.
  intros memory address value updated Hstore.
  unfold rv32_memory_store_word in Hstore.
  destruct (N.eqb (N.modulo (rv32_word_value address) 4) 0)
    eqn:Haligned; try discriminate.
  apply N.eqb_eq in Haligned.
  split.
  - exact Haligned.
  - eapply rv32_memory_store_success_is_in_bounds.
    exact Hstore.
Qed.

Definition rv32_effective_address
    (base : rv32_word) (offset : rv32_imm12) : rv32_word :=
  rv32_add base (rv32_sign_extend_12 offset).

Definition rv32_step_running
    (instruction : rv32_instruction)
    (state : rv32_execution_state) : rv32_execution_state :=
  let core := rv32_core_state state in
  let registers := rv321_registers core in
  let pc := rv321_pc core in
  let memory := rv32_data_memory state in
  let advance :=
    fun next_registers next_memory =>
      rv32_state_with state (rv32_pc_advance pc) next_registers
        MachineRunning next_memory in
  match instruction with
  | RV32_ADD rd rs1 rs2 =>
      advance
        (rv32_write_register registers rd
          (rv32_add (rv32_read_register registers rs1)
                    (rv32_read_register registers rs2)))
        memory
  | RV32_SUB rd rs1 rs2 =>
      advance
        (rv32_write_register registers rd
          (rv32_sub (rv32_read_register registers rs1)
                    (rv32_read_register registers rs2)))
        memory
  | RV32_ADDI rd rs1 immediate =>
      advance
        (rv32_write_register registers rd
          (rv32_add (rv32_read_register registers rs1)
                    (rv32_sign_extend_12 immediate)))
        memory
  | RV32_LW rd rs1 immediate =>
      let address :=
        rv32_effective_address
          (rv32_read_register registers rs1) immediate in
      match rv32_memory_load memory address with
      | Some value =>
          advance (rv32_write_register registers rd value) memory
      | None => rv32_trap_state state
      end
  | RV32_SW rs1 rs2 immediate =>
      let address :=
        rv32_effective_address
          (rv32_read_register registers rs1) immediate in
      match rv32_memory_store_word memory address
          (rv32_read_register registers rs2) with
      | Some updated_memory => advance registers updated_memory
      | None => rv32_trap_state state
      end
  | RV32_BEQ rs1 rs2 immediate =>
      if rv32_word_value (rv32_read_register registers rs1) =?
         rv32_word_value (rv32_read_register registers rs2) then
        match rv32_pc_offset pc (rv32_sign_extend_13 immediate) with
        | Some target =>
            rv32_state_with state target registers MachineRunning memory
        | None => rv32_trap_state state
        end
      else advance registers memory
  | RV32_LUI rd immediate =>
      advance
        (rv32_write_register registers rd
          (rv32_word_wrap (rv32_imm20_bits immediate * 4096)))
        memory
  | RV32_JAL rd immediate =>
      match rv32_pc_offset pc (rv32_sign_extend_21 immediate) with
      | Some target =>
          let return_pc := rv32_pc_advance pc in
          rv32_state_with state target
            (rv32_write_register registers rd (rv32_pc_word return_pc))
            MachineRunning memory
      | None => rv32_trap_state state
      end
  | RV32_JALR rd rs1 immediate =>
      let target_word :=
        rv32_jalr_target
          (rv32_read_register registers rs1)
          (rv32_sign_extend_12 immediate) in
      match rv32_pc_from_word target_word with
      | Some target =>
          let return_pc := rv32_pc_advance pc in
          rv32_state_with state target
            (rv32_write_register registers rd (rv32_pc_word return_pc))
            MachineRunning memory
      | None => rv32_trap_state state
      end
  end.

Definition rv32_step_state
    (instruction : rv32_instruction)
    (state : rv32_execution_state) : rv32_execution_state :=
  match rv321_status (rv32_core_state state) with
  | MachineRunning => rv32_step_running instruction state
  | MachineHalted | MachineTrapped => state
  end.

Definition rv32_step_encoded
    (encoding : N) (state : rv32_execution_state) : rv32_execution_state :=
  match rv321_status (rv32_core_state state) with
  | MachineRunning =>
      match rv32_decode encoding with
      | RV32Decoded instruction _ _ => rv32_step_state instruction state
      | RV32IllegalEncoding | RV32UnsupportedEncoding =>
          rv32_trap_state state
      end
  | MachineHalted | MachineTrapped => state
  end.

Definition rv32_step_rel
    (instruction : rv32_instruction)
    (before after : rv32_execution_state) : Prop :=
  rv32_step_state instruction before = after.

Definition rv32_step_encoded_rel
    (encoding : N)
    (before after : rv32_execution_state) : Prop :=
  rv32_step_encoded encoding before = after.

Theorem rv32_pc_from_word_aligned :
  forall word pc,
    rv32_pc_from_word word = Some pc ->
    rv32_pc_word pc = word.
Proof.
  intros word pc Hpc.
  unfold rv32_pc_from_word in Hpc.
  destruct
    (N.eq_dec
      (N.modulo (rv32_word_value word) rv32_instruction_alignment) 0);
    inversion Hpc; reflexivity.
Qed.

Theorem rv32_memory_load_rejects_misaligned_address :
  forall memory address,
    N.modulo (rv32_word_value address) 4 <> 0 ->
    rv32_memory_load memory address = None.
Proof.
  intros memory address Hmisaligned.
  unfold rv32_memory_load.
  assert (N.eqb (N.modulo (rv32_word_value address) 4) 0 = false)
    as Htest.
  { apply N.eqb_neq. exact Hmisaligned. }
  rewrite Htest.
  reflexivity.
Qed.

Theorem rv32_memory_store_rejects_misaligned_address :
  forall memory address value,
    N.modulo (rv32_word_value address) 4 <> 0 ->
    rv32_memory_store_word memory address value = None.
Proof.
  intros memory address value Hmisaligned.
  unfold rv32_memory_store_word.
  assert (N.eqb (N.modulo (rv32_word_value address) 4) 0 = false)
    as Htest.
  { apply N.eqb_neq. exact Hmisaligned. }
  rewrite Htest.
  reflexivity.
Qed.

Theorem rv32_step_rel_deterministic :
  forall instruction before after1 after2,
    rv32_step_rel instruction before after1 ->
    rv32_step_rel instruction before after2 ->
    after1 = after2.
Proof.
  intros instruction before after1 after2 Hstep1 Hstep2.
  unfold rv32_step_rel in *.
  congruence.
Qed.

Theorem rv32_step_encoded_rel_deterministic :
  forall encoding before after1 after2,
    rv32_step_encoded_rel encoding before after1 ->
    rv32_step_encoded_rel encoding before after2 ->
    after1 = after2.
Proof.
  intros encoding before after1 after2 Hstep1 Hstep2.
  unfold rv32_step_encoded_rel in *.
  congruence.
Qed.

Theorem rv32_step_state_preserves_pc_alignment :
  forall instruction state,
    rv32_pc_aligned
      (rv32_pc_word
        (rv321_pc (rv32_core_state
          (rv32_step_state instruction state)))).
Proof.
  intros instruction state.
  apply rv321_state_pc_is_aligned.
Qed.

Theorem rv32_step_state_preserves_x0 :
  forall instruction state,
    rv32_read_register
      (rv321_registers
        (rv32_core_state (rv32_step_state instruction state)))
      RV32X0 = rv32_word_zero.
Proof.
  intros instruction state.
  apply rv32_x0_reads_zero.
Qed.

Theorem rv32_step_encoded_preserves_pc_alignment :
  forall encoding state,
    rv32_pc_aligned
      (rv32_pc_word
        (rv321_pc (rv32_core_state
          (rv32_step_encoded encoding state)))).
Proof.
  intros encoding state.
  apply rv321_state_pc_is_aligned.
Qed.

Theorem rv32_step_encoded_preserves_x0 :
  forall encoding state,
    rv32_read_register
      (rv321_registers
        (rv32_core_state (rv32_step_encoded encoding state)))
      RV32X0 = rv32_word_zero.
Proof.
  intros encoding state.
  apply rv32_x0_reads_zero.
Qed.

Theorem rv32_step_state_preserves_x0_after_any_write :
  forall registers index value,
    rv32_read_register (rv32_write_register registers index value) RV32X0 =
      rv32_word_zero.
Proof.
  apply rv32_x0_remains_zero_after_any_write.
Qed.

Theorem rv32_step_encoded_traps_illegal_encoding :
  forall encoding state,
    rv321_status (rv32_core_state state) = MachineRunning ->
    rv32_decode encoding = RV32IllegalEncoding ->
    rv321_status
      (rv32_core_state (rv32_step_encoded encoding state)) = MachineTrapped.
Proof.
  intros encoding state Hrunning Hdecode.
  unfold rv32_step_encoded.
  rewrite Hrunning, Hdecode.
  reflexivity.
Qed.

Theorem rv32_step_encoded_traps_unsupported_encoding :
  forall encoding state,
    rv321_status (rv32_core_state state) = MachineRunning ->
    rv32_decode encoding = RV32UnsupportedEncoding ->
    rv321_status
      (rv32_core_state (rv32_step_encoded encoding state)) = MachineTrapped.
Proof.
  intros encoding state Hrunning Hdecode.
  unfold rv32_step_encoded.
  rewrite Hrunning, Hdecode.
  reflexivity.
Qed.

Theorem rv32_step_encoded_preserves_pc_on_decode_trap :
  forall encoding state,
    rv321_status (rv32_core_state state) = MachineRunning ->
    (rv32_decode encoding = RV32IllegalEncoding \/
     rv32_decode encoding = RV32UnsupportedEncoding) ->
    rv321_pc (rv32_core_state (rv32_step_encoded encoding state)) =
      rv321_pc (rv32_core_state state).
Proof.
  intros encoding state Hrunning [Hdecode | Hdecode];
    unfold rv32_step_encoded;
    rewrite Hrunning, Hdecode;
    reflexivity.
Qed.

Theorem rv32_step_encoded_preserves_memory_on_decode_trap :
  forall encoding state,
    rv321_status (rv32_core_state state) = MachineRunning ->
    (rv32_decode encoding = RV32IllegalEncoding \/
     rv32_decode encoding = RV32UnsupportedEncoding) ->
    rv32_data_memory (rv32_step_encoded encoding state) =
      rv32_data_memory state.
Proof.
  intros encoding state Hrunning [Hdecode | Hdecode];
    unfold rv32_step_encoded;
    rewrite Hrunning, Hdecode;
    reflexivity.
Qed.
