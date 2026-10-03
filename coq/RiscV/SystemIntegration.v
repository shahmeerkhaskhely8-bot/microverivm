(* System-level loading, execution, and trace guarantees for RV32I images. *)

From Stdlib Require Import List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import RiscV.Word.
From MicroVeriVM Require Import RiscV.Machine.
From MicroVeriVM Require Import RiscV.Semantics.
From MicroVeriVM Require Import RiscV.Execution.
From MicroVeriVM Require Import RiscV.TrapHandling.

Import ListNotations.
Open Scope N_scope.

Record rv32_binary_image : Type := {
  rv32_binary_text_words : list rv32_word;
  rv32_binary_data_words : rv32_memory
}.

Definition rv32_load_binary_text
    (image : rv32_binary_image) : rv32_program :=
  map rv32_word_value (rv32_binary_text_words image).

Definition rv32_start_application
    (image : rv32_binary_image) : rv32_execution_state :=
  rv32_initial_execution_state (rv32_binary_data_words image).

Definition rv32_application_step
    (image : rv32_binary_image)
    (before after : rv32_execution_state) : Prop :=
  rv32_program_step (rv32_load_binary_text image) before after.

Definition rv32_run_application
    (image : rv32_binary_image)
    (fuel : nat) : rv32_execution_state :=
  rv32_execute_n (rv32_load_binary_text image) fuel
    (rv32_start_application image).

Definition rv32_run_application_with_traps
    (image : rv32_binary_image)
    (handler_pc : rv32_pc)
    (fuel : nat) : rv32_system_state :=
  rv32_system_execute_n
    (rv32_load_binary_text image) handler_pc fuel
    (rv32_system_initial_state (rv32_binary_data_words image)).

Theorem rv32_load_binary_text_preserves_image_length :
  forall image,
    length (rv32_load_binary_text image) =
      length (rv32_binary_text_words image).
Proof.
  intros image.
  unfold rv32_load_binary_text.
  apply length_map.
Qed.

Theorem rv32_load_binary_text_words_are_32_bit :
  forall image,
    Forall (fun encoding => encoding < rv32_modulus)
      (rv32_load_binary_text image).
Proof.
  intros [text data].
  induction text as [|word text IH]; simpl.
  - constructor.
  - constructor.
    + apply rv32_word_range.
    + exact IH.
Qed.

Theorem rv32_loaded_image_fetches_first_instruction :
  forall first rest image,
    rv32_program_fetch
      (rv32_load_binary_text
        {| rv32_binary_text_words := first :: rest;
           rv32_binary_data_words := rv32_binary_data_words image |})
      (rv32_start_application image) =
    Some (rv32_word_value first).
Proof.
  intros first rest image.
  unfold rv32_program_fetch, rv32_load_binary_text,
    rv32_start_application, rv32_initial_execution_state.
  simpl.
  vm_compute.
  reflexivity.
Qed.

Theorem rv32_nonempty_application_has_initial_progress :
  forall first rest memory,
    exists next_state,
      rv32_application_step
        {| rv32_binary_text_words := first :: rest;
           rv32_binary_data_words := memory |}
        (rv32_start_application
          {| rv32_binary_text_words := first :: rest;
             rv32_binary_data_words := memory |})
        next_state.
Proof.
  intros first rest memory.
  unfold rv32_application_step.
  apply rv32_program_step_has_progress with
    (encoding := rv32_word_value first).
  - reflexivity.
  - apply rv32_loaded_image_fetches_first_instruction.
Qed.

Theorem rv32_application_initial_state_is_safe :
  forall image,
    rv32_execution_invariant (rv32_start_application image).
Proof.
  intros image.
  unfold rv32_start_application.
  apply rv32_initial_execution_state_satisfies_invariant.
  apply rv32_every_memory_is_well_formed.
Qed.

Theorem rv32_application_step_deterministic :
  forall image before after1 after2,
    rv32_application_step image before after1 ->
    rv32_application_step image before after2 ->
    after1 = after2.
Proof.
  intros image before after1 after2 Hstep1 Hstep2.
  unfold rv32_application_step in *.
  eapply rv32_program_step_deterministic; eassumption.
Qed.

Theorem rv32_application_step_preserves_safety :
  forall image before after,
    rv32_application_step image before after ->
    rv32_execution_invariant before ->
    rv32_execution_invariant after.
Proof.
  intros image before after Hstep Hsafe.
  unfold rv32_application_step in Hstep.
  eapply rv32_program_step_preserves_execution_invariant; eassumption.
Qed.

Theorem rv32_application_step_is_one_step_run :
  forall image before after encoding,
    rv321_status (rv32_core_state before) = MachineRunning ->
    rv32_program_fetch (rv32_load_binary_text image) before =
      Some encoding ->
    rv32_application_step image before after ->
    rv32_execute_n (rv32_load_binary_text image) 1 before = after.
Proof.
  intros image before after encoding Hrunning Hfetch Hstep.
  rewrite
    (rv32_execute_n_takes_step_when_instruction_is_fetched
      (rv32_load_binary_text image) 0 before encoding Hrunning Hfetch).
  simpl.
  unfold rv32_application_step, rv32_program_step in Hstep.
  destruct Hstep as [_ [fetched [Hfetched Hencoded]]].
  assert (fetched = encoding) by congruence.
  subst fetched.
  exact Hencoded.
Qed.

Theorem rv32_run_application_is_trace :
  forall image fuel,
    rv32_program_steps (rv32_load_binary_text image)
      (rv32_start_application image)
      (rv32_run_application image fuel).
Proof.
  intros image fuel.
  unfold rv32_run_application.
  apply rv32_execute_n_is_a_program_trace.
Qed.

Theorem rv32_run_application_has_bounded_exact_trace :
  forall image fuel,
    exists executed,
      (executed <= fuel)%nat /\
      rv32_program_steps_n (rv32_load_binary_text image) executed
        (rv32_start_application image) (rv32_run_application image fuel).
Proof.
  intros image fuel.
  unfold rv32_run_application.
  apply rv32_execute_n_has_bounded_exact_trace.
Qed.

Theorem rv32_run_application_preserves_safety :
  forall image fuel,
    rv32_execution_invariant (rv32_run_application image fuel).
Proof.
  intros image fuel.
  unfold rv32_run_application.
  apply rv32_bounded_execution_is_safe.
  apply rv32_every_memory_is_well_formed.
Qed.

Theorem rv32_run_application_preserves_memory_size :
  forall image fuel,
    length
      (rv32_data_memory (rv32_run_application image fuel)) =
    length (rv32_binary_data_words image).
Proof.
  intros image fuel.
  unfold rv32_run_application, rv32_start_application,
    rv32_initial_execution_state.
  apply rv32_execute_n_preserves_memory_length.
Qed.

Theorem rv32_run_application_is_functional :
  forall image fuel result1 result2,
    rv32_run_application image fuel = result1 ->
    rv32_run_application image fuel = result2 ->
    result1 = result2.
Proof.
  intros image fuel result1 result2 Hrun1 Hrun2.
  congruence.
Qed.

Theorem rv32_run_application_exact_trace_is_deterministic :
  forall image fuel initial final1 final2,
    initial = rv32_start_application image ->
    rv32_program_steps_n (rv32_load_binary_text image) fuel
      initial final1 ->
    rv32_program_steps_n (rv32_load_binary_text image) fuel
      initial final2 ->
    final1 = final2.
Proof.
  intros image fuel initial final1 final2 Hinitial Htrace1 Htrace2.
  subst initial.
  eapply rv32_program_steps_n_deterministic; eassumption.
Qed.

Theorem rv32_run_application_with_traps_is_safe :
  forall image handler_pc fuel,
    rv32_system_invariant
      (rv32_run_application_with_traps image handler_pc fuel).
Proof.
  intros image handler_pc fuel.
  unfold rv32_run_application_with_traps.
  apply rv32_system_execute_n_preserves_safety.
  unfold rv32_system_invariant, rv32_system_initial_state.
  apply rv32_initial_execution_state_satisfies_invariant.
  apply rv32_every_memory_is_well_formed.
Qed.

Theorem rv32_run_application_with_traps_has_bounded_trace :
  forall image handler_pc fuel,
    exists executed,
      (executed <= fuel)%nat /\
      rv32_system_steps_n
        (rv32_load_binary_text image) handler_pc executed
        (rv32_system_initial_state (rv32_binary_data_words image))
        (rv32_run_application_with_traps image handler_pc fuel).
Proof.
  intros image handler_pc fuel.
  unfold rv32_run_application_with_traps.
  apply rv32_system_execute_n_has_exact_trace.
Qed.

Theorem rv32_run_application_with_traps_equal_length_deterministic :
  forall image handler_pc count initial final1 final2,
    initial =
      rv32_system_initial_state (rv32_binary_data_words image) ->
    rv32_system_steps_n (rv32_load_binary_text image) handler_pc
      count initial final1 ->
    rv32_system_steps_n (rv32_load_binary_text image) handler_pc
      count initial final2 ->
    final1 = final2.
Proof.
  intros image handler_pc count initial final1 final2 Hinitial Htrace1 Htrace2.
  subst initial.
  eapply rv32_system_steps_n_deterministic; eassumption.
Qed.
