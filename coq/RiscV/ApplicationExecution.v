(* Application-level execution and safety integration for RV32I images. *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import RiscV.Machine.
From MicroVeriVM Require Import RiscV.Semantics.
From MicroVeriVM Require Import RiscV.Execution.
From MicroVeriVM Require Import RiscV.SystemIntegration.
From MicroVeriVM Require Import RiscV.TrapHandling.
From MicroVeriVM Require Import RiscV.RetirementTrace.

Import ListNotations.

Record rv32_application_execution : Type := {
  rv32_application_plain_result : rv32_execution_state;
  rv32_application_trap_result : rv32_system_state;
  rv32_application_trace_result : rv32_pc_tracked_machine
}.

Definition rv32_execute_application
    (image : rv32_binary_image)
    (trap_vector : rv32_pc)
    (fuel : nat) : rv32_application_execution :=
  {| rv32_application_plain_result :=
       rv32_run_application image fuel;
     rv32_application_trap_result :=
       rv32_run_application_with_traps image trap_vector fuel;
     rv32_application_trace_result :=
       rv32_run_application_with_pc_trace image trap_vector fuel |}.

Definition rv32_application_execution_safe
    (execution : rv32_application_execution) : Prop :=
  rv32_execution_invariant (rv32_application_plain_result execution) /\
  rv32_system_invariant (rv32_application_trap_result execution) /\
  rv32_pc_tracking_invariant (rv32_application_trace_result execution).

Theorem rv32_execute_application_preserves_safety :
  forall image trap_vector fuel,
    rv32_application_execution_safe
      (rv32_execute_application image trap_vector fuel).
Proof.
  intros image trap_vector fuel.
  unfold rv32_application_execution_safe, rv32_execute_application.
  simpl.
  split.
  - apply rv32_run_application_preserves_safety.
  - split.
    + apply rv32_run_application_with_traps_is_safe.
    + apply rv32_run_application_with_pc_trace_is_safe.
Qed.

Theorem rv32_application_traces_preserve_safety :
  forall image trap_vector plain_count trap_count trace_count
    plain_final trap_final trace_final,
    rv32_program_steps_n (rv32_load_binary_text image) plain_count
      (rv32_start_application image) plain_final ->
    rv32_system_steps_n (rv32_load_binary_text image) trap_vector trap_count
      (rv32_system_initial_state (rv32_binary_data_words image)) trap_final ->
    rv32_pc_tracked_steps_n (rv32_load_binary_text image) trace_count
      (rv32_pc_tracked_application_initial image trap_vector) trace_final ->
    rv32_execution_invariant (rv32_start_application image) ->
    rv32_system_invariant
      (rv32_system_initial_state (rv32_binary_data_words image)) ->
    rv32_pc_tracking_invariant
      (rv32_pc_tracked_application_initial image trap_vector) ->
    rv32_execution_invariant plain_final /\
    rv32_system_invariant trap_final /\
    rv32_pc_tracking_invariant trace_final.
Proof.
  intros image trap_vector plain_count trap_count trace_count
    plain_final trap_final trace_final Hplain Htrap Htrace
    Hplain_safe Htrap_safe Htrace_safe.
  split.
  - eapply rv32_program_steps_preserves_execution_invariant.
    + eapply rv32_program_steps_n_is_reflexive_transitive.
      exact Hplain.
    + exact Hplain_safe.
  - split.
    + eapply rv32_system_steps_n_preserves_safety; eassumption.
    + eapply rv32_pc_tracked_steps_n_preserves_invariant; eassumption.
Qed.

Theorem rv32_execute_application_has_bounded_traces :
  forall image trap_vector fuel,
    exists plain_count trap_count trace_count,
      (plain_count <= fuel)%nat /\
      rv32_program_steps_n (rv32_load_binary_text image) plain_count
        (rv32_start_application image)
        (rv32_application_plain_result
          (rv32_execute_application image trap_vector fuel)) /\
      (trap_count <= fuel)%nat /\
      rv32_system_steps_n (rv32_load_binary_text image) trap_vector
        trap_count
        (rv32_system_initial_state (rv32_binary_data_words image))
        (rv32_application_trap_result
          (rv32_execute_application image trap_vector fuel)) /\
      (trace_count <= fuel)%nat /\
      rv32_pc_tracked_steps_n (rv32_load_binary_text image) trace_count
        (rv32_pc_tracked_application_initial image trap_vector)
        (rv32_application_trace_result
          (rv32_execute_application image trap_vector fuel)).
Proof.
  intros image trap_vector fuel.
  destruct (rv32_run_application_has_bounded_exact_trace image fuel)
    as [plain_count [Hplain_bound Hplain_trace]].
  destruct
    (rv32_run_application_with_traps_has_bounded_trace
      image trap_vector fuel)
    as [trap_count [Htrap_bound Htrap_trace]].
  destruct
    (rv32_run_application_with_pc_trace_has_bounded_steps
      image trap_vector fuel)
    as [trace_count [Htrace_bound Htrace]].
  exists plain_count, trap_count, trace_count.
  unfold rv32_execute_application.
  simpl.
  repeat split; assumption.
Qed.

Theorem rv32_execute_application_event_count_is_bounded :
  forall image trap_vector fuel,
    (length (rv32_pc_event_trace
      (rv32_application_trace_result
        (rv32_execute_application image trap_vector fuel))) <= fuel)%nat.
Proof.
  intros image trap_vector fuel.
  unfold rv32_execute_application.
  simpl.
  apply rv32_run_application_with_pc_trace_event_bound.
Qed.

Theorem rv32_application_exact_traces_are_deterministic :
  forall image trap_vector plain_count trap_count trace_count
    plain_final1 plain_final2 trap_final1 trap_final2
    trace_final1 trace_final2,
    rv32_program_steps_n (rv32_load_binary_text image) plain_count
      (rv32_start_application image) plain_final1 ->
    rv32_program_steps_n (rv32_load_binary_text image) plain_count
      (rv32_start_application image) plain_final2 ->
    rv32_system_steps_n (rv32_load_binary_text image) trap_vector trap_count
      (rv32_system_initial_state (rv32_binary_data_words image)) trap_final1 ->
    rv32_system_steps_n (rv32_load_binary_text image) trap_vector trap_count
      (rv32_system_initial_state (rv32_binary_data_words image)) trap_final2 ->
    rv32_pc_tracked_steps_n (rv32_load_binary_text image) trace_count
      (rv32_pc_tracked_application_initial image trap_vector) trace_final1 ->
    rv32_pc_tracked_steps_n (rv32_load_binary_text image) trace_count
      (rv32_pc_tracked_application_initial image trap_vector) trace_final2 ->
    plain_final1 = plain_final2 /\
    trap_final1 = trap_final2 /\
    trace_final1 = trace_final2.
Proof.
  intros image trap_vector plain_count trap_count trace_count
    plain_final1 plain_final2 trap_final1 trap_final2 trace_final1 trace_final2
    Hplain1 Hplain2 Htrap1 Htrap2 Htrace1 Htrace2.
  split.
  - eapply rv32_program_steps_n_deterministic; eassumption.
  - split.
    + eapply rv32_system_steps_n_deterministic; eassumption.
    + eapply rv32_pc_tracked_steps_n_deterministic; eassumption.
Qed.
