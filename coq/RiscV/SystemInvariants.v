(* Top-level safety, boundedness, determinism, and refinement integration. *)

From Stdlib Require Import List.
From MicroVeriVM Require Import RiscV.Machine.
From MicroVeriVM Require Import RiscV.Semantics.
From MicroVeriVM Require Import RiscV.Execution.
From MicroVeriVM Require Import RiscV.SystemIntegration.
From MicroVeriVM Require Import RiscV.TrapHandling.
From MicroVeriVM Require Import RiscV.RetirementTrace.
From MicroVeriVM Require Import RiscV.ApplicationExecution.
From MicroVeriVM Require Import RiscV.BisimulationRefinement.
From MicroVeriVM Require Import RustModel.
From MicroVeriVM Require Import Correspondence.
From MicroVeriVM Require Import Soundness.

Definition rv32_application_trace_invariant
    (image : rv32_binary_image)
    (trap_vector : rv32_pc)
    (fuel : nat) : Prop :=
  rv32_application_execution_safe
    (rv32_execute_application image trap_vector fuel) /\
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
        (rv32_execute_application image trap_vector fuel)) /\
  (length (rv32_pc_event_trace
    (rv32_application_trace_result
      (rv32_execute_application image trap_vector fuel))) <= fuel)%nat.

Theorem rv32_application_trace_invariant_holds :
  forall image trap_vector fuel,
    rv32_application_trace_invariant image trap_vector fuel.
Proof.
  intros image trap_vector fuel.
  unfold rv32_application_trace_invariant.
  split.
  - apply rv32_execute_application_preserves_safety.
  - destruct
      (rv32_execute_application_has_bounded_traces
        image trap_vector fuel)
    as [plain_count [trap_count [trace_count
      [Hplain_bound [Hplain_trace
        [Htrap_bound [Htrap_trace [Htrace_bound Htrace]]]]]]]].
    exists plain_count, trap_count, trace_count.
    split; [exact Hplain_bound|].
    split; [exact Hplain_trace|].
    split; [exact Htrap_bound|].
    split; [exact Htrap_trace|].
    split; [exact Htrace_bound|].
    split; [exact Htrace|].
    apply rv32_execute_application_event_count_is_bounded.
Qed.

Theorem rv32_application_arbitrary_trace_preserves_all_invariants :
  forall image trap_vector plain_count trap_count trace_count
    plain_final trap_final trace_final,
    rv32_program_steps_n (rv32_load_binary_text image) plain_count
      (rv32_start_application image) plain_final ->
    rv32_system_steps_n (rv32_load_binary_text image) trap_vector trap_count
      (rv32_system_initial_state (rv32_binary_data_words image)) trap_final ->
    rv32_pc_tracked_steps_n (rv32_load_binary_text image) trace_count
      (rv32_pc_tracked_application_initial image trap_vector) trace_final ->
    rv32_execution_invariant plain_final /\
    rv32_system_invariant trap_final /\
    rv32_pc_tracking_invariant trace_final.
Proof.
  intros image trap_vector plain_count trap_count trace_count
    plain_final trap_final trace_final Hplain Htrap Htrace.
  eapply rv32_application_traces_preserve_safety.
  - exact Hplain.
  - exact Htrap.
  - exact Htrace.
  - apply rv32_application_initial_state_is_safe.
  - unfold rv32_system_invariant, rv32_system_initial_state.
    apply rv32_initial_execution_state_satisfies_invariant.
    apply rv32_every_memory_is_well_formed.
  - apply rv32_pc_tracked_initial_satisfies_invariant.
Qed.

Theorem rv32_application_equal_length_runs_are_deterministic :
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
  eapply rv32_application_exact_traces_are_deterministic;
    eassumption.
Qed.

Theorem rv32_application_memory_size_is_preserved :
  forall image trap_vector fuel,
    length
      (rv32_data_memory
        (rv32_application_plain_result
          (rv32_execute_application image trap_vector fuel))) =
    length (rv32_binary_data_words image).
Proof.
  intros image trap_vector fuel.
  unfold rv32_execute_application.
  simpl.
  apply rv32_run_application_preserves_memory_size.
Qed.

Theorem rust_stack_model_has_bidirectional_trace_refinement :
  forall rust_program rust_start rocq_start,
    rust_coq_state_relation rust_start rocq_start ->
    (forall rust_finish,
      rust_model_multi_step rust_program rust_start rust_finish ->
      exists rocq_finish,
        rocq_multi_step (rocq_program_of_rust rust_program)
          rocq_start rocq_finish /\
        rust_coq_state_relation rust_finish rocq_finish) /\
    (forall rocq_finish,
      rocq_multi_step (rocq_program_of_rust rust_program)
        rocq_start rocq_finish ->
      exists rust_finish,
        rust_model_multi_step rust_program rust_start rust_finish /\
        rust_coq_state_relation rust_finish rocq_finish).
Proof.
  apply converted_program_successful_trace_bisimulation.
Qed.
