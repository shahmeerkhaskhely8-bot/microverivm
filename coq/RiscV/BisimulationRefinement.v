(* Lockstep and trace refinement for the Coq model of the Rust stack VM.
   The current Rust source implements this stack VM, not the separate RV32I
   model; this module therefore does not claim source-level Rust verification. *)

From Stdlib Require Import Lists.List.
From MicroVeriVM Require Import RustModel.
From MicroVeriVM Require Import Correspondence.
From MicroVeriVM Require Import Soundness.

Import ListNotations.

Definition rust_coq_state_relation :=
  rust_state_corresponds.

Definition rust_coq_instruction_relation :=
  rust_instruction_corresponds.

Definition rust_coq_program_relation :=
  rust_program_corresponds.

Theorem rust_state_has_formal_representation :
  forall rust_state,
    exists rocq_state,
      rust_coq_state_relation rust_state rocq_state.
Proof.
  intros rust_state.
  exists (rocq_state_of_rust rust_state).
  apply rust_state_corresponds_to_rocq_state_of_rust.
Qed.

Definition rocq_program_of_rust
    (program : list RustInstruction) : list RocqInstruction :=
  List.map rocq_instruction_of_rust program.

Theorem rust_program_has_formal_representation :
  forall program,
    rust_coq_program_relation program (rocq_program_of_rust program).
Proof.
  intros program.
  induction program as [|instruction rest IH].
  - constructor.
  - simpl.
    constructor.
    + apply rust_instruction_corresponds_to_conversion.
    + exact IH.
Qed.

Theorem rust_coq_step_forward_simulation :
  forall rust_program rocq_program rust_state rocq_state,
    rust_coq_program_relation rust_program rocq_program ->
    rust_coq_state_relation rust_state rocq_state ->
    rust_result_corresponds
      (rust_step_model rust_program rust_state)
      (coq_step rocq_program rocq_state).
Proof.
  exact rust_step_correspondence.
Qed.

Theorem rust_coq_step_backward_simulation :
  forall rust_program rocq_program rust_state rocq_state rocq_result,
    rust_coq_program_relation rust_program rocq_program ->
    rust_coq_state_relation rust_state rocq_state ->
    rocq_result = coq_step rocq_program rocq_state ->
    exists rust_result,
      rust_result = rust_step_model rust_program rust_state /\
      rust_result_corresponds rust_result rocq_result.
Proof.
  exact coq_step_reflects_rust.
Qed.

Theorem rust_coq_successful_trace_bisimulation :
  forall rust_program rocq_program rust_start rocq_start,
    rust_coq_program_relation rust_program rocq_program ->
    rust_coq_state_relation rust_start rocq_start ->
    (forall rust_finish,
      rust_model_multi_step rust_program rust_start rust_finish ->
      exists rocq_finish,
        rocq_multi_step rocq_program rocq_start rocq_finish /\
        rust_coq_state_relation rust_finish rocq_finish) /\
    (forall rocq_finish,
      rocq_multi_step rocq_program rocq_start rocq_finish ->
      exists rust_finish,
        rust_model_multi_step rust_program rust_start rust_finish /\
        rust_coq_state_relation rust_finish rocq_finish).
Proof.
  intros rust_program rocq_program rust_start rocq_start
    Hprogram Hstart.
  split.
  - intros rust_finish Htrace.
    eapply multi_step_correspondence; eassumption.
  - intros rocq_finish Htrace.
    eapply multi_step_reflects_rust; eassumption.
Qed.

Theorem converted_program_successful_trace_bisimulation :
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
  intros rust_program rust_start rocq_start Hstart.
  apply rust_coq_successful_trace_bisimulation.
  - apply rust_program_has_formal_representation.
  - exact Hstart.
Qed.
