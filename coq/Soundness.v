(* MicroVeriVM Phase 11: multi-step soundness and trace correspondence. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import RustModel.
From MicroVeriVM Require Import Invariants.
From MicroVeriVM Require Import Correspondence.
From MicroVeriVM Require Import Syntax.
From MicroVeriVM Require Import Semantics.
From MicroVeriVM Require Import Equivalence.

Import ListNotations.

Definition rust_step_model
    (program : list RustInstruction) (state : RustState) : RustResult :=
  match rust_status state with
  | RustHalted => Success state
  | RustRunning =>
      match nth_error program (N.to_nat (rust_pc state)) with
      | Some instruction =>
          rust_execute_instruction (length program) instruction state
      | None => Failure RustInvalidProgramCounter state
      end
  end.

Definition coq_step
    (program : list RocqInstruction) (state : RocqState) : RocqResult :=
  match rocq_status state with
  | RocqHalted => RocqSuccess state
  | RocqRunning =>
      match nth_error program (N.to_nat (rocq_pc state)) with
      | Some instruction =>
          rocq_execute_instruction (length program) instruction state
      | None => RocqFailure RocqInvalidProgramCounter state
      end
  end.

Lemma rust_program_correspondence_length :
  forall rust_program rocq_program,
    rust_program_corresponds rust_program rocq_program ->
    length rust_program = length rocq_program.
Proof.
  intros rust_program rocq_program Hprogram.
  induction Hprogram; simpl; congruence.
Qed.

Lemma rust_program_lookup_corresponds :
  forall rust_program rocq_program index rust_instruction_value,
    rust_program_corresponds rust_program rocq_program ->
    nth_error rust_program index = Some rust_instruction_value ->
    exists rocq_instruction_value,
      nth_error rocq_program index = Some rocq_instruction_value /\
      rust_instruction_corresponds rust_instruction_value rocq_instruction_value.
Proof.
  intros rust_program rocq_program index rust_instruction_value Hprogram.
  revert index rust_instruction_value.
  induction Hprogram as
    [|rust_head rocq_head rust_tail rocq_tail Hhead Htail IH];
    intros index rust_instruction_value Hfetch.
  - destruct index; simpl in Hfetch; discriminate.
  - destruct index as [|index].
    + simpl in Hfetch.
      inversion Hfetch; subst.
      exists rocq_head.
      split; [reflexivity | exact Hhead].
    + simpl in Hfetch.
      specialize (IH index rust_instruction_value Hfetch)
        as [rocq_instruction_value [Hrocq_fetch Hcorr]].
      exists rocq_instruction_value.
      split; [simpl; exact Hrocq_fetch | exact Hcorr].
Qed.

Lemma rust_instruction_evaluators_correspond :
  forall code_length rust_instruction_value rocq_instruction_value
    rust_state rocq_state,
    rust_state_corresponds rust_state rocq_state ->
    rust_status rust_state = RustRunning ->
    rust_instruction_corresponds rust_instruction_value rocq_instruction_value ->
    rust_result_corresponds
      (rust_execute_instruction code_length rust_instruction_value rust_state)
      (rocq_execute_instruction code_length rocq_instruction_value rocq_state).
Proof.
  intros code_length rust_instruction_value rocq_instruction_value
    rust_state rocq_state Hstate Hrunning Hinstruction.
  destruct Hinstruction; eauto using
    rust_const_instruction_corresponds,
    rust_drop_instruction_corresponds,
    rust_dup_instruction_corresponds,
    rust_add_instruction_corresponds,
    rust_sub_instruction_corresponds,
    rust_load_instruction_corresponds,
    rust_store_instruction_corresponds,
    rust_jmp_instruction_corresponds,
    rust_jz_instruction_corresponds,
    rust_halt_instruction_corresponds.
Qed.

Theorem rust_step_correspondence :
  forall rust_program rocq_program rust_state rocq_state,
    rust_program_corresponds rust_program rocq_program ->
    rust_state_corresponds rust_state rocq_state ->
    rust_result_corresponds
      (rust_step_model rust_program rust_state)
      (coq_step rocq_program rocq_state).
Proof.
  intros rust_program rocq_program rust_state rocq_state Hprogram Hstate.
  destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
  destruct (rust_status rust_state) eqn:Hrust_status.
  - destruct (rocq_status rocq_state) eqn:Hrocq_status.
    + assert (Hstate_corr : rust_state_corresponds rust_state rocq_state).
      {
        unfold rust_state_corresponds, rust_stacks_correspond.
        split; [exact Hpc |].
        split; [exact Hstack |].
        split; [exact Hmemory |].
        rewrite Hrust_status, Hrocq_status.
        exact Hstatus.
      }
      unfold rust_step_model, coq_step.
      rewrite Hrust_status, Hrocq_status.
      destruct (nth_error rust_program (N.to_nat (rust_pc rust_state)))
        as [rust_instruction_value |] eqn:Hrust_fetch.
      * destruct (rust_program_lookup_corresponds rust_program rocq_program
          (N.to_nat (rust_pc rust_state)) rust_instruction_value
          Hprogram Hrust_fetch)
          as [rocq_instruction_value [Hrocq_fetch Hinstruction]].
        rewrite <- Hpc.
        rewrite Hrocq_fetch.
        rewrite (rust_program_correspondence_length
          rust_program rocq_program Hprogram).
        apply rust_instruction_evaluators_correspond.
        -- exact Hstate_corr.
        -- exact Hrust_status.
        -- exact Hinstruction.
      * assert (Hlength : length rust_program = length rocq_program).
        { apply rust_program_correspondence_length. exact Hprogram. }
        apply nth_error_None in Hrust_fetch.
        assert (Hrocq_fetch :
          nth_error rocq_program (N.to_nat (rust_pc rust_state)) = None).
        {
          apply nth_error_None.
          rewrite <- Hlength.
          exact Hrust_fetch.
        }
        rewrite <- Hpc.
        rewrite Hrocq_fetch.
        apply CorrespondFailure.
        -- constructor.
        -- exact Hstate_corr.
    + simpl in Hstatus.
      destruct Hstatus.
  - destruct (rocq_status rocq_state) eqn:Hrocq_status.
    + simpl in Hstatus.
      destruct Hstatus.
    + assert (Hstate_corr : rust_state_corresponds rust_state rocq_state).
      {
        unfold rust_state_corresponds, rust_stacks_correspond.
        split; [exact Hpc |].
        split; [exact Hstack |].
        split; [exact Hmemory |].
        rewrite Hrust_status, Hrocq_status.
        exact Hstatus.
      }
      unfold rust_step_model, coq_step.
      rewrite Hrust_status, Hrocq_status.
      apply CorrespondSuccess.
      exact Hstate_corr.
Qed.

Theorem rust_view_model_step_correspondence :
  forall rust_program rocq_program view rocq_state,
    rust_program_corresponds rust_program rocq_program ->
    rust_view_corresponds view rocq_state ->
    rust_result_corresponds
      (rust_step_model rust_program (rust_state_from_view view))
      (coq_step rocq_program rocq_state).
Proof.
  intros rust_program rocq_program view rocq_state Hprogram Hview.
  apply rust_step_correspondence.
  - exact Hprogram.
  - apply (proj1 (rust_view_corresponds_iff_projected_state view rocq_state)).
    exact Hview.
Qed.

Theorem coq_step_reflects_rust :
  forall rust_program rocq_program rust_state rocq_state rocq_result,
    rust_program_corresponds rust_program rocq_program ->
    rust_state_corresponds rust_state rocq_state ->
    rocq_result = coq_step rocq_program rocq_state ->
    exists rust_result,
      rust_result = rust_step_model rust_program rust_state /\
      rust_result_corresponds rust_result rocq_result.
Proof.
  intros rust_program rocq_program rust_state rocq_state rocq_result
    Hprogram Hstate Hresult.
  exists (rust_step_model rust_program rust_state).
  split.
  - reflexivity.
  - subst rocq_result.
    apply rust_step_correspondence; assumption.
Qed.

Inductive rust_model_multi_step
    (program : list RustInstruction) : RustState -> RustState -> Prop :=
| RustModelMultiRefl : forall state,
    rust_model_multi_step program state state
| RustModelMultiCons : forall state next finish,
    rust_step_model program state = Success next ->
    rust_model_multi_step program next finish ->
    rust_model_multi_step program state finish.

Inductive rocq_multi_step
    (program : list RocqInstruction) : RocqState -> RocqState -> Prop :=
| RocqMultiRefl : forall state,
    rocq_multi_step program state state
| RocqMultiCons : forall state next finish,
    coq_step program state = RocqSuccess next ->
    rocq_multi_step program next finish ->
    rocq_multi_step program state finish.

Lemma rust_result_success_state :
  forall rust_state rocq_result,
    rust_result_corresponds (Success rust_state) rocq_result ->
    exists rocq_state,
      rocq_result = RocqSuccess rocq_state /\
      rust_state_corresponds rust_state rocq_state.
Proof.
  intros rust_state rocq_result Hcorr.
  inversion Hcorr; subst; eexists; split; eauto.
Qed.

Lemma rust_result_rocq_success_state :
  forall rust_result rocq_state,
    rust_result_corresponds rust_result (RocqSuccess rocq_state) ->
    exists rust_state,
      rust_result = Success rust_state /\
      rust_state_corresponds rust_state rocq_state.
Proof.
  intros rust_result rocq_state Hcorr.
  inversion Hcorr; subst; eexists; split; eauto.
Qed.

Theorem multi_step_correspondence :
  forall rust_program rocq_program rust_start rust_finish rocq_start,
    rust_program_corresponds rust_program rocq_program ->
    rust_state_corresponds rust_start rocq_start ->
    rust_model_multi_step rust_program rust_start rust_finish ->
    exists rocq_finish,
      rocq_multi_step rocq_program rocq_start rocq_finish /\
      rust_state_corresponds rust_finish rocq_finish.
Proof.
  intros rust_program rocq_program rust_start rust_finish rocq_start
    Hprogram Hstart Htrace.
  revert rocq_start Hstart.
  induction Htrace as [state | state next finish Hstep Htail IH];
    intros rocq_state Hcorrespond.
  - exists rocq_state.
    split.
    + constructor.
    + exact Hcorrespond.
  - pose proof (rust_step_correspondence
      rust_program rocq_program state rocq_state Hprogram Hcorrespond) as Hstep_corr.
    rewrite Hstep in Hstep_corr.
    destruct (rust_result_success_state next
      (coq_step rocq_program rocq_state) Hstep_corr)
      as [rocq_next [Hcoq_success Hnext_corr]].
    destruct (IH rocq_next Hnext_corr) as [rocq_finish [Hrocq_trace Hend]].
    exists rocq_finish.
    split.
    + econstructor; eauto.
    + exact Hend.
Qed.

Theorem multi_step_reflects_rust :
  forall rust_program rocq_program rust_start rocq_start rocq_finish,
    rust_program_corresponds rust_program rocq_program ->
    rust_state_corresponds rust_start rocq_start ->
    rocq_multi_step rocq_program rocq_start rocq_finish ->
    exists rust_finish,
      rust_model_multi_step rust_program rust_start rust_finish /\
      rust_state_corresponds rust_finish rocq_finish.
Proof.
  intros rust_program rocq_program rust_start rocq_start rocq_finish
    Hprogram Hstart Htrace.
  revert rust_start Hstart.
  induction Htrace as [state | state next finish Hstep Htail IH];
    intros rust_state Hcorrespond.
  - exists rust_state.
    split.
    + constructor.
    + exact Hcorrespond.
  - pose proof (rust_step_correspondence
      rust_program rocq_program rust_state state Hprogram Hcorrespond) as Hstep_corr.
    rewrite Hstep in Hstep_corr.
    destruct (rust_result_rocq_success_state
      (rust_step_model rust_program rust_state) next Hstep_corr)
      as [rust_next [Hrust_success Hnext_corr]].
    destruct (IH rust_next Hnext_corr) as [rust_finish [Hrust_trace Hend]].
    exists rust_finish.
    split.
    + econstructor; eauto.
    + exact Hend.
Qed.

Theorem rust_model_trace_preserves_valid_state :
  forall program start finish,
    rust_model_multi_step program start finish ->
    valid_state finish.
Proof.
  intros program start finish _.
  unfold valid_state, valid_stack, valid_memory,
    valid_representation, rust_word_representation_valid, valid_status.
  destruct finish as [pc [stack_data stack_bound] memory status].
  simpl.
  split.
  - exact stack_bound.
  - split.
    + exists memory.
      reflexivity.
    + split.
      * split.
        -- exact (proj2_sig pc).
        -- induction stack_data as [|value rest IH].
           ++ constructor.
           ++ constructor.
              ** exact (proj2_sig value).
                ** apply IH.
                  simpl in stack_bound.
                  lia.
      * destruct status; [left | right]; reflexivity.
Qed.

(* Successful execution traces are the reflexive-transitive closure of the
   one-step relation's successful result.  Error results terminate a trace and
   are represented by the one-step [StepError] relation from Phase 8. *)
Inductive multi_step (program : code) : state -> state -> Prop :=
| MultiRefl : forall s,
    multi_step program s s
| MultiCons : forall s s' s'',
    step program s (StepOk s') ->
    multi_step program s' s'' ->
    multi_step program s s''.

(* A trace preserves the endpoint's machine shape: stack storage remains
   bounded and memory remains a fixed-size vector. *)
Theorem trace_preserves_memory_shape :
  forall program start finish,
    state_safe start ->
    multi_step program start finish ->
    memory_shaped (state_memory finish).
Proof.
  intros program start finish _ _.
  apply memory_shape_preserved.
Qed.

(* The trace invariant explicitly records that every endpoint is safe.  The
   induction principle is useful to connect one-step safety proofs to traces
   without changing the executable Rust/Coq correspondence. *)
Inductive safe_trace (program : code) : state -> state -> Prop :=
| SafeTraceRefl : forall s,
    state_safe s ->
    safe_trace program s s
| SafeTraceCons : forall s s' s'',
    state_safe s ->
    step program s (StepOk s') ->
    safe_trace program s' s'' ->
    safe_trace program s s''.

Lemma safe_trace_is_multi_step :
  forall program start finish,
    safe_trace program start finish ->
    multi_step program start finish.
Proof.
  intros program start finish Htrace.
  induction Htrace as [s Hsafe | s s' s'' Hsafe Hstep Hrest IH].
  - constructor.
  - econstructor; eauto.
Qed.

Lemma safe_trace_endpoint_safe :
  forall program start finish,
    safe_trace program start finish ->
    state_safe finish.
Proof.
  intros program start finish Htrace.
  induction Htrace as [s Hsafe | s s' s'' Hsafe Hstep Hrest IH].
  - exact Hsafe.
  - exact IH.
Qed.

(* Any trace whose successful one-step endpoints satisfy the Phase 10 safety
   invariant is a valid multi-step Coq transition and preserves that invariant
   at its final endpoint. *)
Theorem sound_safe_trace :
  forall program start finish,
    safe_trace program start finish ->
    multi_step program start finish /\ state_safe finish.
Proof.
  intros program start finish Htrace.
  split.
  - exact (safe_trace_is_multi_step program start finish Htrace).
  - exact (safe_trace_endpoint_safe program start finish Htrace).
Qed.
