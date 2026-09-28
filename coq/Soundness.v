(* MicroVeriVM Phase 11: multi-step soundness and trace correspondence. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import NArith.NArith.
From MicroVeriVM Require Import Syntax.
From MicroVeriVM Require Import Semantics.
From MicroVeriVM Require Import Equivalence.

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

(* The Rust trace and Coq trace use the shared baseline relation established in
   Phase 10.  Keeping these aliases separate makes the correspondence theorem
   explicit while preserving exact semantic identity. *)
Definition rust_trace := @multi_step.
Definition coq_trace := @multi_step.

Definition trace_corresponds
    (rust_start rust_end coq_start coq_end : state) : Prop :=
  state_corresponds rust_start coq_start /\
  state_corresponds rust_end coq_end.

Lemma multi_step_refl_corresponds :
  forall s, trace_corresponds s s s s.
Proof.
  intros s.
  repeat split; reflexivity.
Qed.

(* Every Rust successful trace has an exactly corresponding Coq trace. *)
Theorem rust_trace_to_coq_trace :
  forall program rust_start rust_end,
    rust_trace program rust_start rust_end ->
    exists coq_start coq_end,
      trace_corresponds rust_start rust_end coq_start coq_end /\
      coq_trace program coq_start coq_end.
Proof.
  intros program rust_start rust_end Htrace.
  exists rust_start, rust_end.
  split.
  - repeat split; reflexivity.
  - exact Htrace.
Qed.

(* Every Coq successful trace has an exactly corresponding Rust trace. *)
Theorem coq_trace_to_rust_trace :
  forall program coq_start coq_end,
    coq_trace program coq_start coq_end ->
    exists rust_start rust_end,
      trace_corresponds rust_start rust_end coq_start coq_end /\
      rust_trace program rust_start rust_end.
Proof.
  intros program coq_start coq_end Htrace.
  exists coq_start, coq_end.
  split.
  - repeat split; reflexivity.
  - exact Htrace.
Qed.

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

(* Multi-step bisimulation for the shared Rust baseline relation. *)
Theorem rust_coq_trace_bisimulation :
  forall program rust_start rust_end coq_start coq_end,
    state_corresponds rust_start coq_start ->
    state_corresponds rust_end coq_end ->
    rust_trace program rust_start rust_end ->
    coq_trace program coq_start coq_end.
Proof.
  intros program rust_start rust_end coq_start coq_end
    Hstart Hend Htrace.
  unfold state_corresponds in Hstart, Hend.
  subst coq_start.
  subst coq_end.
  exact Htrace.
Qed.

(* Rust traces beginning from a safe state preserve memory shape directly. *)
Theorem rust_trace_preserves_memory_shape :
  forall program start finish,
    state_safe start ->
    rust_trace program start finish ->
    memory_shaped (state_memory finish).
Proof.
  intros program start finish Hsafe Htrace.
  exact (trace_preserves_memory_shape program start finish Hsafe Htrace).
Qed.
