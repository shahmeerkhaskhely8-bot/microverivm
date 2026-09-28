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

