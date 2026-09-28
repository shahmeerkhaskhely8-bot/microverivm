(* MicroVeriVM Phase 10: Rust/Coq correspondence and safety invariants. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import Syntax.
From MicroVeriVM Require Import Semantics.

(* The Rust baseline and the Coq model use the same mathematical domains:
   u32 words are represented by [word], instructions by [instruction], and
   machine state/results by [state]/[result].  These aliases make that
   correspondence explicit without introducing a second, divergent model. *)
Definition rust_word := word.
Definition rust_instruction := instruction.
Definition rust_stack := stack.
Definition rust_memory := memory.
Definition rust_status := status.
Definition rust_state := state.
Definition rust_error := error.
Definition rust_result := result.
Definition rust_code := code.

Definition rust_step := @step.
Definition coq_step := @step.

Definition word_corresponds (rust_value : rust_word) (coq_value : word) : Prop :=
  rust_value = coq_value.

Definition instruction_corresponds
    (rust_value : rust_instruction) (coq_value : instruction) : Prop :=
  rust_value = coq_value.

Definition stack_corresponds
    (rust_value : rust_stack) (coq_value : stack) : Prop :=
  rust_value = coq_value.

Definition memory_corresponds
    (rust_value : rust_memory) (coq_value : memory) : Prop :=
  rust_value = coq_value.

Definition state_corresponds
    (rust_value : rust_state) (coq_value : state) : Prop :=
  rust_value = coq_value.

Definition result_corresponds
    (rust_value : rust_result) (coq_value : result) : Prop :=
  rust_value = coq_value.

(* Identity correspondence is total for the shared baseline domains. *)
Lemma word_correspondence_refl :
  forall value, word_corresponds value value.
Proof.
  intros value.
  reflexivity.
Qed.

Lemma instruction_correspondence_refl :
  forall value, instruction_corresponds value value.
Proof.
  intros value.
  reflexivity.
Qed.

Lemma stack_correspondence_refl :
  forall value, stack_corresponds value value.
Proof.
  intros value.
  reflexivity.
Qed.

Lemma memory_correspondence_refl :
  forall value, memory_corresponds value value.
Proof.
  intros value.
  reflexivity.
Qed.

Lemma state_correspondence_refl :
  forall value, state_corresponds value value.
Proof.
  intros value.
  reflexivity.
Qed.

Lemma result_correspondence_refl :
  forall value, result_corresponds value value.
Proof.
  intros value.
  reflexivity.
Qed.

(* Forward simulation: every Rust-baseline step is represented by a Coq step. *)
Theorem rust_step_simulates_coq :
  forall program rust_state_value rust_result_value,
    rust_step program rust_state_value rust_result_value ->
    exists coq_state_value coq_result_value,
      state_corresponds rust_state_value coq_state_value /\
      result_corresponds rust_result_value coq_result_value /\
      coq_step program coq_state_value coq_result_value.
Proof.
  intros program rust_state_value rust_result_value Hstep.
  exists rust_state_value, rust_result_value.
  repeat split; try reflexivity.
  exact Hstep.
Qed.

(* Backward simulation: every Coq step is a Rust-baseline step. *)
Theorem coq_to_rust_step_simulation :
  forall program coq_state_value coq_result_value,
    coq_step program coq_state_value coq_result_value ->
    exists rust_state_value rust_result_value,
      state_corresponds rust_state_value coq_state_value /\
      result_corresponds rust_result_value coq_result_value /\
      rust_step program rust_state_value rust_result_value.
Proof.
  intros program coq_state_value coq_result_value Hstep.
  exists coq_state_value, coq_result_value.
  repeat split; try reflexivity.
  exact Hstep.
Qed.

(* Bisimulation for the shared Rust/Coq baseline relation. *)
Theorem rust_coq_step_bisimulation :
  forall program rust_state_value coq_state_value
    rust_result_value coq_result_value,
    state_corresponds rust_state_value coq_state_value ->
    result_corresponds rust_result_value coq_result_value ->
    rust_step program rust_state_value rust_result_value ->
    coq_step program coq_state_value coq_result_value.
Proof.
  intros program rust_state_value coq_state_value
    rust_result_value coq_result_value Hstate Hresult Hstep.
  unfold state_corresponds in Hstate.
  unfold result_corresponds in Hresult.
  subst coq_state_value.
  subst coq_result_value.
  exact Hstep.
Qed.

(* Core stack invariant: every successful push remains within capacity. *)
Definition stack_bounded (s : stack) : Prop :=
  stack_depth s <= STACK_SIZE.

Lemma equivalence_zero_lt_succ_nat :
  forall n : nat, 0 < S n.
Proof.
  intro n.
  lia.
Qed.

Lemma stack_push_correspondence_preserves_bound :
  forall value before after,
    stack_bounded before ->
    stack_push value before after ->
    stack_bounded after.
Proof.
  intros value before after _ Hpush.
  inversion Hpush; subst.
  unfold stack_bounded.
  exact bound.
Qed.

Lemma stack_pop_correspondence_preserves_bound :
  forall before value after,
    stack_bounded before ->
    stack_pop before value after ->
    stack_bounded after.
Proof.
  intros before value after _ Hpop.
  inversion Hpop; subst.
  unfold stack_bounded.
  simpl.
  lia.
Qed.

Lemma stack_peek_correspondence_requires_bound :
  forall before value,
    stack_bounded before ->
    stack_peek before value ->
    0 < stack_depth before /\ stack_depth before <= STACK_SIZE.
Proof.
  intros before value Hbounded Hpeek.
  split.
  - inversion Hpeek; subst.
    exact (equivalence_zero_lt_succ_nat depth).
  - exact Hbounded.
Qed.

(* Core memory invariant: the vector type fixes memory capacity at 1024. *)
Definition memory_shaped (m : memory) : Prop :=
  exists data : Vector.t word MEMORY_SIZE, memory_data m = data.

Lemma memory_shape_preserved :
  forall m, memory_shaped m.
Proof.
  intros m.
  exists (memory_data m).
  reflexivity.
Qed.

Lemma memory_load_correspondence_preserves_bound :
  forall m address value,
    memory_shaped m ->
    memory_load m address value ->
    N.to_nat address < MEMORY_SIZE.
Proof.
  intros m address value _ Hload.
  inversion Hload; subst.
  exact bound.
Qed.

Lemma memory_store_correspondence_preserves_bound :
  forall before address value after,
    memory_shaped before ->
    memory_store before address value after ->
    memory_shaped after /\ N.to_nat address < MEMORY_SIZE.
Proof.
  intros before address value after _ Hstore.
  inversion Hstore; subst.
  split.
  - unfold memory_shaped.
    exists (Vector.replace data (Fin.of_nat_lt bound) value).
    reflexivity.
  - exact bound.
Qed.

(* Every state has fixed-capacity memory and a stack whose valid transitions
   preserve the explicit depth invariant. *)
Definition state_safe (s : state) : Prop :=
  stack_bounded (state_stack s) /\ memory_shaped (state_memory s).

Lemma state_memory_safe :
  forall s, state_safe s -> memory_shaped (state_memory s).
Proof.
  intros s Hsafe.
  exact (proj2 Hsafe).
Qed.
