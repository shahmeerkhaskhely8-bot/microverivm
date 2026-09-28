(* MicroVeriVM Phase 10: Coq model safety invariants. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Vectors.Vector.
From MicroVeriVM Require Import Syntax.
From MicroVeriVM Require Import Semantics.

(* No Rust/Coq simulation theorem is claimed until an independent Rust
   transition relation and a representation proof are available. *)
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
