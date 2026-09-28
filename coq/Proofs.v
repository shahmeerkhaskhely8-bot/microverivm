(* MicroVeriVM Phase 9: properties of the Phase 8 semantics. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Vectors.Vector.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import Syntax.
From MicroVeriVM Require Import Semantics.

(* Primitive stack safety. *)
Lemma zero_lt_succ_nat :
  forall n : nat, 0 < S n.
Proof.
  intro n.
  lia.
Qed.

Lemma stack_push_preserves_bound :
  forall value s s',
    stack_push value s s' ->
    stack_depth s < STACK_SIZE /\
    stack_depth s' <= STACK_SIZE.
Proof.
  intros value s s' H.
  inversion H; subst.
  split.
  - exact bound.
  - exact bound.
Qed.

Lemma stack_pop_preserves_bound :
  forall s value s',
    stack_pop s value s' ->
    0 < stack_depth s /\
    stack_depth s' < STACK_SIZE.
Proof.
  intros s value s' H.
  inversion H; subst.
  split.
  - exact (zero_lt_succ_nat depth).
  - exact bound.
Qed.

Lemma stack_peek_requires_nonempty :
  forall s value,
    stack_peek s value ->
    0 < stack_depth s.
Proof.
  intros s value H.
  inversion H; subst.
  exact (zero_lt_succ_nat depth).
Qed.

(* Primitive memory safety. *)
Lemma memory_load_requires_valid_address :
  forall mem address value,
    memory_load mem address value ->
    N.to_nat address < MEMORY_SIZE.
Proof.
  intros mem address value H.
  inversion H; subst.
  exact bound.
Qed.

Lemma memory_store_preserves_capacity :
  forall mem address value mem',
    memory_store mem address value mem' ->
    N.to_nat address < MEMORY_SIZE.
Proof.
  intros mem address value mem' H.
  inversion H; subst.
  exact bound.
Qed.

(* u32 boundary arithmetic agrees with Rust's wrapping operations. *)
Theorem modular_add_u32_max_boundary :
  word_value (modular_add word_max word_one) = 0%N.
Proof.
  unfold modular_add, word_modulo, word_value, word_max, word_one,
    word_of_N, WORD_MODULUS.
  simpl.
  vm_compute.
  reflexivity.
Qed.

Theorem modular_sub_u32_zero_boundary :
  word_value (modular_sub word_zero word_one) = N.pred (2 ^ 32).
Proof.
  unfold modular_sub, word_modulo, word_value, word_zero, word_one,
    word_of_N, WORD_MODULUS.
  simpl.
  vm_compute.
  reflexivity.
Qed.

Theorem advance_wraps_u32_max :
  exists next,
    advance (state_with_pc initial_state word_max) (StepOk next) /\
    word_value (state_pc next) = 0%N.
Proof.
  exists
    (state_with_pc
      (state_with_pc initial_state word_max)
      (word_modulo (word_max + 1))).
  split.
  - constructor.
  - simpl.
    unfold word_value, word_modulo, word_of_N, word_max, WORD_MODULUS.
    simpl.
    vm_compute.
    reflexivity.
Qed.

(* Wrapping PC advancement is deterministic. *)
Lemma advance_deterministic :
  forall s r1 r2,
    advance s r1 ->
    advance s r2 ->
    r1 = r2.
Proof.
  intros s r1 r2 H1 H2.
  inversion H1; inversion H2; subst; try reflexivity; try congruence; lia.
Qed.

(* A halted machine has exactly the no-op transition. *)
Theorem halted_step_deterministic :
  forall program s r1 r2,
    state_status s = Halted ->
    step program s r1 ->
    step program s r2 ->
    r1 = r2.
Proof.
  intros program s r1 r2 Hstatus H1 H2.
  assert (Hunique : forall r, step program s r -> r = StepOk s).
  {
    intros r Hstep.
    inversion Hstep; subst; congruence.
  }
  rewrite (Hunique r1 H1), (Hunique r2 H2).
  reflexivity.
Qed.

(* Progress witnesses for the ten instruction forms under the same
   preconditions required by the corresponding Rust operation. *)
Lemma progress_const :
  forall program s value next_stack next_result,
    state_status s = Running ->
    fetch (state_pc s) program (CONST value) ->
    stack_push value (state_stack s) next_stack ->
    advance (state_with_stack s next_stack) next_result ->
    exists result, step program s result.
Proof.
  intros.
  exists next_result.
  eapply StepConst; eauto.
Qed.

Lemma progress_add :
  forall program s left right after_right after_left after_push next_result,
    state_status s = Running ->
    fetch (state_pc s) program ADD ->
    stack_pop (state_stack s) right after_right ->
    stack_pop after_right left after_left ->
    stack_push (modular_add left right) after_left after_push ->
    advance (state_with_stack s after_push) next_result ->
    exists result, step program s result.
Proof.
  intros.
  exists next_result.
  eapply StepAdd; eauto.
Qed.

Lemma progress_sub :
  forall program s left right after_right after_left after_push next_result,
    state_status s = Running ->
    fetch (state_pc s) program SUB ->
    stack_pop (state_stack s) right after_right ->
    stack_pop after_right left after_left ->
    stack_push (modular_sub left right) after_left after_push ->
    advance (state_with_stack s after_push) next_result ->
    exists result, step program s result.
Proof.
  intros.
  exists next_result.
  eapply StepSub; eauto.
Qed.

Lemma progress_dup :
  forall program s value after_push next_result,
    state_status s = Running ->
    fetch (state_pc s) program DUP ->
    stack_peek (state_stack s) value ->
    stack_push value (state_stack s) after_push ->
    advance (state_with_stack s after_push) next_result ->
    exists result, step program s result.
Proof.
  intros.
  exists next_result.
  eapply StepDup; eauto.
Qed.

Lemma progress_drop :
  forall program s value after_pop next_result,
    state_status s = Running ->
    fetch (state_pc s) program DROP ->
    stack_pop (state_stack s) value after_pop ->
    advance (state_with_stack s after_pop) next_result ->
    exists result, step program s result.
Proof.
  intros.
  exists next_result.
  eapply StepDrop; eauto.
Qed.

Lemma progress_load :
  forall program s address value after_push next_result,
    state_status s = Running ->
    fetch (state_pc s) program (LOAD address) ->
    memory_load (state_memory s) address value ->
    stack_push value (state_stack s) after_push ->
    advance (state_with_stack s after_push) next_result ->
    exists result, step program s result.
Proof.
  intros.
  exists next_result.
  eapply StepLoad; eauto.
Qed.

Lemma progress_store :
  forall program s address value after_pop next_memory next_result,
    state_status s = Running ->
    fetch (state_pc s) program (STORE address) ->
    valid_memory_address address ->
    stack_pop (state_stack s) value after_pop ->
    memory_store (state_memory s) address value next_memory ->
    advance
      (state_with_memory (state_with_stack s after_pop) next_memory)
      next_result ->
    exists result, step program s result.
Proof.
  intros.
  exists next_result.
  eapply StepStore; eauto.
Qed.

Lemma progress_jmp :
  forall program s target,
    state_status s = Running ->
    fetch (state_pc s) program (JMP target) ->
    valid_target target program ->
    exists result, step program s result.
Proof.
  intros.
  exists (StepOk (state_with_pc s target)).
  eapply StepJmp; eauto.
Qed.

Lemma progress_jz_zero :
  forall program s target after_pop,
    state_status s = Running ->
    fetch (state_pc s) program (JZ target) ->
    stack_pop (state_stack s) word_zero after_pop ->
    valid_target target program ->
    exists result, step program s result.
Proof.
  intros.
  exists (StepOk (state_with_pc (state_with_stack s after_pop) target)).
  eapply StepJzZero; eauto.
Qed.

Lemma progress_jz_nonzero :
  forall program s target (value : word) after_pop next_result,
    state_status s = Running ->
    fetch (state_pc s) program (JZ target) ->
    value <> word_zero ->
    stack_pop (state_stack s) value after_pop ->
    advance (state_with_stack s after_pop) next_result ->
    exists result, step program s result.
Proof.
  intros.
  exists next_result.
  eapply StepJzNonzero; eauto.
Qed.

Lemma progress_halt :
  forall program s,
    state_status s = Running ->
    fetch (state_pc s) program HALT ->
    exists result, step program s result.
Proof.
  intros.
  exists (StepOk (state_with_status s Halted)).
  eapply StepHalt; eauto.
Qed.

(* Successful stack and memory helper transitions preserve fixed capacity. *)
Theorem successful_stack_push_safe :
  forall value s s',
    stack_push value s s' ->
    stack_depth s' <= STACK_SIZE.
Proof.
  intros value s s' Hpush.
  pose proof (stack_push_preserves_bound value s s' Hpush) as Hbounds.
  exact (proj2 Hbounds).
Qed.

Theorem successful_stack_pop_safe :
  forall s value s',
    stack_pop s value s' ->
    stack_depth s' < STACK_SIZE.
Proof.
  intros s value s' Hpop.
  pose proof (stack_pop_preserves_bound s value s' Hpop) as Hbounds.
  exact (proj2 Hbounds).
Qed.

Theorem successful_memory_access_safe :
  forall mem address value,
    memory_load mem address value ->
    N.to_nat address < MEMORY_SIZE.
Proof.
  intros mem address value Hload.
  exact (memory_load_requires_valid_address mem address value Hload).
Qed.
