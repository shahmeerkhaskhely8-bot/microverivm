(* Structural invariants for the independent Rust-shaped model. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Vectors.Vector.
From MicroVeriVM Require Import RustModel.

Import ListNotations.

Definition valid_stack (stack : RustStack) : Prop :=
  length (rust_stack_values stack) <= RUST_STACK_CAPACITY.

Definition valid_memory (memory : RustMemory) : Prop :=
  exists cells : Vector.t RustWord RUST_MEMORY_SIZE, memory = cells.

Definition rust_word_representation_valid (word : RustWord) : Prop :=
  (rust_word_value word < RUST_WORD_MODULUS)%N.

Definition valid_representation (state : RustState) : Prop :=
  rust_word_representation_valid (rust_pc state) /\
  List.Forall rust_word_representation_valid
    (rust_stack_values (rust_stack state)).

Definition valid_status (status : RustStatus) : Prop :=
  status = RustRunning \/ status = RustHalted.

Definition valid_state (state : RustState) : Prop :=
  valid_stack (rust_stack state) /\
  valid_memory (rust_memory state) /\
  valid_representation state /\
  valid_status (rust_status state).

Definition initial_state : RustState := rust_initial_state.

Theorem initial_state_valid : valid_state initial_state.
Proof.
  unfold valid_state, valid_stack, valid_memory, valid_representation,
    rust_word_representation_valid, valid_status, initial_state,
    rust_initial_state.
  simpl.
  split.
  - unfold RUST_STACK_CAPACITY.
    lia.
  - split.
    + exists (Vector.const rust_word_zero RUST_MEMORY_SIZE).
      reflexivity.
    + split.
      * split.
        -- exact (proj2_sig rust_word_zero).
        -- constructor.
      * left.
        reflexivity.
Qed.

Theorem push_preserves_valid_stack :
  forall value before after,
    valid_stack before ->
    rust_stack_push value before = RustStackPushed after ->
    valid_stack after.
Proof.
  intros value before after _ _.
  exact (rust_stack_bounded after).
Qed.

Theorem pop_preserves_valid_stack :
  forall before value after,
    valid_stack before ->
    rust_stack_pop before = RustStackPopped value after ->
    valid_stack after.
Proof.
  intros before value after _ _.
  exact (rust_stack_bounded after).
Qed.

Theorem memory_store_preserves_valid_memory :
  forall memory address value,
    valid_memory memory ->
    valid_memory (rust_memory_store memory address value).
Proof.
  intros memory address value _.
  unfold valid_memory.
  exists (rust_memory_store memory address value).
  reflexivity.
Qed.

Theorem pc_update_preserves_pc_representation :
  forall state pc,
    valid_representation state ->
    valid_representation (rust_state_with_pc state pc).
Proof.
  intros state pc [Hpc Hstack].
  unfold valid_representation, rust_state_with_pc.
  simpl.
  split.
  - exact (proj2_sig pc).
  - exact Hstack.
Qed.
