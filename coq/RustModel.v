(* Independent mathematical model of the public Rust machine types. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Vectors.Vector.

Import ListNotations.

Definition RUST_WORD_MODULUS : N := (2 ^ 32)%N.
Definition RUST_STACK_CAPACITY : nat := 256.
Definition RUST_MEMORY_SIZE : nat := 1024.

Definition RustWord := { value : N | (value < RUST_WORD_MODULUS)%N }.

Definition rust_word_value (word : RustWord) : N := proj1_sig word.
Coercion rust_word_value : RustWord >-> N.

Definition rust_word_of_N (value : N)
    (bound : (value < RUST_WORD_MODULUS)%N) : RustWord :=
  exist _ value bound.

Lemma RUST_WORD_MODULUS_pos : (0 < RUST_WORD_MODULUS)%N.
Proof.
  unfold RUST_WORD_MODULUS.
  vm_compute.
  reflexivity.
Qed.

Definition rust_word_wrap (value : N) : RustWord :=
  rust_word_of_N (N.modulo value RUST_WORD_MODULUS)
    (N.mod_lt value RUST_WORD_MODULUS
      (ltac:(pose proof RUST_WORD_MODULUS_pos; lia))).

Definition rust_word_zero : RustWord :=
  rust_word_of_N 0%N
    (ltac:(unfold RUST_WORD_MODULUS; vm_compute; reflexivity)).

Definition rust_word_one : RustWord :=
  rust_word_of_N 1%N
    (ltac:(unfold RUST_WORD_MODULUS; vm_compute; reflexivity)).

Definition rust_word_max : RustWord :=
  rust_word_of_N (RUST_WORD_MODULUS - 1)%N
    (ltac:(unfold RUST_WORD_MODULUS; vm_compute; reflexivity)).

Definition rust_wrapping_add (left right : RustWord) : RustWord :=
  rust_word_wrap (left + right).

Definition rust_wrapping_sub (left right : RustWord) : RustWord :=
  rust_word_wrap (left + RUST_WORD_MODULUS - right).

Theorem rust_wrapping_add_zero_zero :
  rust_word_value (rust_wrapping_add rust_word_zero rust_word_zero) = 0%N.
Proof. vm_compute. reflexivity. Qed.

Theorem rust_wrapping_add_max_one :
  rust_word_value (rust_wrapping_add rust_word_max rust_word_one) = 0%N.
Proof. vm_compute. reflexivity. Qed.

Theorem rust_wrapping_add_max_max :
  rust_word_value (rust_wrapping_add rust_word_max rust_word_max) =
    (RUST_WORD_MODULUS - 2)%N.
Proof. vm_compute. reflexivity. Qed.

Theorem rust_wrapping_sub_zero_one :
  rust_word_value (rust_wrapping_sub rust_word_zero rust_word_one) =
    rust_word_value rust_word_max.
Proof. vm_compute. reflexivity. Qed.

Theorem rust_wrapping_sub_one_two :
  rust_word_value (rust_wrapping_sub rust_word_one
    (rust_word_wrap 2%N)) = rust_word_value rust_word_max.
Proof. vm_compute. reflexivity. Qed.

Record RustStack : Type :=
{
  rust_stack_values : list RustWord;
  rust_stack_bounded : length rust_stack_values <= RUST_STACK_CAPACITY
}.

Definition RustMemory : Type := Vector.t RustWord RUST_MEMORY_SIZE.

Definition rust_memory_address_valid (address : N) : Prop :=
  (address < N.of_nat RUST_MEMORY_SIZE)%N.

Theorem rust_memory_addresses_below_1024_valid :
  forall address, (address < 1024)%N -> rust_memory_address_valid address.
Proof.
  intros address Haddress.
  unfold rust_memory_address_valid, RUST_MEMORY_SIZE.
  exact Haddress.
Qed.

Theorem rust_memory_addresses_at_least_1024_invalid :
  forall address, (1024 <= address)%N -> ~ rust_memory_address_valid address.
Proof.
  intros address Haddress Hvalid.
  unfold rust_memory_address_valid, RUST_MEMORY_SIZE in Hvalid.
  lia.
Qed.

Definition rust_memory_store
    (memory : RustMemory)
    (address : Fin.t RUST_MEMORY_SIZE)
    (value : RustWord) : RustMemory :=
  Vector.replace memory address value.

Inductive RustStatus : Type :=
| RustRunning
| RustHalted.

Record RustState : Type :=
{
  rust_pc : RustWord;
  rust_stack : RustStack;
  rust_memory : RustMemory;
  rust_status : RustStatus
}.

Inductive RustInstruction : Type :=
| RustCONST (value : RustWord)
| RustADD
| RustSUB
| RustDUP
| RustDROP
| RustLOAD (address : RustWord)
| RustSTORE (address : RustWord)
| RustJMP (target : RustWord)
| RustJZ (target : RustWord)
| RustHALT.

Inductive RustError : Type :=
| RustStackOverflow
| RustStackUnderflow
| RustMemoryOutOfBounds
| RustInvalidProgramCounter
| RustInvalidInstruction.

Inductive RustPushResult : Type :=
| RustPushSuccess (stack : RustStack)
| RustPushFailure (error : RustError) (stack : RustStack).

Inductive RustPopResult : Type :=
| RustPopSuccess (value : RustWord) (stack : RustStack)
| RustPopFailure (error : RustError) (stack : RustStack).

Definition rust_stack_with_push
    (value : RustWord)
    (stack : RustStack)
    (below : length (rust_stack_values stack) < RUST_STACK_CAPACITY)
    : RustStack.
Proof.
  refine
    {| rust_stack_values := value :: rust_stack_values stack;
       rust_stack_bounded := _ |}.
  simpl.
  lia.
Defined.

Definition rust_stack_with_tail
    (rest : list RustWord)
    (bound : S (length rest) <= RUST_STACK_CAPACITY)
    : RustStack.
Proof.
  refine {| rust_stack_values := rest; rust_stack_bounded := _ |}.
  lia.
Defined.

Definition rust_stack_push (value : RustWord) (stack : RustStack)
  : RustPushResult :=
  match Compare_dec.lt_dec (length (rust_stack_values stack)) RUST_STACK_CAPACITY with
  | left below =>
      RustPushSuccess (rust_stack_with_push value stack below)
  | right _ => RustPushFailure RustStackOverflow stack
  end.

Definition rust_stack_pop (stack : RustStack) : RustPopResult :=
  match stack with
  | {| rust_stack_values := []; rust_stack_bounded := _ |} =>
      RustPopFailure RustStackUnderflow stack
  | {| rust_stack_values := value :: rest; rust_stack_bounded := bound |} =>
      RustPopSuccess value (rust_stack_with_tail rest bound)
  end.

Theorem rust_stack_push_increases_length :
  forall value before after,
    rust_stack_push value before = RustPushSuccess after ->
    length (rust_stack_values after) = S (length (rust_stack_values before)).
Proof.
  intros value before after Hpush.
  unfold rust_stack_push in Hpush.
  destruct (Compare_dec.lt_dec (length (rust_stack_values before)) RUST_STACK_CAPACITY).
  - inversion Hpush; subst.
    simpl.
    reflexivity.
  - discriminate.
Qed.

Theorem rust_stack_push_at_capacity_overflows :
  forall value stack,
    length (rust_stack_values stack) = RUST_STACK_CAPACITY ->
    rust_stack_push value stack = RustPushFailure RustStackOverflow stack.
Proof.
  intros value stack Hcapacity.
  unfold rust_stack_push.
  destruct (Compare_dec.lt_dec (length (rust_stack_values stack)) RUST_STACK_CAPACITY).
  - lia.
  - reflexivity.
Qed.

Theorem rust_stack_pop_decreases_length :
  forall before value after,
    rust_stack_pop before = RustPopSuccess value after ->
    length (rust_stack_values before) = S (length (rust_stack_values after)).
Proof.
  intros before value after Hpop.
  unfold rust_stack_pop in Hpop.
  destruct before as [values bounded].
  destruct values as [|head tail].
  - simpl in Hpop.
    discriminate.
  - simpl in Hpop.
    inversion Hpop; subst.
    simpl.
    reflexivity.
Qed.

Theorem rust_stack_pop_empty_underflows :
  forall stack,
    rust_stack_values stack = [] ->
    rust_stack_pop stack = RustPopFailure RustStackUnderflow stack.
Proof.
  intros stack Hempty.
  unfold rust_stack_pop.
  destruct stack as [values bounded].
  simpl in Hempty.
  subst values.
  simpl.
  reflexivity.
Qed.

(* Failures retain the state after any mutations preceding the trap. *)
Inductive RustResult : Type :=
| Success (s : RustState)
| Failure (e : RustError) (s : RustState).

Definition rust_empty_stack : RustStack :=
  {| rust_stack_values := [];
  rust_stack_bounded := ltac:(unfold RUST_STACK_CAPACITY; simpl; lia) |}.

Definition rust_zero_memory : RustMemory :=
  Vector.const rust_word_zero RUST_MEMORY_SIZE.

Definition rust_initial_state : RustState :=
  {| rust_pc := rust_word_zero;
     rust_stack := rust_empty_stack;
     rust_memory := rust_zero_memory;
     rust_status := RustRunning |}.

Definition rust_state_with_pc (state : RustState) (pc : RustWord) : RustState :=
  {| rust_pc := pc;
     rust_stack := rust_stack state;
     rust_memory := rust_memory state;
     rust_status := rust_status state |}.
