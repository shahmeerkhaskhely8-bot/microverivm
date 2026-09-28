(* MicroVeriVM Phase 8: small-step operational semantics. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import Lists.List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Vectors.Vector.
From Stdlib Require Import Vectors.Fin.
From MicroVeriVM Require Import Syntax.

Import ListNotations.
Import VectorNotations.

Inductive error : Type :=
| StackOverflow
| StackUnderflow
| MemoryOutOfBounds
| InvalidProgramCounter
| InvalidInstruction.

Inductive result : Type :=
| StepOk (next : state)
| StepError (post : state) (fault : error).

Definition code := list instruction.

Definition state_with_pc (s : state) (pc : word) : state :=
{| state_pc := pc;
   state_stack := state_stack s;
   state_memory := state_memory s;
   state_status := state_status s |}.

Definition state_with_stack (s : state) (st : stack) : state :=
{| state_pc := state_pc s;
   state_stack := st;
   state_memory := state_memory s;
   state_status := state_status s |}.

Definition state_with_memory (s : state) (mem : memory) : state :=
{| state_pc := state_pc s;
   state_stack := state_stack s;
   state_memory := mem;
   state_status := state_status s |}.

Definition state_with_status (s : state) (st : status) : state :=
{| state_pc := state_pc s;
   state_stack := state_stack s;
   state_memory := state_memory s;
   state_status := st |}.

(* Rust's wrapping increment of the u32 program counter. *)
Inductive advance : state -> result -> Prop :=
| AdvanceWrapping : forall s,
    advance s (StepOk (state_with_pc s (word_modulo (state_pc s + 1)))).

Definition fetch (pc : word) (program : code) (i : instruction) : Prop :=
  nth_error program (N.to_nat pc) = Some i.

Definition valid_target (target : word) (program : code) : Prop :=
  exists i, fetch target program i.

Definition valid_memory_address (address : word) : Prop :=
  N.to_nat address < MEMORY_SIZE.

(* Fixed-capacity stack operations with explicit depth. *)
Inductive stack_push (value : word) : stack -> stack -> Prop :=
| StackPush : forall data depth (bound : depth < STACK_SIZE),
    stack_push value
      {| stack_data := data; stack_depth := depth |}
      {| stack_data := Vector.replace data (Fin.of_nat_lt bound) value;
         stack_depth := S depth |}.

Inductive stack_pop : stack -> word -> stack -> Prop :=
| StackPop : forall data depth (bound : depth < STACK_SIZE),
    stack_pop
      {| stack_data := data; stack_depth := S depth |}
      (Vector.nth data (Fin.of_nat_lt bound))
      {| stack_data := data; stack_depth := depth |}.

Inductive stack_peek : stack -> word -> Prop :=
| StackPeek : forall data depth (bound : depth < STACK_SIZE),
    stack_peek
      {| stack_data := data; stack_depth := S depth |}
      (Vector.nth data (Fin.of_nat_lt bound)).

(* Fixed-capacity memory operations. *)
Inductive memory_load : memory -> word -> word -> Prop :=
| MemoryLoad : forall data (address : word)
    (bound : N.to_nat address < MEMORY_SIZE),
    memory_load
      {| memory_data := data |}
      address
      (Vector.nth data (Fin.of_nat_lt bound)).

Inductive memory_store : memory -> word -> word -> memory -> Prop :=
| MemoryStore : forall data (address : word) value
    (bound : N.to_nat address < MEMORY_SIZE),
    memory_store
      {| memory_data := data |}
      address
      value
      {| memory_data := Vector.replace data (Fin.of_nat_lt bound) value |}.

Definition modular_add (left right : word) : word :=
    word_modulo (left + right).

Definition modular_sub (left right : word) : word :=
    word_modulo (left + (WORD_MODULUS - right)).

(* One Rust-equivalent execution step. *)
Inductive step (program : code) : state -> result -> Prop :=
| StepHalted : forall s,
    state_status s = Halted ->
    step program s (StepOk s)

| StepInvalidProgramCounter : forall s,
    state_status s = Running ->
    (forall i, fetch (state_pc s) program i -> False) ->
    step program s (StepError s InvalidProgramCounter)

| StepConst : forall s value next_stack result_value,
    state_status s = Running ->
    fetch (state_pc s) program (CONST value) ->
    stack_push value (state_stack s) next_stack ->
    advance (state_with_stack s next_stack) result_value ->
    step program s result_value

| StepConstOverflow : forall s value,
    state_status s = Running ->
    fetch (state_pc s) program (CONST value) ->
    stack_depth (state_stack s) = STACK_SIZE ->
    step program s (StepError s StackOverflow)

| StepAdd : forall s right after_right left after_left after_push result_value,
    state_status s = Running ->
    fetch (state_pc s) program ADD ->
    stack_pop (state_stack s) right after_right ->
    stack_pop after_right left after_left ->
    stack_push (modular_add left right) after_left after_push ->
    advance (state_with_stack s after_push) result_value ->
    step program s result_value

| StepAddFirstUnderflow : forall s,
    state_status s = Running ->
    fetch (state_pc s) program ADD ->
    stack_depth (state_stack s) = 0 ->
    step program s (StepError s StackUnderflow)

| StepAddSecondUnderflow : forall s right after_right,
    state_status s = Running ->
    fetch (state_pc s) program ADD ->
    stack_pop (state_stack s) right after_right ->
    stack_depth after_right = 0 ->
    step program s (StepError (state_with_stack s after_right) StackUnderflow)

| StepSub : forall s right after_right left after_left after_push result_value,
    state_status s = Running ->
    fetch (state_pc s) program SUB ->
    stack_pop (state_stack s) right after_right ->
    stack_pop after_right left after_left ->
    stack_push (modular_sub left right) after_left after_push ->
    advance (state_with_stack s after_push) result_value ->
    step program s result_value

| StepSubFirstUnderflow : forall s,
    state_status s = Running ->
    fetch (state_pc s) program SUB ->
    stack_depth (state_stack s) = 0 ->
    step program s (StepError s StackUnderflow)

| StepSubSecondUnderflow : forall s right after_right,
    state_status s = Running ->
    fetch (state_pc s) program SUB ->
    stack_pop (state_stack s) right after_right ->
    stack_depth after_right = 0 ->
    step program s (StepError (state_with_stack s after_right) StackUnderflow)

| StepDup : forall s value after_push result_value,
    state_status s = Running ->
    fetch (state_pc s) program DUP ->
    stack_peek (state_stack s) value ->
    stack_push value (state_stack s) after_push ->
    advance (state_with_stack s after_push) result_value ->
    step program s result_value

| StepDupUnderflow : forall s,
    state_status s = Running ->
    fetch (state_pc s) program DUP ->
    stack_depth (state_stack s) = 0 ->
    step program s (StepError s StackUnderflow)

| StepDupOverflow : forall s value,
    state_status s = Running ->
    fetch (state_pc s) program DUP ->
    stack_peek (state_stack s) value ->
    stack_depth (state_stack s) = STACK_SIZE ->
    step program s (StepError s StackOverflow)

| StepDrop : forall s value after_pop result_value,
    state_status s = Running ->
    fetch (state_pc s) program DROP ->
    stack_pop (state_stack s) value after_pop ->
    advance (state_with_stack s after_pop) result_value ->
    step program s result_value

| StepDropUnderflow : forall s,
    state_status s = Running ->
    fetch (state_pc s) program DROP ->
    stack_depth (state_stack s) = 0 ->
    step program s (StepError s StackUnderflow)

| StepLoad : forall s address value after_push result_value,
    state_status s = Running ->
    fetch (state_pc s) program (LOAD address) ->
    memory_load (state_memory s) address value ->
    stack_push value (state_stack s) after_push ->
    advance (state_with_stack s after_push) result_value ->
    step program s result_value

| StepLoadOutOfBounds : forall s address,
    state_status s = Running ->
    fetch (state_pc s) program (LOAD address) ->
    MEMORY_SIZE <= N.to_nat address ->
    step program s (StepError s MemoryOutOfBounds)

| StepLoadOverflow : forall s address value,
    state_status s = Running ->
    fetch (state_pc s) program (LOAD address) ->
    memory_load (state_memory s) address value ->
    stack_depth (state_stack s) = STACK_SIZE ->
    step program s (StepError s StackOverflow)

| StepStore : forall s address value after_pop next_memory result_value,
    state_status s = Running ->
    fetch (state_pc s) program (STORE address) ->
    valid_memory_address address ->
    stack_pop (state_stack s) value after_pop ->
    memory_store (state_memory s) address value next_memory ->
    advance
      (state_with_memory (state_with_stack s after_pop) next_memory)
      result_value ->
    step program s result_value

| StepStoreOutOfBounds : forall s address,
    state_status s = Running ->
    fetch (state_pc s) program (STORE address) ->
    MEMORY_SIZE <= N.to_nat address ->
    step program s (StepError s MemoryOutOfBounds)

| StepStoreUnderflow : forall s address,
    state_status s = Running ->
    fetch (state_pc s) program (STORE address) ->
    valid_memory_address address ->
    stack_depth (state_stack s) = 0 ->
    step program s (StepError s StackUnderflow)

| StepJmp : forall s target,
    state_status s = Running ->
    fetch (state_pc s) program (JMP target) ->
    valid_target target program ->
    step program s
      (StepOk (state_with_pc s target))

| StepJmpInvalidTarget : forall s target,
    state_status s = Running ->
    fetch (state_pc s) program (JMP target) ->
    (forall i, fetch target program i -> False) ->
    step program s (StepError s InvalidProgramCounter)

| StepJzZero : forall s target after_pop,
    state_status s = Running ->
    fetch (state_pc s) program (JZ target) ->
    stack_pop (state_stack s) word_zero after_pop ->
    valid_target target program ->
    step program s
      (StepOk (state_with_pc (state_with_stack s after_pop) target))

| StepJzZeroInvalidTarget : forall s target after_pop,
    state_status s = Running ->
    fetch (state_pc s) program (JZ target) ->
    stack_pop (state_stack s) word_zero after_pop ->
    (forall i, fetch target program i -> False) ->
    step program s
      (StepError (state_with_stack s after_pop) InvalidProgramCounter)

| StepJzNonzero : forall s target (value : word) after_pop result_value,
    state_status s = Running ->
    fetch (state_pc s) program (JZ target) ->
    value <> word_zero ->
    stack_pop (state_stack s) value after_pop ->
    advance (state_with_stack s after_pop) result_value ->
    step program s result_value

| StepJzUnderflow : forall s target,
    state_status s = Running ->
    fetch (state_pc s) program (JZ target) ->
    stack_depth (state_stack s) = 0 ->
    step program s (StepError s StackUnderflow)

| StepHalt : forall s,
    state_status s = Running ->
    fetch (state_pc s) program HALT ->
    step program s (StepOk (state_with_status s Halted)).
