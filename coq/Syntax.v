(* MicroVeriVM Phase 7: abstract machine syntax. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Vectors.Vector.
From Stdlib Require Import Arith.
From Stdlib Require Import Fin.
From Stdlib Require Import Vectors.Fin.

(* Rust u32 values and instruction operands. *)
Definition WORD_MODULUS : N := (2 ^ 32)%N.
Definition word := { value : N | (value < WORD_MODULUS)%N }.
Definition word_value (value : word) : N := proj1_sig value.
Coercion word_value : word >-> N.

Definition word_of_N (value : N) (bound : (value < WORD_MODULUS)%N) : word :=
  exist _ value bound.

Definition word_zero : word :=
  word_of_N 0%N (ltac:(unfold WORD_MODULUS; vm_compute; reflexivity)).

Definition word_one : word :=
  word_of_N 1%N (ltac:(unfold WORD_MODULUS; vm_compute; reflexivity)).

Definition word_max : word :=
  word_of_N (WORD_MODULUS - 1)%N
    (ltac:(unfold WORD_MODULUS; vm_compute; reflexivity)).

Lemma WORD_MODULUS_pos : (0 < WORD_MODULUS)%N.
Proof.
  unfold WORD_MODULUS.
  vm_compute.
  reflexivity.
Qed.

Definition word_modulo (value : N) : word :=
  word_of_N (N.modulo value WORD_MODULUS)
    (N.mod_lt value WORD_MODULUS
      (ltac:(pose proof WORD_MODULUS_pos; lia))).

Definition STACK_SIZE : nat := 256.
Definition MEMORY_SIZE : nat := 1024.

(* The ten Rust baseline instructions. *)
Inductive instruction : Type :=
| CONST (value : word)
| ADD
| SUB
| DUP
| DROP
| LOAD (address : word)
| STORE (address : word)
| JMP (target : word)
| JZ (target : word)
| HALT.

(* Fixed-capacity stack storage with an explicit depth, matching Stack. *)
Record stack : Type :=
{
  stack_data : Vector.t word STACK_SIZE;
  stack_depth : nat
}.

(* Fixed-capacity memory storage, matching Memory. *)
Record memory : Type :=
{
  memory_data : Vector.t word MEMORY_SIZE
}.

Inductive status : Type :=
| Running
| Halted.

(* Machine state, matching State. *)
Record state : Type :=
{
  state_pc : word;
  state_stack : stack;
  state_memory : memory;
  state_status : status
}.

Definition empty_stack : stack :=
{| stack_data := Vector.const word_zero STACK_SIZE;
   stack_depth := 0 |}.

Definition zero_memory : memory :=
{| memory_data := Vector.const word_zero MEMORY_SIZE |}.

Definition initial_state : state :=
{| state_pc := word_zero;
   state_stack := empty_stack;
   state_memory := zero_memory;
   state_status := Running |}.
