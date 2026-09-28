(* MicroVeriVM Phase 12: Coq extraction setup. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Vectors.Vector.
From Corelib Require Import Extraction.
From MicroVeriVM Require Import Syntax.
From MicroVeriVM Require Import Semantics.
From MicroVeriVM Require Import Proofs.
From MicroVeriVM Require Import Equivalence.
From MicroVeriVM Require Import Soundness.

Extraction Language OCaml.
Set Extraction Output Directory ".".

(* These are the executable components of the verified baseline. *)
Extraction "microverivm.ml"
  instruction
  status
  stack
  memory
  state
  error
  result
  empty_stack
  zero_memory
  initial_state
  modular_add
  modular_sub.

(* [step], [multi_step], and the Phase 9/10 proof theorems are intentionally
   relational definitions in [Prop].  Coq erases proof terms during extraction,
   so they remain the certified specification and proof boundary rather than
   becoming an unchecked executable interpreter.  The extracted data and
   arithmetic above are the executable components generated from the verified
   definitions. *)
