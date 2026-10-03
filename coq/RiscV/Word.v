(* RV32I machine words and modulo-2^32 arithmetic. *)

From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.

Open Scope N_scope.

Definition rv32_modulus : N := 4294967296.

Definition rv32_word := { value : N | value < rv32_modulus }.

Theorem rv32_modulus_is_two_to_32 :
  rv32_modulus = 2 ^ 32.
Proof.
  reflexivity.
Qed.

Definition rv32_word_value (word : rv32_word) : N :=
  proj1_sig word.

Definition rv32_word_wrap (value : N) : rv32_word.
Proof.
  refine (exist _ (N.modulo value rv32_modulus) _).
  apply N.mod_lt.
  discriminate.
Defined.

Definition rv32_word_zero : rv32_word := rv32_word_wrap 0.

Definition rv32_word_one : rv32_word := rv32_word_wrap 1.

Definition rv32_word_max : rv32_word :=
  rv32_word_wrap (rv32_modulus - 1).

Definition rv32_add (left right : rv32_word) : rv32_word :=
  rv32_word_wrap (rv32_word_value left + rv32_word_value right).

Definition rv32_sub (left right : rv32_word) : rv32_word :=
  rv32_word_wrap
    (rv32_word_value left + rv32_modulus - rv32_word_value right).

Theorem rv32_modulus_positive : 0 < rv32_modulus.
Proof.
  unfold rv32_modulus.
  apply N.lt_trans with (m := 1).
  - exact N.lt_0_1.
  - vm_compute.
    reflexivity.
Qed.

Theorem rv32_word_range :
  forall word, rv32_word_value word < rv32_modulus.
Proof.
  intros [value Hvalue].
  exact Hvalue.
Qed.

Theorem rv32_word_wrap_range :
  forall value, rv32_word_value (rv32_word_wrap value) < rv32_modulus.
Proof.
  intros value.
  apply rv32_word_range.
Qed.

Theorem rv32_word_wrap_small :
  forall value,
    value < rv32_modulus ->
    rv32_word_value (rv32_word_wrap value) = value.
Proof.
  intros value Hvalue.
  unfold rv32_word_wrap, rv32_word_value.
  simpl.
  apply N.mod_small.
  exact Hvalue.
Qed.

Theorem rv32_add_spec :
  forall left right,
    rv32_word_value (rv32_add left right) =
      N.modulo
        (rv32_word_value left + rv32_word_value right)
        rv32_modulus.
Proof.
  reflexivity.
Qed.

Theorem rv32_sub_spec :
  forall left right,
    rv32_word_value (rv32_sub left right) =
      N.modulo
        (rv32_word_value left + rv32_modulus - rv32_word_value right)
        rv32_modulus.
Proof.
  reflexivity.
Qed.

Theorem rv32_add_max_one_wraps :
  rv32_word_value (rv32_add rv32_word_max rv32_word_one) = 0.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem rv32_sub_zero_one_wraps :
  rv32_word_value (rv32_sub rv32_word_zero rv32_word_one) =
    rv32_word_value rv32_word_max.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem rv32_add_preserves_range :
  forall left right,
    rv32_word_value (rv32_add left right) < rv32_modulus.
Proof.
  intros left right.
  apply rv32_word_range.
Qed.

Theorem rv32_sub_preserves_range :
  forall left right,
    rv32_word_value (rv32_sub left right) < rv32_modulus.
Proof.
  intros left right.
  apply rv32_word_range.
Qed.
