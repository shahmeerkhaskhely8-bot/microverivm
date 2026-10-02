(* Lowering of TargetAST instructions into the RustLite statement language. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import String.
From Stdlib Require Import Vectors.Vector.
From MicroVeriVM Require Import RustModel.
From MicroVeriVM Require Import Correspondence.
From MicroVeriVM Require Import TargetAST.
From MicroVeriVM Require Import Bridge.RustLite.

Import ListNotations.
Open Scope string_scope.

Definition rust_word_value_as_rval (word : RustWord) : rval :=
  RVU32 (rust_word_value word).

Definition rust_words_as_rvals (words : list RustWord) : list rval :=
  List.map rust_word_value_as_rval words.

Definition rust_memory_as_rvals (memory : RustMemory) : list rval :=
  rust_words_as_rvals (Vector.to_list memory).

Definition st_rel (state : RustState) (env : environment) : Prop :=
  lookup "pc" env =
    Some (rust_word_value_as_rval (rust_pc state)) /\
  lookup "stack" env =
    Some (RVVec (rust_words_as_rvals
      (rust_stack_values (rust_stack state)))) /\
  lookup "memory" env =
    Some (RVVec (rust_memory_as_rvals (rust_memory state))) /\
  lookup "halted" env =
    Some (RVBool (match rust_status state with
      | RustRunning => false
      | RustHalted => true
      end)).

Definition env_of_state (state : RustState) : environment :=
  [("pc", rust_word_value_as_rval (rust_pc state));
   ("stack", RVVec (rust_words_as_rvals
     (rust_stack_values (rust_stack state))));
   ("memory", RVVec (rust_memory_as_rvals (rust_memory state)));
   ("halted", RVBool (match rust_status state with
     | RustRunning => false
     | RustHalted => true
     end))].

Theorem env_of_state_satisfies_st_rel :
  forall state, st_rel state (env_of_state state).
Proof.
  intros state.
  unfold st_rel, env_of_state, lookup.
  repeat split; reflexivity.
Qed.

Lemma lookup_update_same :
  forall key value env,
    lookup key (update key value env) = Some value.
Proof.
  intros key value env.
  induction env as [|[head old] tail IH].
  - cbn [update lookup].
    rewrite String.eqb_refl.
    reflexivity.
  - cbn [update].
    destruct (String.eqb key head) eqn:Hkey.
    + apply String.eqb_eq in Hkey.
      subst head.
      cbn [lookup].
      rewrite String.eqb_refl.
      reflexivity.
    + cbn [lookup].
      rewrite Hkey.
      exact IH.
Qed.

Lemma lookup_update_other :
  forall name key value env,
    name <> key ->
    lookup name (update key value env) = lookup name env.
Proof.
  intros name key value env Hneq.
  induction env as [|[head old] tail IH].
  - cbn [update lookup].
    destruct (String.eqb name key) eqn:Hname.
    + apply String.eqb_eq in Hname.
      contradiction.
    + reflexivity.
  - cbn [update].
    destruct (String.eqb key head) eqn:Hkey.
    + apply String.eqb_eq in Hkey.
      subst head.
      cbn [lookup].
      destruct (String.eqb name key) eqn:Hname.
      * apply String.eqb_eq in Hname.
        contradiction.
      * reflexivity.
    + cbn [lookup].
      destruct (String.eqb name head); simpl.
      * reflexivity.
      * apply IH.
Qed.

Lemma st_rel_update_stack :
  forall state env next_stack,
    st_rel state env ->
    st_rel
      (rust_state_with_stack state next_stack)
      (update "stack"
        (RVVec (rust_words_as_rvals
          (rust_stack_values next_stack))) env).
Proof.
  intros state env next_stack [Hpc [Hstack [Hmemory Hstatus]]].
  unfold st_rel, rust_state_with_stack.
  simpl.
  split.
  - rewrite (lookup_update_other "pc" "stack" _ env ltac:(discriminate)).
    exact Hpc.
  - split.
    + apply lookup_update_same.
    + split.
      * rewrite (lookup_update_other "memory" "stack" _ env
          ltac:(discriminate)).
        exact Hmemory.
      * rewrite (lookup_update_other "halted" "stack" _ env
          ltac:(discriminate)).
        exact Hstatus.
Qed.

Lemma st_rel_update_memory :
  forall state env next_memory,
    st_rel state env ->
    st_rel
      (rust_state_with_memory state next_memory)
      (update "memory" (RVVec (rust_memory_as_rvals next_memory)) env).
Proof.
  intros state env next_memory [Hpc [Hstack [Hmemory Hstatus]]].
  unfold st_rel, rust_state_with_memory.
  simpl.
  split.
  - rewrite (lookup_update_other "pc" "memory" _ env
      ltac:(discriminate)).
    exact Hpc.
  - split.
    + rewrite (lookup_update_other "stack" "memory" _ env
        ltac:(discriminate)).
      exact Hstack.
    + split.
      * apply lookup_update_same.
      * rewrite (lookup_update_other "halted" "memory" _ env
          ltac:(discriminate)).
        exact Hstatus.
Qed.

Lemma st_rel_update_pc :
  forall state env next_pc,
    st_rel state env ->
    st_rel
      (rust_state_with_pc state next_pc)
      (update "pc" (rust_word_value_as_rval next_pc) env).
Proof.
  intros state env next_pc [Hpc [Hstack [Hmemory Hstatus]]].
  unfold st_rel, rust_state_with_pc.
  simpl.
  split.
  - apply lookup_update_same.
  - split.
    + rewrite (lookup_update_other "stack" "pc" _ env ltac:(discriminate)).
      exact Hstack.
    + split.
      * rewrite (lookup_update_other "memory" "pc" _ env
          ltac:(discriminate)).
        exact Hmemory.
      * rewrite (lookup_update_other "halted" "pc" _ env
          ltac:(discriminate)).
        exact Hstatus.
Qed.

Lemma st_rel_update_private :
  forall state env name value,
    st_rel state env ->
    name <> "pc" ->
    name <> "stack" ->
    name <> "memory" ->
    name <> "halted" ->
    st_rel state (update name value env).
Proof.
  intros state env name value [Hpc [Hstack [Hmemory Hstatus]]]
    Hpc_name Hstack_name Hmemory_name Hstatus_name.
  unfold st_rel.
  split.
  - rewrite (lookup_update_other "pc" name value env).
    + exact Hpc.
    + congruence.
  - split.
    + rewrite (lookup_update_other "stack" name value env).
      * exact Hstack.
      * congruence.
    + split.
      * rewrite (lookup_update_other "memory" name value env).
        -- exact Hmemory.
        -- congruence.
      * rewrite (lookup_update_other "halted" name value env).
        -- exact Hstatus.
        -- congruence.
Qed.

Lemma rust_word_as_rval_eq :
  forall left right,
    rust_word_value left = rust_word_value right ->
    rust_word_value_as_rval left = rust_word_value_as_rval right.
Proof.
  intros [left Hleft] [right Hright] Hvalue.
  simpl in Hvalue.
  subst right.
  reflexivity.
Qed.

Lemma rust_pc_advance_rval_matches :
  forall pc,
    rust_word_value_as_rval (rust_word_wrap (pc + 1)) =
    RVU32 (u32_of_N (pc + 1)).
Proof.
  intros pc.
  reflexivity.
Qed.

Lemma w32_add_one_bounded :
  forall word,
    w32 (w32 (rust_word_value word) + w32 1) =
    w32 (rust_word_value word + 1).
Proof.
  intros word.
  unfold w32.
  assert (Hword : (rust_word_value word < word_modulus)%N).
  { exact (proj2_sig word). }
  rewrite (N.mod_small (rust_word_value word) word_modulus
    Hword).
  assert (Hone : (1 < word_modulus)%N).
  { unfold word_modulus. vm_compute. reflexivity. }
  rewrite (N.mod_small 1 word_modulus Hone).
  reflexivity.
Qed.

Definition rconst (value : rval) : rexpr := EConst value.
Definition rvar (name : string) : rexpr := EVar name.
Definition rword (word : RustWord) : rexpr :=
  rconst (rust_word_value_as_rval word).
Definition rsize (value : N) : rexpr := rconst (RVUsize value).
Definition rbool (value : bool) : rexpr := rconst (RVBool value).

Lemma N_ltb_of_nat :
  forall left right,
    N.ltb (N.of_nat left) (N.of_nat right) = Nat.ltb left right.
Proof.
  intros left right.
  unfold N.ltb.
  rewrite <- Nat2N.inj_compare.
  destruct (Nat.compare left right) eqn:Hcompare; simpl.
  - apply Nat.compare_eq_iff in Hcompare.
    subst right.
    rewrite Nat.ltb_irrefl.
    reflexivity.
  - assert (Hlt : Nat.ltb left right = true).
    { apply Nat.ltb_lt.
      apply Nat.compare_lt_iff in Hcompare.
      exact Hcompare. }
    now rewrite Hlt.
  - apply Nat.compare_gt_iff in Hcompare.
    assert (Nat.ltb left right = false) as Hfalse.
    { destruct (Nat.ltb left right) eqn:Hlt.
      - apply Nat.ltb_lt in Hlt.
        lia.
      - reflexivity. }
    rewrite Hfalse.
    reflexivity.
Qed.

Lemma eval_stack_length :
  forall env words,
    lookup "stack" env = Some (RVVec (rust_words_as_rvals words)) ->
    eval_expr env (EVectorLength (rvar "stack")) =
      Some (RVUsize (N.of_nat (List.length words))).
Proof.
  intros env words Hstack.
  unfold eval_expr, rvar.
  simpl.
  rewrite Hstack.
  unfold rust_words_as_rvals.
  rewrite List.length_map.
  reflexivity.
Qed.

Lemma eval_stack_has_room :
  forall env words,
    lookup "stack" env = Some (RVVec (rust_words_as_rvals words)) ->
    eval_expr env
      (ELessThan
        (EVectorLength (rvar "stack"))
        (rsize (N.of_nat RUST_STACK_CAPACITY))) =
    Some (RVBool (Nat.ltb (List.length words) RUST_STACK_CAPACITY)).
Proof.
  intros env words Hstack.
  change
    (match eval_expr env (EVectorLength (rvar "stack")),
       Some (RVUsize (N.of_nat RUST_STACK_CAPACITY)) with
     | Some (RVUsize lhs), Some (RVUsize rhs) =>
         Some (RVBool (N.ltb lhs rhs))
     | _, _ => None
     end =
     Some (RVBool (Nat.ltb (List.length words) RUST_STACK_CAPACITY))).
  rewrite (eval_stack_length env words Hstack).
  rewrite N_ltb_of_nat.
  reflexivity.
Qed.

Lemma eval_pc_advance :
  forall state env,
    st_rel state env ->
    eval_expr env (EWrapAdd (rvar "pc") (rword rust_word_one)) =
      Some (RVU32
        (u32_of_N
          (rust_word_value (rust_pc state) +
           rust_word_value rust_word_one))).
Proof.
  intros state env [Hpc [Hstack [Hmemory Hstatus]]].
  unfold rust_word_value_as_rval in Hpc.
  cbn [eval_expr rvar rword rconst rust_word_value_as_rval].
  rewrite Hpc.
  reflexivity.
Qed.

Lemma eval_pc_advance_matches_word_wrap :
  forall state,
    RVU32
      (u32_of_N
       (w32 (rust_word_value (rust_pc state)) + w32 1)) =
    rust_word_value_as_rval (rust_word_wrap (rust_pc state + 1)).
Proof.
  intros state.
  unfold rust_word_value_as_rval, rust_word_wrap, rust_word_of_N,
    rust_word_value, u32_of_N.
  simpl.
  f_equal.
  unfold w32, word_modulus, RUST_WORD_MODULUS.
  symmetry.
  apply N.Div0.add_mod.
Qed.

Lemma eval_stack_empty :
  forall env words,
    lookup "stack" env = Some (RVVec (rust_words_as_rvals words)) ->
    eval_expr env (EIsEmpty (rvar "stack")) =
      Some (RVBool (match words with [] => true | _ :: _ => false end)).
Proof.
  intros env words Hstack.
  unfold eval_expr, rvar.
  simpl.
  rewrite Hstack.
  destruct words; reflexivity.
Qed.

Lemma eval_stack_index_zero :
  forall env head tail,
    lookup "stack" env =
      Some (RVVec (rust_words_as_rvals (head :: tail))) ->
    eval_expr env (EVectorIndex (rvar "stack") (rsize 0%N)) =
      Some (rust_word_value_as_rval head).
Proof.
  intros env head tail Hstack.
  unfold eval_expr, rvar, rsize, rconst.
  simpl.
  rewrite Hstack.
  reflexivity.
Qed.

Lemma w32_rust_word_value :
  forall word,
    w32 (rust_word_value word) = rust_word_value word.
Proof.
  intros word.
  unfold w32, word_modulus.
  apply N.mod_small.
  exact (proj2_sig word).
Qed.

Lemma w32_add_congruent :
  forall left right,
    w32 (w32 left + w32 right) = w32 (left + right).
Proof.
  intros left right.
  unfold w32.
  rewrite <- N.Div0.add_mod.
  reflexivity.
Qed.

Lemma eval_wrapping_add_matches :
  forall env left right,
    lookup "$left" env = Some (rust_word_value_as_rval left) ->
    lookup "$right" env = Some (rust_word_value_as_rval right) ->
    eval_expr env (EWrapAdd (rvar "$left") (rvar "$right")) =
      Some (rust_word_value_as_rval
        (rust_wrapping_add left right)).
Proof.
  intros env left right Hleft Hright.
  cbn [eval_expr rvar].
  rewrite Hleft, Hright.
  unfold rust_word_value_as_rval, rust_wrapping_add, rust_word_wrap,
    rust_word_of_N.
  simpl.
  reflexivity.
Qed.

Lemma w32_sub_congruent_bounded :
  forall left right : RustWord,
    w32
      (w32 (rust_word_value left) + word_modulus -
        w32 (rust_word_value right)) =
    w32
      (rust_word_value left + RUST_WORD_MODULUS -
        rust_word_value right).
Proof.
  intros left right.
  rewrite (w32_rust_word_value left).
  rewrite (w32_rust_word_value right).
  unfold word_modulus, RUST_WORD_MODULUS.
  reflexivity.
Qed.

Lemma eval_wrapping_sub_matches :
  forall env left right,
    lookup "$left" env = Some (rust_word_value_as_rval left) ->
    lookup "$right" env = Some (rust_word_value_as_rval right) ->
    eval_expr env (EWrapSub (rvar "$left") (rvar "$right")) =
      Some (rust_word_value_as_rval
        (rust_wrapping_sub left right)).
Proof.
  intros env left right Hleft Hright.
  cbn [eval_expr rvar].
  rewrite Hleft, Hright.
  unfold rust_word_value_as_rval, rust_wrapping_sub, rust_word_wrap,
    rust_word_of_N.
  simpl.
  reflexivity.
Qed.

Definition binary_result_expr (is_add : bool) : rexpr :=
  if is_add
  then EWrapAdd (rvar "$left") (rvar "$right")
  else EWrapSub (rvar "$left") (rvar "$right").

Lemma eval_binary_result_matches :
  forall is_add env left right,
    lookup "$left" env = Some (rust_word_value_as_rval left) ->
    lookup "$right" env = Some (rust_word_value_as_rval right) ->
    eval_expr env (binary_result_expr is_add) =
      Some (rust_word_value_as_rval
        (if is_add
         then rust_wrapping_add left right
         else rust_wrapping_sub left right)).
Proof.
  intros [|] env left right Hleft Hright;
    unfold binary_result_expr.
  - apply eval_wrapping_add_matches; assumption.
  - apply eval_wrapping_sub_matches; assumption.
Qed.

Lemma eval_u32_is_zero :
  forall env word,
    lookup "$condition" env =
      Some (rust_word_value_as_rval word) ->
    eval_expr env (EIsZero (rvar "$condition")) =
      Some (RVBool (N.eqb (rust_word_value word) 0)).
Proof.
  intros env [word Hbound] Hcondition.
  cbn [eval_expr rvar].
  rewrite Hcondition.
  reflexivity.
Qed.

Lemma exec_let_of_evaluated_expression :
  forall fuel name expression env value,
    eval_expr env expression = Some value ->
    exec (S fuel) (RLet name expression) env =
      ROk (update name value env) CNormal.
Proof.
  intros fuel name expression env value Heval.
  simpl.
  now rewrite Heval.
Qed.

Theorem exec_binary_result_assignment_matches :
  forall fuel is_add env left right,
    lookup "$left" env = Some (rust_word_value_as_rval left) ->
    lookup "$right" env = Some (rust_word_value_as_rval right) ->
    exec (S fuel)
      (RLet "$binary_result" (binary_result_expr is_add)) env =
    ROk
      (update "$binary_result"
        (rust_word_value_as_rval
          (if is_add
           then rust_wrapping_add left right
           else rust_wrapping_sub left right)) env)
      CNormal.
Proof.
  intros fuel is_add env left right Hleft Hright.
  apply exec_let_of_evaluated_expression.
  apply eval_binary_result_matches; assumption.
Qed.

Theorem rustlite_add_max_one_wraps :
  eval_expr
    [("$left", rust_word_value_as_rval rust_word_max);
     ("$right", rust_word_value_as_rval rust_word_one)]
    (EWrapAdd (rvar "$left") (rvar "$right")) =
  Some (rust_word_value_as_rval rust_word_zero).
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem rustlite_sub_zero_one_wraps :
  eval_expr
    [("$left", rust_word_value_as_rval rust_word_zero);
     ("$right", rust_word_value_as_rval rust_word_one)]
    (EWrapSub (rvar "$left") (rvar "$right")) =
  Some (rust_word_value_as_rval rust_word_max).
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition trap_stmt (tag : N) : rstmt :=
  RSeq
    (RLet "$trap" (rsize tag))
    RTrap.

Definition guard_not_empty
    (vector_name : string) (underflow_tag : N) (body : rstmt) : rstmt :=
  RIf (EIsEmpty (rvar vector_name))
    (trap_stmt underflow_tag)
    body.

Definition stack_has_room (body : rstmt) (overflow_tag : N) : rstmt :=
  RIf
    (ELessThan
      (EVectorLength (rvar "stack"))
      (rsize (N.of_nat RUST_STACK_CAPACITY)))
    body
    (trap_stmt overflow_tag).

Definition advance_pc : rstmt :=
  RLet "pc"
    (EWrapAdd (rvar "pc")
      (rword rust_word_one)).

Definition push_instruction (word : RustWord) : rstmt :=
  stack_has_room
    (RSeq
      (RPush "stack" (rword word))
      advance_pc)
    1%N.

Definition drop_instruction : rstmt :=
  guard_not_empty "stack" 2%N
    (RSeq
      (RPop "stack" "$discard" (rword rust_word_zero))
      advance_pc).

Definition duplicate_instruction_complete : rstmt :=
  guard_not_empty "stack" 2%N
    (RSeq
      (RLet "$duplicate"
        (EVectorIndex (rvar "stack") (rsize 0%N)))
      (stack_has_room
        (RSeq (RPush "stack" (rvar "$duplicate")) advance_pc)
        1%N)).

Definition binary_instruction (is_add : bool) : rstmt :=
  guard_not_empty "stack" 2%N
    (RSeq
      (RPop "stack" "$right" (rword rust_word_zero))
      (guard_not_empty "stack" 2%N
        (RSeq
          (RPop "stack" "$left" (rword rust_word_zero))
          (stack_has_room
            (RSeq
              (RPush "stack" (binary_result_expr is_add))
              advance_pc)
            1%N)))).

Definition load_instruction (address : RustWord) : rstmt :=
  RIf
    (ELessThan (rsize (rust_word_value address))
      (EVectorLength (rvar "memory")))
    (RSeq
      (RLet "$loaded"
        (EVectorIndex (rvar "memory")
          (rsize (rust_word_value address))))
      (stack_has_room
        (RSeq (RPush "stack" (rvar "$loaded")) advance_pc)
        1%N))
    (trap_stmt 3%N).

Definition store_instruction (address : RustWord) : rstmt :=
  RIf
    (ELessThan (rsize (rust_word_value address))
      (EVectorLength (rvar "memory")))
    (guard_not_empty "stack" 2%N
      (RSeq
        (RPop "stack" "$stored" (rword rust_word_zero))
        (RSeq
          (RLet "memory"
            (EVectorReplace (rvar "memory")
              (rsize (rust_word_value address))
              (rvar "$stored")))
          advance_pc)))
    (trap_stmt 3%N).

Definition jump_instruction (code_length : nat) (target : RustWord) : rstmt :=
  RIf
    (ELessThan (rsize (rust_word_value target))
      (rsize (N.of_nat code_length)))
    (RLet "pc" (rword target))
    (trap_stmt 4%N).

Definition jump_zero_instruction
    (code_length : nat) (target : RustWord) : rstmt :=
  guard_not_empty "stack" 2%N
    (RSeq
      (RPop "stack" "$condition" (rword rust_word_zero))
      (RIf (EIsZero (rvar "$condition"))
        (jump_instruction code_length target)
        advance_pc)).

Definition lower_target_instruction
    (code_length : nat) (instruction : TargetInstruction) : rstmt :=
  match instruction with
  | TPush word => push_instruction word
  | TAddWrapping => binary_instruction true
  | TSubWrapping => binary_instruction false
  | TDuplicateTop => duplicate_instruction_complete
  | TDropTop => drop_instruction
  | TLoadChecked address => load_instruction address
  | TStoreChecked address => store_instruction address
  | TJumpChecked target => jump_instruction code_length target
  | TJumpZeroChecked target => jump_zero_instruction code_length target
  | THalt => RLet "halted" (rbool true)
  end.

Definition lower_target_step
    (code_length : nat) (instruction : TargetInstruction) : rstmt :=
  RIf (rvar "halted") RSkip
    (lower_target_instruction code_length instruction).

Fixpoint lower_fetch (code_length pc : nat)
    (program : list TargetInstruction) : rstmt :=
  match program with
  | [] => trap_stmt 4%N
  | instruction :: tail =>
      let rest := lower_fetch code_length (S pc) tail in
      if N.ltb (N.of_nat pc) word_modulus then
        RIf
          (EEqual (rvar "pc") (rword (rust_word_wrap (N.of_nat pc))))
          (lower_target_instruction code_length instruction)
          rest
      else rest
  end.

Definition lower_fetch_guard
    (env : environment) (pc target : nat) : Prop :=
  (N.of_nat pc < word_modulus)%N /\
  eval_expr env
    (EEqual (rvar "pc")
      (rword (rust_word_wrap (N.of_nat pc)))) =
    Some (RVBool (Nat.eqb pc target)).

Definition lower_target_program_step
    (program : list TargetInstruction) : rstmt :=
  RIf (rvar "halted") RSkip
    (lower_fetch (List.length program) 0 program).

Definition rust_error_tag (error : RustError) : N :=
  match error with
  | RustStackOverflow => 1%N
  | RustStackUnderflow => 2%N
  | RustMemoryOutOfBounds => 3%N
  | RustInvalidProgramCounter => 4%N
  | RustInvalidInstruction => 5%N
  end.

Inductive step_outcome_rel : RustResult -> exec_result -> Prop :=
| StepOutcomeSuccess : forall state env,
    st_rel state env ->
    step_outcome_rel (Success state) (ROk env CNormal)
| StepOutcomeFailure : forall error state env,
    st_rel state env ->
    lookup "$trap" env = Some (RVUsize (rust_error_tag error)) ->
    step_outcome_rel (Failure error state) (RStuck env).

Theorem rustlite_trap_sticks :
  forall fuel env,
    exec (S fuel) RTrap env = RStuck env.
Proof.
  reflexivity.
Qed.

Theorem lower_halt_step_exact :
  forall code_length fuel state,
    rust_status state = RustRunning ->
    exec (S (S fuel))
      (lower_target_step code_length THalt)
      (env_of_state state) =
    ROk (update "halted" (RVBool true) (env_of_state state)) CNormal.
Proof.
  intros code_length fuel state Hrunning.
  destruct state as [pc stack memory status].
  destruct status; simpl in Hrunning; try discriminate.
  reflexivity.
Qed.

Lemma halt_update_related :
  forall state,
    rust_status state = RustRunning ->
    st_rel
      (rust_state_with_status state RustHalted)
      (update "halted" (RVBool true) (env_of_state state)).
Proof.
  intros [pc stack memory status] Hrunning.
  simpl in Hrunning.
  subst status.
  unfold st_rel, env_of_state, rust_state_with_status.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem target_halt_step_exact :
  forall code_length state,
    target_eval code_length THalt state =
      Success (rust_state_with_status state RustHalted).
Proof.
  intros code_length state.
  destruct state as [pc stack memory status].
  destruct status; reflexivity.
Qed.

Theorem halt_instruction_simulation :
  forall code_length fuel state,
    rust_status state = RustRunning ->
    step_outcome_rel
      (target_eval code_length THalt state)
      (exec (S (S fuel))
        (lower_target_step code_length THalt)
        (env_of_state state)).
Proof.
  intros code_length fuel state Hrunning.
  rewrite lower_halt_step_exact by exact Hrunning.
  rewrite target_halt_step_exact.
  constructor.
  apply halt_update_related.
  exact Hrunning.
Qed.

Theorem halted_instruction_simulation :
  forall code_length fuel state instruction,
    rust_status state = RustHalted ->
    step_outcome_rel
      (target_eval code_length instruction state)
      (exec (S (S fuel))
        (lower_target_step code_length instruction)
        (env_of_state state)).
Proof.
  intros code_length fuel state instruction Hhalted.
  destruct state as [pc stack memory status].
  destruct status; simpl in Hhalted; try discriminate.
  unfold lower_target_step, env_of_state, st_rel.
  simpl.
  constructor.
  unfold lookup.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma exec_if_true :
  forall fuel condition then_branch else_branch env,
    eval_expr env condition = Some (RVBool true) ->
    exec (S fuel) (RIf condition then_branch else_branch) env =
      exec fuel then_branch env.
Proof.
  intros fuel condition then_branch else_branch env Hcondition.
  simpl.
  now rewrite Hcondition.
Qed.

Lemma exec_if_false :
  forall fuel condition then_branch else_branch env,
    eval_expr env condition = Some (RVBool false) ->
    exec (S fuel) (RIf condition then_branch else_branch) env =
      exec fuel else_branch env.
Proof.
  intros fuel condition then_branch else_branch env Hcondition.
  simpl.
  now rewrite Hcondition.
Qed.

Theorem lower_fetch_dispatch_at_index :
  forall code_length base distance program instruction env fuel,
    nth_error program distance = Some instruction ->
    (forall offset,
      offset <= distance ->
      lower_fetch_guard env (base + offset) (base + distance)) ->
    exec (S (distance + fuel))
      (lower_fetch code_length base program) env =
    exec fuel (lower_target_instruction code_length instruction) env.
Proof.
  intros code_length base distance.
  revert base.
  induction distance as [|distance IH];
    intros base program instruction env fuel Hfetch Hguards.
  - destruct program as [|head tail]; simpl in Hfetch; try discriminate.
    inversion Hfetch; subst instruction.
    pose proof (Hguards 0 ltac:(lia)) as Hguard0.
    destruct Hguard0 as [Hbound Hequal].
    replace (base + 0) with base in * by lia.
    rewrite Nat.eqb_refl in Hequal.
    assert (Hlt : N.ltb (N.of_nat base) word_modulus = true).
    { apply N.ltb_lt. exact Hbound. }
    unfold lower_fetch at 1.
    rewrite Hlt.
    replace (0 + fuel) with fuel by lia.
    change
      (exec (S fuel)
        (RIf
          (EEqual (rvar "pc")
            (rword (rust_word_wrap (N.of_nat base))))
          (lower_target_instruction code_length head)
          (lower_fetch code_length (S base) tail)) env =
       exec fuel (lower_target_instruction code_length head) env).
    rewrite (exec_if_true fuel
      (EEqual (rvar "pc")
        (rword (rust_word_wrap (N.of_nat base))))
      (lower_target_instruction code_length head)
      (lower_fetch code_length (S base) tail)
      env Hequal).
    reflexivity.
  - destruct program as [|head tail]; simpl in Hfetch; try discriminate.
    pose proof (Hguards 0 ltac:(lia)) as Hguard0.
    destruct Hguard0 as [Hbound Hequal].
    replace (base + 0) with base in * by lia.
    assert (Hlt : N.ltb (N.of_nat base) word_modulus = true).
    { apply N.ltb_lt. exact Hbound. }
    assert (Hequal_false :
      eval_expr env
        (EEqual (rvar "pc")
          (rword (rust_word_wrap (N.of_nat base)))) =
      Some (RVBool false)).
    {
      rewrite Hequal.
      assert (Nat.eqb base (base + S distance) = false) as Hneq.
      { apply Nat.eqb_neq. lia. }
      now rewrite Hneq.
    }
    unfold lower_fetch at 1.
    rewrite Hlt.
    change
      (exec (S (S distance + fuel))
        (RIf
          (EEqual (rvar "pc")
            (rword (rust_word_wrap (N.of_nat base))))
          (lower_target_instruction code_length head)
          (lower_fetch code_length (S base) tail)) env =
       exec fuel (lower_target_instruction code_length instruction) env).
    rewrite (exec_if_false (S distance + fuel)
      (EEqual (rvar "pc")
        (rword (rust_word_wrap (N.of_nat base))))
      (lower_target_instruction code_length head)
      (lower_fetch code_length (S base) tail)
      env Hequal_false).
    replace (S distance + fuel) with (S (distance + fuel)) by lia.
    apply IH with (base := S base) (instruction := instruction).
    + exact Hfetch.
    + intros offset Hoff.
      specialize (Hguards (S offset) ltac:(lia)) as [Hbound' Hequal'].
      unfold lower_fetch_guard.
      replace (S base + offset) with (base + S offset) by lia.
      replace (S base + distance) with (base + S distance) by lia.
      exact (conj Hbound' Hequal').
Qed.

Lemma lower_fetch_guard_from_st_rel :
  forall state env target index,
    st_rel state env ->
    N.to_nat (rust_word_value (rust_pc state)) = target ->
    index <= target ->
    lower_fetch_guard env index target.
Proof.
  intros state env target index [Hpc [Hstack [Hmemory Hhalted]]]
    Hpc_index Hindex.
  assert (Hpc_value :
    rust_word_value (rust_pc state) = N.of_nat target).
  {
    rewrite <- Hpc_index.
    symmetry.
    apply N2Nat.id.
  }
  assert (Hindex_N : (N.of_nat index <= N.of_nat target)%N).
  { induction Hindex; simpl; lia. }
  assert (Htarget_bound :
    (N.of_nat target < word_modulus)%N).
  { rewrite <- Hpc_value. exact (proj2_sig (rust_pc state)). }
  assert (Hindex_bound : (N.of_nat index < word_modulus)%N) by lia.
  assert (Hwrapped :
    rust_word_value (rust_word_wrap (N.of_nat index)) = N.of_nat index).
  {
    unfold rust_word_wrap, rust_word_of_N.
    simpl.
    apply N.mod_small.
    exact Hindex_bound.
  }
  assert (Heqb :
    N.eqb (N.of_nat target) (N.of_nat index) = Nat.eqb index target).
  {
    destruct (Nat.eqb index target) eqn:Heq.
    - apply Nat.eqb_eq in Heq.
      apply N.eqb_eq.
      now rewrite Heq.
    - apply Nat.eqb_neq in Heq.
      assert (N.eqb (N.of_nat target) (N.of_nat index) = false) as Hneq.
      {
        apply N.eqb_neq.
        intro Hcontra.
        apply Heq.
        apply (f_equal N.to_nat) in Hcontra.
        rewrite !Nat2N.id in Hcontra.
        lia.
      }
      now rewrite Hneq.
  }
  unfold lower_fetch_guard.
  split; [exact Hindex_bound|].
  cbn [eval_expr rvar rconst].
  rewrite Hpc.
  change
    (match rval_eqb
      (RVU32 (rust_word_value (rust_pc state)))
      (RVU32 (rust_word_value (rust_word_wrap (N.of_nat index)))) with
     | Some equal => Some (RVBool equal)
     | None => None
     end = Some (RVBool (Nat.eqb index target))).
  rewrite Hpc_value, Hwrapped.
  cbn [rval_eqb].
  now rewrite Heqb.
Qed.

Lemma exec_trap_stmt :
  forall fuel tag env,
    fuel >= 3 ->
    exec fuel (trap_stmt tag) env =
      RStuck (update "$trap" (RVUsize tag) env).
Proof.
  intros [|[|[|fuel]]] tag env Hfuel; try lia.
  reflexivity.
Qed.

Lemma eval_empty_stack_rvals :
  forall env,
    lookup "stack" env = Some (RVVec []) ->
    eval_expr env (EIsEmpty (rvar "stack")) = Some (RVBool true).
Proof.
  intros env Hstack.
  cbn [eval_expr rvar].
  rewrite Hstack.
  reflexivity.
Qed.

Lemma eval_nonempty_stack_rvals :
  forall env head tail,
    lookup "stack" env = Some (RVVec (head :: tail)) ->
    eval_expr env (EIsEmpty (rvar "stack")) = Some (RVBool false).
Proof.
  intros env head tail Hstack.
  cbn [eval_expr rvar].
  rewrite Hstack.
  reflexivity.
Qed.

Lemma exec_guard_empty_stack :
  forall fuel tag body env,
    3 <= fuel ->
    lookup "stack" env = Some (RVVec []) ->
    exec (S fuel) (guard_not_empty "stack" tag body) env =
      RStuck (update "$trap" (RVUsize tag) env).
Proof.
  intros fuel tag body env Hfuel Hstack.
  unfold guard_not_empty at 1.
  rewrite (exec_if_true fuel (EIsEmpty (rvar "stack"))
    (trap_stmt tag) body env (eval_empty_stack_rvals env Hstack)).
  apply exec_trap_stmt.
  exact Hfuel.
Qed.

Lemma exec_guard_nonempty_stack :
  forall fuel head tail tag body env,
    lookup "stack" env = Some (RVVec (head :: tail)) ->
    exec (S fuel) (guard_not_empty "stack" tag body) env =
      exec fuel body env.
Proof.
  intros fuel head tail tag body env Hstack.
  unfold guard_not_empty at 1.
  rewrite (exec_if_false fuel (EIsEmpty (rvar "stack"))
    (trap_stmt tag) body env
    (eval_nonempty_stack_rvals env head tail Hstack)).
  reflexivity.
Qed.

Lemma exec_pop_nonempty_stack :
  forall fuel head tail result_name env,
    lookup "stack" env = Some (RVVec (head :: tail)) ->
    exec (S fuel)
      (RPop "stack" result_name (rword rust_word_zero)) env =
      ROk
        (update result_name head
          (update "stack" (RVVec tail) env))
        CNormal.
Proof.
  intros fuel head tail result_name env Hstack.
  simpl.
  rewrite Hstack.
  reflexivity.
Qed.

Lemma eval_stack_room_rvals :
  forall env values,
    lookup "stack" env = Some (RVVec values) ->
    eval_expr env
      (ELessThan (EVectorLength (rvar "stack"))
        (rsize (N.of_nat RUST_STACK_CAPACITY))) =
      Some (RVBool
        (Nat.ltb (List.length values) RUST_STACK_CAPACITY)).
Proof.
  intros env values Hstack.
  cbn [eval_expr rvar rsize rconst].
  rewrite Hstack.
  rewrite N_ltb_of_nat.
  reflexivity.
Qed.

Lemma exec_stack_has_room_rvals :
  forall fuel values body overflow_tag env,
    lookup "stack" env = Some (RVVec values) ->
    (List.length values < RUST_STACK_CAPACITY)%nat ->
    exec (S fuel) (stack_has_room body overflow_tag) env =
      exec fuel body env.
Proof.
  intros fuel values body overflow_tag env Hstack Hroom.
  eapply exec_if_true.
  rewrite (eval_stack_room_rvals env values Hstack).
  assert (Hlt :
    Nat.ltb (List.length values) RUST_STACK_CAPACITY = true).
  { apply Nat.ltb_lt. exact Hroom. }
  now rewrite Hlt.
Qed.

Lemma rust_stack_values_with_tail :
  forall values bound,
    rust_stack_values (rust_stack_with_tail values bound) = values.
Proof.
  intros values bound.
  reflexivity.
Qed.

Lemma rust_stack_values_with_push :
  forall value stack below,
    rust_stack_values (rust_stack_with_push value stack below) =
      value :: rust_stack_values stack.
Proof.
  intros value stack below.
  reflexivity.
Qed.

Lemma exec_seq_normal :
  forall fuel first second env next_env,
    exec fuel first env = ROk next_env CNormal ->
    exec (S fuel) (RSeq first second) env =
      exec fuel second next_env.
Proof.
  intros fuel first second env next_env Hfirst.
  simpl.
  now rewrite Hfirst.
Qed.

Lemma exec_push_rvals :
  forall fuel env values value,
    lookup "stack" env = Some (RVVec values) ->
    exec (S fuel) (RPush "stack" (EConst value)) env =
      ROk (update "stack" (RVVec (value :: values)) env) CNormal.
Proof.
  intros fuel env values value Hstack.
  simpl.
  rewrite Hstack.
  reflexivity.
Qed.

Lemma exec_push_expression :
  forall fuel env values expression value,
    lookup "stack" env = Some (RVVec values) ->
    eval_expr env expression = Some value ->
    exec (S fuel) (RPush "stack" expression) env =
      ROk (update "stack" (RVVec (value :: values)) env) CNormal.
Proof.
  intros fuel env values expression value Hstack Heval.
  simpl.
  rewrite Hstack, Heval.
  reflexivity.
Qed.

Lemma eval_running_flag :
  forall state env,
    st_rel state env ->
    rust_status state = RustRunning ->
    eval_expr env (rvar "halted") = Some (RVBool false).
Proof.
  intros state env [_ [_ [_ Hhalted]]] Hrunning.
  rewrite Hrunning in Hhalted.
  cbn [eval_expr rvar].
  exact Hhalted.
Qed.

Theorem binary_first_pop_underflow_simulation :
  forall is_add state env,
    rust_status state = RustRunning ->
    st_rel state env ->
    lookup "stack" env = Some (RVVec []) ->
    step_outcome_rel
      (target_binary is_add state)
      (exec 16
        (RIf (rvar "halted") RSkip (binary_instruction is_add))
        env).
Proof.
  intros is_add [pc [words Hbounded] memory status]
    env Hrunning Hrel Hempty.
  destruct status; simpl in Hrunning; try discriminate.
  destruct Hrel as [Hpc [Hstack_rel [Hmemory Hstatus]]].
  destruct words as [|right_word words].
  - assert (Hstack_empty : lookup "stack" env = Some (RVVec [])).
    { exact Hempty. }
    assert (Hrel_state : st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := []; rust_stack_bounded := Hbounded |};
         rust_memory := memory;
         rust_status := RustRunning |} env).
    { unfold st_rel. simpl. repeat split; assumption. }
    rewrite (exec_if_false 15 (rvar "halted") RSkip
      (binary_instruction is_add) env
      (eval_running_flag _ _ Hrel_state Hrunning)).
    unfold binary_instruction at 1.
    rewrite (exec_guard_empty_stack 14 2%N
      (RSeq
        (RPop "stack" "$right" (rword rust_word_zero))
        (guard_not_empty "stack" 2%N
          (RSeq
            (RPop "stack" "$left" (rword rust_word_zero))
            (stack_has_room
              (RSeq
                (RPush "stack" (binary_result_expr is_add))
                advance_pc)
              1%N))))
      env ltac:(lia) Hstack_empty).
    cbn [target_binary rust_stack_pop].
    constructor.
    + apply st_rel_update_private; try assumption; congruence.
    + apply lookup_update_same.
  - simpl in Hstack_rel.
    rewrite Hempty in Hstack_rel.
    discriminate.
Qed.

Theorem binary_second_pop_underflow_simulation :
  forall is_add pc memory right
    (bound : (List.length [right] <= RUST_STACK_CAPACITY)%nat) env,
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := [right]; rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_binary is_add
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := [right]; rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 16
        (RIf (rvar "halted") RSkip (binary_instruction is_add))
        env).
Proof.
  intros is_add pc memory right bound env Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  assert (Hstate : st_rel
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := [right]; rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |} env).
  { unfold st_rel. simpl. repeat split; assumption. }
  assert (Hright :
    lookup "stack" env =
      Some (RVVec [rust_word_value_as_rval right])).
  { exact Hstack. }
  rewrite (exec_if_false 15 (rvar "halted") RSkip
    (binary_instruction is_add) env
    (eval_running_flag _ _ Hstate eq_refl)).
  unfold binary_instruction at 1.
  rewrite (exec_guard_nonempty_stack 14
    (rust_word_value_as_rval right) [] 2%N
    (RSeq
      (RPop "stack" "$right" (rword rust_word_zero))
      (guard_not_empty "stack" 2%N
        (RSeq
          (RPop "stack" "$left" (rword rust_word_zero))
          (stack_has_room
            (RSeq
              (RPush "stack" (binary_result_expr is_add))
              advance_pc)
            1%N))))
    env Hright).
  set (stack_after_right := rust_stack_with_tail [] bound).
  set (env_after_right :=
    update "$right" (rust_word_value_as_rval right)
      (update "stack" (RVVec []) env)).
  rewrite (exec_seq_normal 13
    (RPop "stack" "$right" (rword rust_word_zero))
    (guard_not_empty "stack" 2%N
      (RSeq
        (RPop "stack" "$left" (rword rust_word_zero))
        (stack_has_room
          (RSeq
            (RPush "stack" (binary_result_expr is_add))
            advance_pc)
          1%N)))
    env env_after_right).
  - assert (Hafter_stack :
      lookup "stack" env_after_right = Some (RVVec [])).
    {
      unfold env_after_right.
      rewrite (lookup_update_other "stack" "$right"
        (rust_word_value_as_rval right)
        (update "stack" (RVVec []) env) ltac:(congruence)).
      apply lookup_update_same.
    }
    rewrite (exec_guard_empty_stack 12 2%N
      (RSeq
        (RPop "stack" "$left" (rword rust_word_zero))
        (stack_has_room
          (RSeq
            (RPush "stack" (binary_result_expr is_add))
            advance_pc)
          1%N))
      env_after_right ltac:(lia) Hafter_stack).
    cbn [target_binary rust_stack_pop].
    apply StepOutcomeFailure with
      (error := RustStackUnderflow)
      (state := rust_state_with_stack
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := [right]; rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |}
        stack_after_right)
      (env := update "$trap" (RVUsize 2%N) env_after_right).
    + eapply st_rel_update_private.
      { eapply st_rel_update_private.
        { apply st_rel_update_stack. exact Hstate. }
        all: congruence. }
      all: congruence.
    + apply lookup_update_same.
  - apply exec_pop_nonempty_stack.
    exact Hright.
Qed.

Theorem binary_success_simulation :
  forall is_add pc memory right left tail
    (bound : (List.length (right :: left :: tail) <=
      RUST_STACK_CAPACITY)%nat) env,
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := right :: left :: tail;
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_binary is_add
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := right :: left :: tail;
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 16
        (RIf (rvar "halted") RSkip (binary_instruction is_add))
        env).
Proof.
  intros is_add pc memory right left tail bound env Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := right :: left :: tail;
                        rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  {
    unfold state0, st_rel.
    simpl.
    split; [exact Hpc|].
    split; [exact Hstack|].
    split; [exact Hmemory|exact Hhalted].
  }
  assert (Hstack0 :
    lookup "stack" env =
      Some (RVVec (rust_word_value_as_rval right ::
        rust_word_value_as_rval left :: rust_words_as_rvals tail))).
  { exact Hstack. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  set (stack1 := rust_stack_with_tail (left :: tail) bound).
  assert (Hbound_tail : (S (List.length tail) <=
      RUST_STACK_CAPACITY)%nat).
  { simpl in bound. lia. }
  set (stack2 := rust_stack_with_tail tail Hbound_tail).
  set (state1 := rust_state_with_stack state0 stack1).
  set (state2 := rust_state_with_stack state1 stack2).
  set (result :=
    if is_add then rust_wrapping_add left right
    else rust_wrapping_sub left right).
  assert (Hroom : (List.length tail < RUST_STACK_CAPACITY)%nat).
  { simpl in bound. lia. }
  destruct (Compare_dec.lt_dec (List.length tail) RUST_STACK_CAPACITY)
    as [Hpush_room | Hpush_full].
  2: { exfalso; lia. }
  set (stack3 := rust_stack_with_push result stack2 Hpush_room).
  set (env1 :=
    update "$right" (rust_word_value_as_rval right)
      (update "stack"
        (RVVec (rust_words_as_rvals (left :: tail))) env)).
  set (env2 :=
    update "$left" (rust_word_value_as_rval left)
      (update "stack" (RVVec (rust_words_as_rvals tail)) env1)).
  set (env3 :=
    update "stack"
      (RVVec (rust_word_value_as_rval result ::
        rust_words_as_rvals tail)) env2).
  assert (Hstack1 : lookup "stack" env1 =
      Some (RVVec (rust_words_as_rvals (left :: tail)))).
  {
    unfold env1.
    rewrite (lookup_update_other "stack" "$right"
      (rust_word_value_as_rval right)
      (update "stack"
        (RVVec (rust_words_as_rvals (left :: tail))) env)
      ltac:(congruence)).
    apply lookup_update_same.
  }
  assert (Hstack2 : lookup "stack" env2 =
      Some (RVVec (rust_words_as_rvals tail))).
  {
    unfold env2.
    rewrite (lookup_update_other "stack" "$left"
      (rust_word_value_as_rval left)
      (update "stack" (RVVec (rust_words_as_rvals tail)) env1)
      ltac:(congruence)).
    apply lookup_update_same.
  }
  assert (Hstack3 : lookup "stack" env3 =
      Some (RVVec (rust_word_value_as_rval result ::
        rust_words_as_rvals tail))).
  { unfold env3. apply lookup_update_same. }
  assert (Hpop_right :
    exec 13 (RPop "stack" "$right" (rword rust_word_zero)) env =
      ROk env1 CNormal).
  {
    unfold env1.
    rewrite (exec_pop_nonempty_stack 12
      (rust_word_value_as_rval right)
      (rust_words_as_rvals (left :: tail)) "$right" env Hstack0).
    reflexivity.
  }
  assert (Hpop_left :
    exec 11 (RPop "stack" "$left" (rword rust_word_zero)) env1 =
      ROk env2 CNormal).
  {
    unfold env2.
    rewrite (exec_pop_nonempty_stack 10
      (rust_word_value_as_rval left) (rust_words_as_rvals tail)
      "$left" env1 Hstack1).
    reflexivity.
  }
  assert (Hleft_lookup :
    lookup "$left" env2 = Some (rust_word_value_as_rval left)).
  { unfold env2. apply lookup_update_same. }
  assert (Hright_lookup :
    lookup "$right" env2 = Some (rust_word_value_as_rval right)).
  {
    unfold env2.
    transitivity (lookup "$right"
      (update "stack" (RVVec (rust_words_as_rvals tail)) env1)).
    - apply lookup_update_other. congruence.
    - transitivity (lookup "$right" env1).
      + apply lookup_update_other. congruence.
      + unfold env1. apply lookup_update_same.
  }
  assert (Hresult_eval :
    eval_expr env2 (binary_result_expr is_add) =
      Some (rust_word_value_as_rval result)).
  {
    unfold result.
    apply eval_binary_result_matches; assumption.
  }
  assert (Hroom_eval : (List.length (rust_words_as_rvals tail) <
      RUST_STACK_CAPACITY)%nat).
  { unfold rust_words_as_rvals. rewrite List.length_map. exact Hroom. }
  assert (Hpush_exec :
    exec 9 (RPush "stack" (binary_result_expr is_add)) env2 =
      ROk env3 CNormal).
  {
    unfold env3.
    rewrite (exec_push_expression 8 env2
      (rust_words_as_rvals tail) (binary_result_expr is_add)
      (rust_word_value_as_rval result) Hstack2 Hresult_eval).
    reflexivity.
  }
  assert (Hrel1 : st_rel state1 env1).
  {
    unfold state1, env1.
    apply st_rel_update_private with
      (state := rust_state_with_stack state0 stack1)
      (env := update "stack"
        (RVVec (rust_words_as_rvals (left :: tail))) env)
      (name := "$right")
      (value := rust_word_value_as_rval right).
    { apply st_rel_update_stack. exact Hstate. }
    all: congruence.
  }
  assert (Hrel2 : st_rel state2 env2).
  {
    unfold state2, state1, env2, env1.
    apply st_rel_update_private with
      (state := rust_state_with_stack state1 stack2)
      (env := update "stack" (RVVec (rust_words_as_rvals tail))
        (update "$right" (rust_word_value_as_rval right)
          (update "stack"
            (RVVec (rust_words_as_rvals (left :: tail))) env)))
      (name := "$left")
      (value := rust_word_value_as_rval left).
    { apply st_rel_update_stack. exact Hrel1. }
    all: congruence.
  }
  assert (Henv3_rel : st_rel
    (rust_state_with_stack state2 stack3) env3).
  {
    unfold env3.
    apply st_rel_update_stack.
    exact Hrel2.
  }
  assert (Hadvance_eval :
    eval_expr env3
      (EWrapAdd (rvar "pc") (rword rust_word_one)) =
      Some (rust_word_value_as_rval (rust_word_wrap (pc + 1)))).
  {
    rewrite (eval_pc_advance (rust_state_with_stack state2 stack3)
      env3 Henv3_rel).
    replace (rust_word_value rust_word_one) with 1%N by reflexivity.
    rewrite <- rust_pc_advance_rval_matches.
    reflexivity.
  }
  set (pc1 := rust_word_wrap (pc + 1)).
  set (env4 := update "pc" (rust_word_value_as_rval pc1) env3).
  assert (Hadvance_exec :
    exec 9 advance_pc env3 = ROk env4 CNormal).
  {
    unfold advance_pc, env4.
    apply exec_let_of_evaluated_expression with
      (fuel := 8) (value := rust_word_value_as_rval pc1).
    exact Hadvance_eval.
  }
  rewrite (exec_if_false 15 (rvar "halted") RSkip
    (binary_instruction is_add) env Hflag).
  unfold binary_instruction at 1.
  rewrite (exec_guard_nonempty_stack 14
    (rust_word_value_as_rval right)
    (rust_words_as_rvals (left :: tail)) 2%N
    (RSeq
      (RPop "stack" "$right" (rword rust_word_zero))
      (guard_not_empty "stack" 2%N
        (RSeq
          (RPop "stack" "$left" (rword rust_word_zero))
          (stack_has_room
            (RSeq
              (RPush "stack" (binary_result_expr is_add))
              advance_pc)
            1%N))))
    env Hstack0).
  rewrite (exec_seq_normal 13
    (RPop "stack" "$right" (rword rust_word_zero))
    (guard_not_empty "stack" 2%N
      (RSeq
        (RPop "stack" "$left" (rword rust_word_zero))
        (stack_has_room
          (RSeq
            (RPush "stack" (binary_result_expr is_add))
            advance_pc)
          1%N)))
    env env1 Hpop_right).
  rewrite (exec_guard_nonempty_stack 12
    (rust_word_value_as_rval left) (rust_words_as_rvals tail)
    2%N
    (RSeq
      (RPop "stack" "$left" (rword rust_word_zero))
      (stack_has_room
        (RSeq
          (RPush "stack" (binary_result_expr is_add))
          advance_pc)
        1%N))
    env1 Hstack1).
  rewrite (exec_seq_normal 11
    (RPop "stack" "$left" (rword rust_word_zero))
    (stack_has_room
      (RSeq
        (RPush "stack" (binary_result_expr is_add))
        advance_pc)
      1%N)
    env1 env2 Hpop_left).
  rewrite (exec_stack_has_room_rvals 10
    (rust_words_as_rvals tail)
    (RSeq (RPush "stack" (binary_result_expr is_add)) advance_pc)
    1%N env2 Hstack2 Hroom_eval).
  rewrite (exec_seq_normal 9
    (RPush "stack" (binary_result_expr is_add))
    advance_pc env2 env3 Hpush_exec).
  rewrite Hadvance_exec.
  unfold state0, state2, state1, stack3, stack2, stack1.
  unfold target_binary.
  cbn [rust_stack rust_stack_values rust_stack_pop rust_stack_with_tail].
  unfold rust_stack_push.
  cbn [rust_stack_values rust_stack_with_tail].
  destruct (Compare_dec.lt_dec (List.length tail) RUST_STACK_CAPACITY)
    as [Htarget_room | Htarget_full].
  2: { exfalso. lia. }
  unfold result, pc1, env4.
  constructor.
  destruct Henv3_rel as [Hpc3 [Hstack3_rel [Hmemory3 Hstatus3]]].
  unfold st_rel, rust_state_with_pc, rust_state_with_stack.
  simpl.
  split.
  - apply lookup_update_same.
  - split.
    + change
        (lookup "stack"
          (update "pc" (rust_word_value_as_rval
            (rust_word_wrap (rust_word_value pc + 1))) env3) =
         Some (RVVec
           (rust_words_as_rvals
             ((if is_add then rust_wrapping_add left right
               else rust_wrapping_sub left right) :: tail)))).
      rewrite (lookup_update_other "stack" "pc"
        (rust_word_value_as_rval
          (rust_word_wrap (rust_word_value pc + 1)))
        env3 ltac:(discriminate)).
      rewrite Hstack3_rel.
      unfold rust_words_as_rvals, rust_word_value_as_rval in *.
      reflexivity.
    + split.
      * change
          (lookup "memory"
            (update "pc" (rust_word_value_as_rval pc1) env3) =
           Some (RVVec (rust_memory_as_rvals memory))).
        rewrite (lookup_update_other "memory" "pc"
          (rust_word_value_as_rval pc1) env3 ltac:(discriminate)).
        rewrite Hmemory3.
        unfold state2, state1, stack3, stack2, stack1, rust_state_with_stack.
        simpl.
        reflexivity.
      * change
          (lookup "halted"
            (update "pc" (rust_word_value_as_rval pc1) env3) =
           Some (RVBool false)).
        rewrite (lookup_update_other "halted" "pc"
          (rust_word_value_as_rval pc1) env3 ltac:(discriminate)).
        rewrite Hstatus3.
        unfold state2, state1, stack3, stack2, stack1, rust_state_with_stack.
        simpl.
        reflexivity.
Qed.

Theorem push_instruction_success_simulation :
  forall code_length pc memory stack_values
    (bound : List.length stack_values <= RUST_STACK_CAPACITY)
    word env,
    (List.length stack_values < RUST_STACK_CAPACITY)%nat ->
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := stack_values;
                           rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TPush word)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := stack_values;
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 8 (lower_target_step code_length (TPush word)) env).
Proof.
  intros code_length pc memory stack_values bound word env Hroom Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := stack_values;
                        rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Hstack0 :
    lookup "stack" env = Some (RVVec (rust_words_as_rvals stack_values))).
  { exact Hstack. }
  set (stack1 := rust_stack_with_push word
    {| rust_stack_values := stack_values; rust_stack_bounded := bound |}
    Hroom).
  set (env1 := update "stack"
    (RVVec (rust_word_value_as_rval word ::
      rust_words_as_rvals stack_values)) env).
  assert (Hstack1 :
    lookup "stack" env1 =
      Some (RVVec (rust_word_value_as_rval word ::
        rust_words_as_rvals stack_values))).
  { unfold env1. apply lookup_update_same. }
  assert (Hrel1 :
    st_rel (rust_state_with_stack state0 stack1) env1).
  { unfold env1. apply st_rel_update_stack. exact Hstate. }
  assert (Hadvance_eval :
    eval_expr env1 (EWrapAdd (rvar "pc") (rword rust_word_one)) =
      Some (rust_word_value_as_rval (rust_word_wrap (pc + 1)))).
  {
    rewrite (eval_pc_advance (rust_state_with_stack state0 stack1)
      env1 Hrel1).
    replace (rust_word_value rust_word_one) with 1%N by reflexivity.
    rewrite <- rust_pc_advance_rval_matches.
    reflexivity.
  }
  set (pc1 := rust_word_wrap (pc + 1)).
  set (env2 := update "pc" (rust_word_value_as_rval pc1) env1).
  assert (Hadvance :
    exec 5 advance_pc env1 = ROk env2 CNormal).
  {
    unfold advance_pc, env2.
    apply exec_let_of_evaluated_expression with
      (fuel := 4) (value := rust_word_value_as_rval pc1).
    exact Hadvance_eval.
  }
  assert (Hpush :
    exec 5 (RPush "stack" (rword word)) env =
      ROk env1 CNormal).
  {
    unfold env1, rword.
    simpl.
    rewrite Hstack0.
    reflexivity.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 7 (rvar "halted") RSkip
    (lower_target_instruction code_length (TPush word)) env Hflag).
  unfold lower_target_instruction, push_instruction.
  rewrite (exec_stack_has_room_rvals 6
    (rust_words_as_rvals stack_values)
    (RSeq (RPush "stack" (rword word)) advance_pc)
    1%N env Hstack0).
  2: {
    unfold rust_words_as_rvals.
    rewrite List.length_map.
    exact Hroom.
  }
  rewrite (exec_seq_normal 5
    (RPush "stack" (rword word)) advance_pc env env1 Hpush).
  rewrite Hadvance.
  unfold state0, stack1, env2, pc1.
  unfold target_eval.
  simpl.
  unfold rust_stack_push.
  simpl.
  destruct (Compare_dec.lt_dec
    (List.length stack_values) RUST_STACK_CAPACITY) as [Hlt|Hge].
  2: { exfalso. lia. }
  constructor.
  unfold st_rel, rust_state_with_pc, rust_state_with_stack.
  simpl.
  split.
  - apply lookup_update_same.
  - split.
    + rewrite (lookup_update_other "stack" "pc"
        (rust_word_value_as_rval (rust_word_wrap (pc + 1)))
      env1 ltac:(discriminate)).
      exact Hstack1.
    + split.
      * change
          (lookup "memory"
            (update "pc"
              (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env1) =
           Some (RVVec (rust_memory_as_rvals memory))).
        rewrite (lookup_update_other "memory" "pc"
          (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env1
          ltac:(discriminate)).
        rewrite (proj1 (proj2 (proj2 Hrel1))).
        reflexivity.
      * change
          (lookup "halted"
            (update "pc"
              (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env1) =
           Some (RVBool false)).
        rewrite (lookup_update_other "halted" "pc"
          (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env1
          ltac:(discriminate)).
        rewrite (proj2 (proj2 (proj2 Hrel1))).
        reflexivity.
Qed.

Lemma st_rel_trap_update :
  forall state env tag,
    st_rel state env ->
    st_rel state (update "$trap" (RVUsize tag) env).
Proof.
  intros state env tag Hrel.
  eapply st_rel_update_private; try eassumption; discriminate.
Qed.

Theorem drop_empty_simulation :
  forall code_length state env,
    rust_status state = RustRunning ->
    rust_stack_values (rust_stack state) = [] ->
    st_rel state env ->
    step_outcome_rel
      (target_eval code_length TDropTop state)
      (exec 8 (lower_target_step code_length TDropTop) env).
Proof.
  intros code_length [pc [values bound] memory status] env
    Hrunning Hempty Hrel.
  simpl in Hrunning, Hempty, Hrel.
  destruct status; simpl in Hrunning; try discriminate.
  destruct values as [|head tail]; [|simpl in Hempty; discriminate].
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  assert (Hstate : st_rel
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := []; rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |} env).
  { unfold st_rel. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with
      (state := {| rust_pc := pc;
                   rust_stack := {| rust_stack_values := [];
                                    rust_stack_bounded := bound |};
                   rust_memory := memory;
                   rust_status := RustRunning |});
      assumption. }
  assert (Hstack_empty : lookup "stack" env = Some (RVVec [])).
  {
    simpl in Hstack.
    exact Hstack.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 7 (rvar "halted") RSkip
    (lower_target_instruction code_length TDropTop) env Hflag).
  unfold lower_target_instruction, drop_instruction.
  rewrite (exec_guard_empty_stack 6 2%N
    (RSeq
      (RPop "stack" "$discard" (rword rust_word_zero))
      advance_pc)
    env ltac:(lia) Hstack_empty).
  unfold target_eval.
  simpl.
  constructor.
  - apply st_rel_trap_update.
    exact Hstate.
  - apply lookup_update_same.
Qed.

Theorem drop_nonempty_simulation :
  forall code_length pc memory head tail
    (bound : S (List.length tail) <= RUST_STACK_CAPACITY) env,
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := head :: tail;
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length TDropTop
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := head :: tail;
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 8 (lower_target_step code_length TDropTop) env).
Proof.
  intros code_length pc memory head tail bound env Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := head :: tail;
                        rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Hstack0 :
    lookup "stack" env =
      Some (RVVec (rust_word_value_as_rval head :: rust_words_as_rvals tail))).
  { exact Hstack. }
  set (stack1 := rust_stack_with_tail tail bound).
  set (env1 := update "$discard" (rust_word_value_as_rval head)
    (update "stack" (RVVec (rust_words_as_rvals tail)) env)).
  assert (Hstack1 :
    lookup "stack" env1 = Some (RVVec (rust_words_as_rvals tail))).
  {
    unfold env1.
    rewrite (lookup_update_other "stack" "$discard"
      (rust_word_value_as_rval head)
      (update "stack" (RVVec (rust_words_as_rvals tail)) env)
      ltac:(discriminate)).
    apply lookup_update_same.
  }
  assert (Hrel1 : st_rel (rust_state_with_stack state0 stack1) env1).
  {
    unfold env1.
    eapply st_rel_update_private with
      (state := rust_state_with_stack state0 stack1)
      (env := update "stack" (RVVec (rust_words_as_rvals tail)) env)
      (name := "$discard")
      (value := rust_word_value_as_rval head).
    { apply st_rel_update_stack. exact Hstate. }
    all: congruence.
  }
  assert (Hadvance_eval :
    eval_expr env1 (EWrapAdd (rvar "pc") (rword rust_word_one)) =
      Some (rust_word_value_as_rval (rust_word_wrap (pc + 1)))).
  {
    rewrite (eval_pc_advance (rust_state_with_stack state0 stack1)
      env1 Hrel1).
    replace (rust_word_value rust_word_one) with 1%N by reflexivity.
    rewrite <- rust_pc_advance_rval_matches.
    reflexivity.
  }
  set (pc1 := rust_word_wrap (pc + 1)).
  set (env2 := update "pc" (rust_word_value_as_rval pc1) env1).
  assert (Hpop :
    exec 5 (RPop "stack" "$discard" (rword rust_word_zero)) env =
      ROk env1 CNormal).
  {
    unfold env1.
    rewrite (exec_pop_nonempty_stack 4
      (rust_word_value_as_rval head) (rust_words_as_rvals tail)
      "$discard" env Hstack0).
    reflexivity.
  }
  assert (Hadvance :
    exec 5 advance_pc env1 = ROk env2 CNormal).
  {
    unfold advance_pc, env2.
    apply exec_let_of_evaluated_expression with
      (fuel := 4) (value := rust_word_value_as_rval pc1).
    exact Hadvance_eval.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 7 (rvar "halted") RSkip
    (lower_target_instruction code_length TDropTop) env Hflag).
  unfold lower_target_instruction, drop_instruction.
  rewrite (exec_guard_nonempty_stack 6
    (rust_word_value_as_rval head) (rust_words_as_rvals tail)
    2%N (RSeq
      (RPop "stack" "$discard" (rword rust_word_zero))
      advance_pc) env Hstack0).
  rewrite (exec_seq_normal 5
    (RPop "stack" "$discard" (rword rust_word_zero))
    advance_pc env env1 Hpop).
  rewrite Hadvance.
  unfold state0, stack1, env2, pc1.
  unfold target_eval.
  simpl.
  constructor.
  unfold st_rel, rust_state_with_pc, rust_state_with_stack.
  simpl.
  split.
  - apply lookup_update_same.
  - split.
    + rewrite (lookup_update_other "stack" "pc"
        (rust_word_value_as_rval (rust_word_wrap (pc + 1)))
        env1 ltac:(discriminate)).
      exact Hstack1.
    + split.
      * change
          (lookup "memory"
            (update "pc"
              (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env1) =
           Some (RVVec (rust_memory_as_rvals memory))).
        rewrite (lookup_update_other "memory" "pc"
          (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env1
          ltac:(discriminate)).
        rewrite (proj1 (proj2 (proj2 Hrel1))).
        reflexivity.
      * change
          (lookup "halted"
            (update "pc"
              (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env1) =
           Some (RVBool false)).
        rewrite (lookup_update_other "halted" "pc"
          (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env1
          ltac:(discriminate)).
        rewrite (proj2 (proj2 (proj2 Hrel1))).
        reflexivity.
Qed.

Lemma target_valid_pc_boolean :
  forall code_length target,
    N.ltb (rust_word_value target) (N.of_nat code_length) =
    Nat.ltb (N.to_nat (rust_word_value target)) code_length.
Proof.
  intros code_length target.
  destruct (N.ltb (rust_word_value target) (N.of_nat code_length))
    eqn:Hn;
    destruct (Nat.ltb (N.to_nat (rust_word_value target)) code_length)
      eqn:Hnat;
    try reflexivity.
  - apply N.ltb_lt in Hn.
    apply Nat.ltb_ge in Hnat.
    lia.
  - apply N.ltb_ge in Hn.
    apply Nat.ltb_lt in Hnat.
    lia.
Qed.

Lemma eval_jump_target_guard :
  forall env code_length target,
    eval_expr env
      (ELessThan (rsize (rust_word_value target))
        (rsize (N.of_nat code_length))) =
    Some (RVBool (target_valid_pc code_length target)).
Proof.
  intros env code_length target.
  cbn [eval_expr rsize rconst target_valid_pc].
  rewrite target_valid_pc_boolean.
  reflexivity.
Qed.

Theorem jump_valid_simulation :
  forall code_length pc memory stack status target env,
    rust_status
      {| rust_pc := pc; rust_stack := stack; rust_memory := memory;
         rust_status := status |} = RustRunning ->
    target_valid_pc code_length target = true ->
    st_rel
      {| rust_pc := pc; rust_stack := stack; rust_memory := memory;
         rust_status := RustRunning |} env ->
    step_outcome_rel
      (target_eval code_length (TJumpChecked target)
        {| rust_pc := pc; rust_stack := stack; rust_memory := memory;
           rust_status := RustRunning |})
      (exec 8 (lower_target_step code_length (TJumpChecked target)) env).
Proof.
  intros code_length pc memory stack status target env Hrunning Hvalid Hrel.
  simpl in Hrunning.
  destruct status; simpl in Hrunning; try discriminate.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc; rust_stack := stack; rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Hguard :
    eval_expr env
      (ELessThan (rsize (rust_word_value target))
        (rsize (N.of_nat code_length))) = Some (RVBool true)).
  {
    rewrite eval_jump_target_guard.
    rewrite Hvalid.
    reflexivity.
  }
  set (env1 := update "pc" (rust_word_value_as_rval target) env).
  unfold lower_target_step.
  rewrite (exec_if_false 7 (rvar "halted") RSkip
    (lower_target_instruction code_length (TJumpChecked target)) env Hflag).
  unfold lower_target_instruction, jump_instruction.
  rewrite (exec_if_true 6
    (ELessThan (rsize (rust_word_value target))
      (rsize (N.of_nat code_length)))
    (RLet "pc" (rword target)) (trap_stmt 4%N) env Hguard).
  unfold rword, env1.
  simpl.
  unfold target_eval.
  simpl.
  rewrite Hvalid.
  constructor.
  apply st_rel_update_pc.
  exact Hstate.
Qed.

Theorem jump_invalid_simulation :
  forall code_length pc memory stack status target env,
    rust_status
      {| rust_pc := pc; rust_stack := stack; rust_memory := memory;
         rust_status := status |} = RustRunning ->
    target_valid_pc code_length target = false ->
    st_rel
      {| rust_pc := pc; rust_stack := stack; rust_memory := memory;
         rust_status := RustRunning |} env ->
    step_outcome_rel
      (target_eval code_length (TJumpChecked target)
        {| rust_pc := pc; rust_stack := stack; rust_memory := memory;
           rust_status := RustRunning |})
      (exec 8 (lower_target_step code_length (TJumpChecked target)) env).
Proof.
  intros code_length pc memory stack status target env Hrunning Hinvalid Hrel.
  simpl in Hrunning.
  destruct status; simpl in Hrunning; try discriminate.
  set (state0 :=
    {| rust_pc := pc; rust_stack := stack; rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env) by exact Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Hguard :
    eval_expr env
      (ELessThan (rsize (rust_word_value target))
        (rsize (N.of_nat code_length))) = Some (RVBool false)).
  {
    rewrite eval_jump_target_guard.
    rewrite Hinvalid.
    reflexivity.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 7 (rvar "halted") RSkip
    (lower_target_instruction code_length (TJumpChecked target)) env Hflag).
  unfold lower_target_instruction, jump_instruction.
  rewrite (exec_if_false 6
    (ELessThan (rsize (rust_word_value target))
      (rsize (N.of_nat code_length)))
    (RLet "pc" (rword target)) (trap_stmt 4%N) env Hguard).
  unfold trap_stmt.
  simpl.
  unfold target_eval.
  simpl.
  rewrite Hinvalid.
  constructor.
  - apply st_rel_trap_update.
    exact Hstate.
  - apply lookup_update_same.
Qed.

Theorem duplicate_empty_simulation :
  forall code_length pc memory bound env,
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := [];
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |} env ->
    step_outcome_rel
      (target_eval code_length TDuplicateTop
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := [];
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 12 (lower_target_step code_length TDuplicateTop) env).
Proof.
  intros code_length pc memory bound env Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  assert (Hstate : st_rel
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := []; rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |} env).
  { unfold st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  {
    apply eval_running_flag with
      (state := {| rust_pc := pc;
                   rust_stack := {| rust_stack_values := [];
                                    rust_stack_bounded := bound |};
                   rust_memory := memory;
                   rust_status := RustRunning |});
      [exact Hstate|reflexivity].
  }
  assert (Hstack_empty : lookup "stack" env = Some (RVVec [])).
  { simpl in Hstack. exact Hstack. }
  unfold lower_target_step.
  unfold lower_target_step.
  unfold lower_target_step.
  rewrite (exec_if_false 11 (rvar "halted") RSkip
    (lower_target_instruction code_length TDuplicateTop) env Hflag).
  unfold lower_target_instruction, duplicate_instruction_complete.
  rewrite (exec_guard_empty_stack 10 2%N
    (RSeq
      (RLet "$duplicate"
        (EVectorIndex (rvar "stack") (rsize 0%N)))
      (stack_has_room
        (RSeq (RPush "stack" (rvar "$duplicate")) advance_pc)
        1%N))
    env ltac:(lia) Hstack_empty).
  unfold target_eval.
  simpl.
  constructor.
  - apply st_rel_trap_update.
    exact Hstate.
  - apply lookup_update_same.
Qed.

Theorem duplicate_nonempty_simulation :
  forall code_length pc memory head tail
    (bound : S (List.length tail) <= RUST_STACK_CAPACITY) env,
    (S (List.length tail) < RUST_STACK_CAPACITY)%nat ->
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := head :: tail;
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length TDuplicateTop
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := head :: tail;
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 12 (lower_target_step code_length TDuplicateTop) env).
Proof.
  intros code_length pc memory head tail bound env Hroom Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := head :: tail;
                        rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Hstack0 :
    lookup "stack" env =
      Some (RVVec (rust_word_value_as_rval head :: rust_words_as_rvals tail))).
  { exact Hstack. }
  assert (Hpush_room :
    (List.length (rust_stack_values
      {| rust_stack_values := head :: tail; rust_stack_bounded := bound |}) <
        RUST_STACK_CAPACITY)%nat).
  { simpl. exact Hroom. }
  set (stack1 := rust_stack_with_push head
    {| rust_stack_values := head :: tail; rust_stack_bounded := bound |}
    Hpush_room).
  set (env1 := update "$duplicate" (rust_word_value_as_rval head) env).
  set (env2 := update "stack"
    (RVVec (rust_word_value_as_rval head ::
      rust_word_value_as_rval head :: rust_words_as_rvals tail)) env1).
  assert (Hstack1 :
    lookup "stack" env1 =
      Some (RVVec (rust_word_value_as_rval head ::
        rust_words_as_rvals tail))).
  {
    unfold env1.
    rewrite (lookup_update_other "stack" "$duplicate"
      (rust_word_value_as_rval head) env ltac:(discriminate)).
    exact Hstack0.
  }
  assert (Hdup_lookup :
    lookup "$duplicate" env1 = Some (rust_word_value_as_rval head)).
  { unfold env1. apply lookup_update_same. }
  assert (Hstack2 :
    lookup "stack" env2 =
      Some (RVVec (rust_word_value_as_rval head ::
        rust_word_value_as_rval head :: rust_words_as_rvals tail))).
  { unfold env2. apply lookup_update_same. }
  assert (Hindex :
    eval_expr env
      (EVectorIndex (rvar "stack") (rsize 0%N)) =
      Some (rust_word_value_as_rval head)).
  { apply eval_stack_index_zero with (tail := tail). exact Hstack0. }
  assert (Hlet :
    exec 9
      (RLet "$duplicate"
        (EVectorIndex (rvar "stack") (rsize 0%N))) env =
    ROk env1 CNormal).
  {
    unfold env1.
    apply exec_let_of_evaluated_expression.
    exact Hindex.
  }
  assert (Hpush :
    exec 7 (RPush "stack" (rvar "$duplicate")) env1 =
      ROk env2 CNormal).
  {
    unfold env2.
    rewrite (exec_push_expression 6 env1
      (rust_word_value_as_rval head :: rust_words_as_rvals tail)
      (rvar "$duplicate") (rust_word_value_as_rval head)
      Hstack1).
    - reflexivity.
    - cbn [eval_expr rvar]. exact Hdup_lookup.
  }
  assert (Hstate1 :
    st_rel (rust_state_with_stack state0 stack1) env2).
  {
    unfold env2.
    apply st_rel_update_stack.
    unfold env1.
    eapply st_rel_update_private; try eassumption; discriminate.
  }
  assert (Hadvance_eval :
    eval_expr env2 (EWrapAdd (rvar "pc") (rword rust_word_one)) =
      Some (rust_word_value_as_rval (rust_word_wrap (pc + 1)))).
  {
    rewrite (eval_pc_advance (rust_state_with_stack state0 stack1)
      env2 Hstate1).
    replace (rust_word_value rust_word_one) with 1%N by reflexivity.
    rewrite <- rust_pc_advance_rval_matches.
    reflexivity.
  }
  set (env3 := update "pc"
    (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env2).
  assert (Hadvance : exec 7 advance_pc env2 = ROk env3 CNormal).
  {
    unfold advance_pc, env3.
    apply exec_let_of_evaluated_expression with
      (fuel := 6)
      (value := rust_word_value_as_rval (rust_word_wrap (pc + 1))).
    exact Hadvance_eval.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 11 (rvar "halted") RSkip
    (lower_target_instruction code_length TDuplicateTop) env Hflag).
  unfold lower_target_instruction, duplicate_instruction_complete.
  rewrite (exec_guard_nonempty_stack 10
    (rust_word_value_as_rval head) (rust_words_as_rvals tail) 2%N
    (RSeq
      (RLet "$duplicate"
        (EVectorIndex (rvar "stack") (rsize 0%N)))
      (stack_has_room
        (RSeq (RPush "stack" (rvar "$duplicate")) advance_pc)
        1%N))
    env Hstack0).
  rewrite (exec_seq_normal 9
    (RLet "$duplicate"
      (EVectorIndex (rvar "stack") (rsize 0%N)))
    (stack_has_room
      (RSeq (RPush "stack" (rvar "$duplicate")) advance_pc)
      1%N)
    env env1 Hlet).
  rewrite (exec_stack_has_room_rvals 8
    (rust_word_value_as_rval head :: rust_words_as_rvals tail)
    (RSeq (RPush "stack" (rvar "$duplicate")) advance_pc)
    1%N env1 Hstack1).
  2: {
    change
      (S (List.length (rust_words_as_rvals tail)) <
        RUST_STACK_CAPACITY)%nat.
    unfold rust_words_as_rvals.
    rewrite List.length_map.
    exact Hroom.
  }
  rewrite (exec_seq_normal 7
    (RPush "stack" (rvar "$duplicate")) advance_pc
    env1 env2 Hpush).
  rewrite Hadvance.
  unfold state0, stack1, env3.
  unfold target_eval.
  simpl.
  unfold rust_stack_push.
  simpl.
  replace (List.length (head :: tail)) with
    (S (List.length tail)) by reflexivity.
  destruct (Compare_dec.lt_dec
    (S (List.length tail)) RUST_STACK_CAPACITY) as [Hlt|Hge].
  2: { exfalso. lia. }
  constructor.
  unfold st_rel, rust_state_with_pc, rust_state_with_stack.
  simpl.
  split.
  - apply lookup_update_same.
  - split.
    + rewrite (lookup_update_other "stack" "pc"
        (rust_word_value_as_rval (rust_word_wrap (pc + 1)))
        env2 ltac:(discriminate)).
      exact Hstack2.
    + split.
      * change
          (lookup "memory"
            (update "pc"
              (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env2) =
           Some (RVVec (rust_memory_as_rvals memory))).
        rewrite (lookup_update_other "memory" "pc"
          (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env2
          ltac:(discriminate)).
        rewrite (proj1 (proj2 (proj2 Hstate1))).
        reflexivity.
      * change
          (lookup "halted"
            (update "pc"
              (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env2) =
           Some (RVBool false)).
        rewrite (lookup_update_other "halted" "pc"
          (rust_word_value_as_rval (rust_word_wrap (pc + 1))) env2
          ltac:(discriminate)).
        rewrite (proj2 (proj2 (proj2 Hstate1))).
        reflexivity.
Qed.

Theorem duplicate_capacity_overflow_simulation :
  forall code_length pc memory head tail
    (bound : S (List.length tail) <= RUST_STACK_CAPACITY) env,
    S (List.length tail) = RUST_STACK_CAPACITY ->
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := head :: tail;
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length TDuplicateTop
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := head :: tail;
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 12 (lower_target_step code_length TDuplicateTop) env).
Proof.
  intros code_length pc memory head tail bound env Hfull Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := head :: tail;
                        rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Hstack0 :
    lookup "stack" env =
      Some (RVVec (rust_word_value_as_rval head ::
        rust_words_as_rvals tail))).
  { exact Hstack. }
  set (env1 := update "$duplicate" (rust_word_value_as_rval head) env).
  assert (Hstack1 :
    lookup "stack" env1 =
      Some (RVVec (rust_word_value_as_rval head ::
        rust_words_as_rvals tail))).
  {
    unfold env1.
    rewrite (lookup_update_other "stack" "$duplicate"
      (rust_word_value_as_rval head) env ltac:(discriminate)).
    exact Hstack0.
  }
  assert (Hdup_lookup :
    lookup "$duplicate" env1 = Some (rust_word_value_as_rval head)).
  { unfold env1. apply lookup_update_same. }
  assert (Hindex :
    eval_expr env
      (EVectorIndex (rvar "stack") (rsize 0%N)) =
      Some (rust_word_value_as_rval head)).
  { apply eval_stack_index_zero with (tail := tail). exact Hstack0. }
  assert (Hlet :
    exec 9
      (RLet "$duplicate"
        (EVectorIndex (rvar "stack") (rsize 0%N))) env =
    ROk env1 CNormal).
  {
    unfold env1.
    apply exec_let_of_evaluated_expression.
    exact Hindex.
  }
  assert (Hroom_eval :
    eval_expr env1
      (ELessThan (EVectorLength (rvar "stack"))
        (rsize (N.of_nat RUST_STACK_CAPACITY))) =
    Some (RVBool false)).
  {
    rewrite (eval_stack_room_rvals env1
      (rust_word_value_as_rval head :: rust_words_as_rvals tail) Hstack1).
    f_equal.
    f_equal.
    assert (Hlength :
      List.length
        (rust_word_value_as_rval head :: rust_words_as_rvals tail) =
      RUST_STACK_CAPACITY).
    {
      change
        (S (List.length (rust_words_as_rvals tail)) =
          RUST_STACK_CAPACITY).
      unfold rust_words_as_rvals.
      rewrite List.length_map.
      exact Hfull.
    }
    rewrite Hlength.
    apply Nat.ltb_irrefl.
  }
  assert (Hstate1 : st_rel state0 env1).
  {
    unfold env1.
    eapply st_rel_update_private; try eassumption; discriminate.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 11 (rvar "halted") RSkip
    (lower_target_instruction code_length TDuplicateTop) env Hflag).
  unfold lower_target_instruction, duplicate_instruction_complete.
  rewrite (exec_guard_nonempty_stack 10
    (rust_word_value_as_rval head) (rust_words_as_rvals tail) 2%N
    (RSeq
      (RLet "$duplicate"
        (EVectorIndex (rvar "stack") (rsize 0%N)))
      (stack_has_room
        (RSeq (RPush "stack" (rvar "$duplicate")) advance_pc)
        1%N))
    env Hstack0).
  rewrite (exec_seq_normal 9
    (RLet "$duplicate"
      (EVectorIndex (rvar "stack") (rsize 0%N)))
    (stack_has_room
      (RSeq (RPush "stack" (rvar "$duplicate")) advance_pc)
      1%N)
    env env1 Hlet).
  unfold stack_has_room.
  rewrite (exec_if_false 8
    (ELessThan (EVectorLength (rvar "stack"))
      (rsize (N.of_nat RUST_STACK_CAPACITY)))
    (RSeq (RPush "stack" (rvar "$duplicate")) advance_pc)
    (trap_stmt 1%N) env1 Hroom_eval).
  rewrite exec_trap_stmt by lia.
  unfold target_eval.
  simpl.
  unfold rust_stack_push.
  simpl.
  destruct (Compare_dec.lt_dec
    (S (List.length tail)) RUST_STACK_CAPACITY)
    as [Hlt|Hge].
  - exfalso. lia.
  - constructor.
    + apply st_rel_trap_update. exact Hstate1.
    + apply lookup_update_same.
Qed.

Theorem push_capacity_overflow_simulation :
  forall code_length pc memory stack_values
    (bound : List.length stack_values <= RUST_STACK_CAPACITY)
    word env,
    List.length stack_values = RUST_STACK_CAPACITY ->
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := stack_values;
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TPush word)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := stack_values;
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 8 (lower_target_step code_length (TPush word)) env).
Proof.
  intros code_length pc memory stack_values bound word env Hfull Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := stack_values;
                        rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Hstack0 :
    lookup "stack" env = Some (RVVec (rust_words_as_rvals stack_values))).
  { exact Hstack. }
  assert (Hroom_eval :
    eval_expr env
      (ELessThan (EVectorLength (rvar "stack"))
        (rsize (N.of_nat RUST_STACK_CAPACITY))) =
      Some (RVBool false)).
  {
    rewrite (eval_stack_room_rvals env
      (rust_words_as_rvals stack_values) Hstack0).
    unfold rust_words_as_rvals.
    rewrite List.length_map, Hfull.
    reflexivity.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 7 (rvar "halted") RSkip
    (lower_target_instruction code_length (TPush word)) env Hflag).
  unfold lower_target_instruction, push_instruction, stack_has_room.
  rewrite (exec_if_false 6
    (ELessThan (EVectorLength (rvar "stack"))
      (rsize (N.of_nat RUST_STACK_CAPACITY)))
    (RSeq (RPush "stack" (rword word)) advance_pc)
    (trap_stmt 1%N) env Hroom_eval).
  unfold trap_stmt.
  simpl.
  unfold target_eval.
  simpl.
  unfold rust_stack_push.
  destruct (Compare_dec.lt_dec
    (List.length
      (rust_stack_values
        {| rust_stack_values := stack_values;
           rust_stack_bounded := bound |}))
    RUST_STACK_CAPACITY) as [Hlt|Hge].
  - simpl in Hlt. lia.
  - simpl in Hge.
    rewrite Hfull in Hge.
    constructor.
    + apply st_rel_trap_update. exact Hstate.
    + apply lookup_update_same.
Qed.

Theorem jump_zero_underflow_simulation :
  forall code_length pc memory bound target env,
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := [];
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |} env ->
    step_outcome_rel
      (target_eval code_length (TJumpZeroChecked target)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := [];
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 8 (lower_target_step code_length (TJumpZeroChecked target)) env).
Proof.
  intros code_length pc memory bound target env Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  assert (Hstate : st_rel
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := []; rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |} env).
  { unfold st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  {
    apply eval_running_flag with
      (state := {| rust_pc := pc;
                   rust_stack := {| rust_stack_values := [];
                                    rust_stack_bounded := bound |};
                   rust_memory := memory;
                   rust_status := RustRunning |});
      [exact Hstate|reflexivity].
  }
  assert (Hstack_empty : lookup "stack" env = Some (RVVec [])).
  { simpl in Hstack. exact Hstack. }
  unfold lower_target_step.
  rewrite (exec_if_false 7 (rvar "halted") RSkip
    (lower_target_instruction code_length (TJumpZeroChecked target)) env Hflag).
  unfold lower_target_instruction, jump_zero_instruction.
  rewrite (exec_guard_empty_stack 6 2%N
    (RSeq
      (RPop "stack" "$condition" (rword rust_word_zero))
      (RIf (EIsZero (rvar "$condition"))
        (jump_instruction code_length target)
        advance_pc))
    env ltac:(lia) Hstack_empty).
  unfold target_eval.
  simpl.
  constructor.
  - apply st_rel_trap_update. exact Hstate.
  - apply lookup_update_same.
Qed.

Theorem jump_zero_zero_branch_simulation :
  forall code_length pc memory condition tail
    (bound : S (List.length tail) <= RUST_STACK_CAPACITY)
    target env,
    target_valid_pc code_length target = true ->
    N.eqb (rust_word_value condition) 0 = true ->
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := condition :: tail;
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TJumpZeroChecked target)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := condition :: tail;
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 20 (lower_target_step code_length (TJumpZeroChecked target)) env).
Proof.
  intros code_length pc memory condition tail bound target env
    Htarget Hzero Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := condition :: tail;
                        rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Hstack0 :
    lookup "stack" env =
      Some (RVVec (rust_word_value_as_rval condition ::
        rust_words_as_rvals tail))).
  { exact Hstack. }
  set (stack1 := rust_stack_with_tail tail bound).
  set (env1 := update "$condition" (rust_word_value_as_rval condition)
    (update "stack" (RVVec (rust_words_as_rvals tail)) env)).
  assert (Hpop :
    exec 17 (RPop "stack" "$condition" (rword rust_word_zero)) env =
      ROk env1 CNormal).
  {
    unfold env1.
    apply exec_pop_nonempty_stack.
    exact Hstack0.
  }
  assert (Hstate1 : st_rel (rust_state_with_stack state0 stack1) env1).
  {
    unfold env1, stack1.
    eapply st_rel_update_private with
      (state := rust_state_with_stack state0
        (rust_stack_with_tail tail bound))
      (env := update "stack" (RVVec (rust_words_as_rvals tail)) env)
      (name := "$condition")
      (value := rust_word_value_as_rval condition).
    - apply st_rel_update_stack. exact Hstate.
    - congruence.
    - congruence.
    - congruence.
    - congruence.
  }
  assert (Hcondition :
    lookup "$condition" env1 = Some (rust_word_value_as_rval condition)).
  { unfold env1. apply lookup_update_same. }
  assert (Hzero_eval :
    eval_expr env1 (EIsZero (rvar "$condition")) = Some (RVBool true)).
  {
    rewrite (eval_u32_is_zero env1 condition Hcondition).
    rewrite Hzero.
    reflexivity.
  }
  assert (Htarget_eval :
    eval_expr env1
      (ELessThan (rsize (rust_word_value target))
        (rsize (N.of_nat code_length))) = Some (RVBool true)).
  {
    rewrite eval_jump_target_guard.
    exact (f_equal (fun b => Some (RVBool b)) Htarget).
  }
  set (env2 := update "pc" (rust_word_value_as_rval target) env1).
  assert (Hjump :
    exec 16 (jump_instruction code_length target) env1 =
      ROk env2 CNormal).
  {
    unfold jump_instruction.
    rewrite (exec_if_true 15
      (ELessThan (rsize (rust_word_value target))
        (rsize (N.of_nat code_length)))
      (RLet "pc" (rword target)) (trap_stmt 4%N) env1 Htarget_eval).
    unfold env2, rword.
    apply exec_let_of_evaluated_expression.
    reflexivity.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 19 (rvar "halted") RSkip
    (lower_target_instruction code_length (TJumpZeroChecked target))
    env Hflag).
  unfold lower_target_instruction, jump_zero_instruction.
  rewrite (exec_guard_nonempty_stack 18
    (rust_word_value_as_rval condition) (rust_words_as_rvals tail) 2%N
    (RSeq
      (RPop "stack" "$condition" (rword rust_word_zero))
      (RIf (EIsZero (rvar "$condition"))
        (jump_instruction code_length target)
        advance_pc))
    env Hstack0).
  rewrite (exec_seq_normal 17
    (RPop "stack" "$condition" (rword rust_word_zero))
    (RIf (EIsZero (rvar "$condition"))
      (jump_instruction code_length target)
      advance_pc)
    env env1 Hpop).
  rewrite (exec_if_true 16 (EIsZero (rvar "$condition"))
    (jump_instruction code_length target) advance_pc env1 Hzero_eval).
  rewrite Hjump.
  unfold target_eval.
  simpl.
  rewrite Hzero.
  rewrite Htarget.
  apply StepOutcomeSuccess.
  unfold target_advance_pc.
  apply st_rel_update_pc.
  exact Hstate1.
Qed.

Theorem jump_zero_nonzero_branch_simulation :
  forall code_length pc memory condition tail
    (bound : S (List.length tail) <= RUST_STACK_CAPACITY)
    target env,
    N.eqb (rust_word_value condition) 0 = false ->
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := condition :: tail;
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TJumpZeroChecked target)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := condition :: tail;
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 16 (lower_target_step code_length (TJumpZeroChecked target)) env).
Proof.
  intros code_length pc memory condition tail bound target env Hnonzero Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := condition :: tail;
                        rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Hstack0 :
    lookup "stack" env =
      Some (RVVec (rust_word_value_as_rval condition ::
        rust_words_as_rvals tail))).
  { exact Hstack. }
  set (stack1 := rust_stack_with_tail tail bound).
  set (env1 := update "$condition" (rust_word_value_as_rval condition)
    (update "stack" (RVVec (rust_words_as_rvals tail)) env)).
  assert (Hpop :
    exec 13 (RPop "stack" "$condition" (rword rust_word_zero)) env =
      ROk env1 CNormal).
  {
    unfold env1.
    apply exec_pop_nonempty_stack.
    exact Hstack0.
  }
  assert (Hstate1 : st_rel (rust_state_with_stack state0 stack1) env1).
  {
    unfold env1, stack1.
    eapply st_rel_update_private with
      (state := rust_state_with_stack state0
        (rust_stack_with_tail tail bound))
      (env := update "stack" (RVVec (rust_words_as_rvals tail)) env)
      (name := "$condition")
      (value := rust_word_value_as_rval condition).
    - apply st_rel_update_stack. exact Hstate.
    - congruence.
    - congruence.
    - congruence.
    - congruence.
  }
  assert (Hcondition :
    lookup "$condition" env1 = Some (rust_word_value_as_rval condition)).
  { unfold env1. apply lookup_update_same. }
  assert (Hzero_eval :
    eval_expr env1 (EIsZero (rvar "$condition")) = Some (RVBool false)).
  {
    rewrite (eval_u32_is_zero env1 condition Hcondition).
    rewrite Hnonzero.
    reflexivity.
  }
  set (pc1 := rust_word_wrap (pc + 1)).
  set (env2 := update "pc" (rust_word_value_as_rval pc1) env1).
  assert (Hadvance_eval :
    eval_expr env1 (EWrapAdd (rvar "pc") (rword rust_word_one)) =
      Some (rust_word_value_as_rval pc1)).
  {
    rewrite (eval_pc_advance (rust_state_with_stack state0 stack1)
      env1 Hstate1).
    replace (rust_word_value rust_word_one) with 1%N by reflexivity.
    unfold pc1.
    rewrite <- rust_pc_advance_rval_matches.
    reflexivity.
  }
  assert (Hadvance :
    exec 12 advance_pc env1 = ROk env2 CNormal).
  {
    unfold advance_pc, env2.
    apply exec_let_of_evaluated_expression.
    exact Hadvance_eval.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 15 (rvar "halted") RSkip
    (lower_target_instruction code_length (TJumpZeroChecked target))
    env Hflag).
  unfold lower_target_instruction, jump_zero_instruction.
  rewrite (exec_guard_nonempty_stack 14
    (rust_word_value_as_rval condition) (rust_words_as_rvals tail) 2%N
    (RSeq
      (RPop "stack" "$condition" (rword rust_word_zero))
      (RIf (EIsZero (rvar "$condition"))
        (jump_instruction code_length target)
        advance_pc))
    env Hstack0).
  rewrite (exec_seq_normal 13
    (RPop "stack" "$condition" (rword rust_word_zero))
    (RIf (EIsZero (rvar "$condition"))
      (jump_instruction code_length target)
      advance_pc)
    env env1 Hpop).
  rewrite (exec_if_false 12 (EIsZero (rvar "$condition"))
    (jump_instruction code_length target) advance_pc env1 Hzero_eval).
  rewrite Hadvance.
  unfold target_eval.
  simpl.
  rewrite Hnonzero.
  apply StepOutcomeSuccess.
  unfold target_advance_pc.
  apply st_rel_update_pc.
  exact Hstate1.
Qed.

Theorem jump_zero_invalid_target_simulation :
  forall code_length pc memory condition tail
    (bound : S (List.length tail) <= RUST_STACK_CAPACITY)
    target env,
    target_valid_pc code_length target = false ->
    N.eqb (rust_word_value condition) 0 = true ->
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := condition :: tail;
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TJumpZeroChecked target)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := condition :: tail;
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 20 (lower_target_step code_length (TJumpZeroChecked target)) env).
Proof.
  intros code_length pc memory condition tail bound target env
    Htarget Hzero Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := condition :: tail;
                        rust_stack_bounded := bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Hstack0 :
    lookup "stack" env =
      Some (RVVec (rust_word_value_as_rval condition ::
        rust_words_as_rvals tail))).
  { exact Hstack. }
  set (stack1 := rust_stack_with_tail tail bound).
  set (env1 := update "$condition" (rust_word_value_as_rval condition)
    (update "stack" (RVVec (rust_words_as_rvals tail)) env)).
  assert (Hpop :
    exec 17 (RPop "stack" "$condition" (rword rust_word_zero)) env =
      ROk env1 CNormal).
  {
    unfold env1.
    apply exec_pop_nonempty_stack.
    exact Hstack0.
  }
  assert (Hstate1 : st_rel (rust_state_with_stack state0 stack1) env1).
  {
    unfold env1, stack1.
    eapply st_rel_update_private with
      (state := rust_state_with_stack state0
        (rust_stack_with_tail tail bound))
      (env := update "stack" (RVVec (rust_words_as_rvals tail)) env)
      (name := "$condition")
      (value := rust_word_value_as_rval condition).
    - apply st_rel_update_stack. exact Hstate.
    - congruence.
    - congruence.
    - congruence.
    - congruence.
  }
  assert (Hcondition :
    lookup "$condition" env1 = Some (rust_word_value_as_rval condition)).
  { unfold env1. apply lookup_update_same. }
  assert (Hzero_eval :
    eval_expr env1 (EIsZero (rvar "$condition")) = Some (RVBool true)).
  {
    rewrite (eval_u32_is_zero env1 condition Hcondition).
    rewrite Hzero.
    reflexivity.
  }
  assert (Htarget_eval :
    eval_expr env1
      (ELessThan (rsize (rust_word_value target))
        (rsize (N.of_nat code_length))) = Some (RVBool false)).
  {
    rewrite eval_jump_target_guard.
    exact (f_equal (fun b => Some (RVBool b)) Htarget).
  }
  set (env2 := update "$trap" (RVUsize 4%N) env1).
  assert (Hjump :
    exec 16 (jump_instruction code_length target) env1 =
      RStuck env2).
  {
    unfold jump_instruction.
    rewrite (exec_if_false 15
      (ELessThan (rsize (rust_word_value target))
        (rsize (N.of_nat code_length)))
      (RLet "pc" (rword target)) (trap_stmt 4%N) env1 Htarget_eval).
    unfold env2.
    apply exec_trap_stmt.
    lia.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 19 (rvar "halted") RSkip
    (lower_target_instruction code_length (TJumpZeroChecked target))
    env Hflag).
  unfold lower_target_instruction, jump_zero_instruction.
  rewrite (exec_guard_nonempty_stack 18
    (rust_word_value_as_rval condition) (rust_words_as_rvals tail) 2%N
    (RSeq
      (RPop "stack" "$condition" (rword rust_word_zero))
      (RIf (EIsZero (rvar "$condition"))
        (jump_instruction code_length target)
        advance_pc))
    env Hstack0).
  rewrite (exec_seq_normal 17
    (RPop "stack" "$condition" (rword rust_word_zero))
    (RIf (EIsZero (rvar "$condition"))
      (jump_instruction code_length target)
      advance_pc)
    env env1 Hpop).
  rewrite (exec_if_true 16 (EIsZero (rvar "$condition"))
    (jump_instruction code_length target) advance_pc env1 Hzero_eval).
  rewrite Hjump.
  unfold target_eval.
  simpl.
  rewrite Hzero, Htarget.
  apply StepOutcomeFailure with
    (error := RustInvalidProgramCounter)
    (state := rust_state_with_stack state0 stack1)
    (env := env2).
  - unfold env2.
    apply st_rel_trap_update.
    exact Hstate1.
  - unfold env2.
    apply lookup_update_same.
Qed.

Theorem jump_zero_target_bounds :
  forall code_length target,
    target_valid_pc code_length target = true <->
      N.to_nat (rust_word_value target) < code_length.
Proof.
  intros code_length target.
  unfold target_valid_pc.
  apply Nat.ltb_lt.
Qed.

Theorem jump_zero_nonempty_simulation :
  forall code_length pc memory condition tail
    (bound : S (List.length tail) <= RUST_STACK_CAPACITY)
    target env,
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := condition :: tail;
                          rust_stack_bounded := bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TJumpZeroChecked target)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := condition :: tail;
                            rust_stack_bounded := bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 20 (lower_target_step code_length (TJumpZeroChecked target)) env).
Proof.
  intros code_length pc memory condition tail bound target env Hrel.
  destruct (N.eqb (rust_word_value condition) 0) eqn:Hzero.
  - destruct (target_valid_pc code_length target) eqn:Htarget.
    + eapply jump_zero_zero_branch_simulation; eassumption.
    + eapply jump_zero_invalid_target_simulation; eassumption.
  - eapply jump_zero_nonzero_branch_simulation; eassumption.
Qed.

Lemma eval_memory_length :
  forall env memory,
    lookup "memory" env =
      Some (RVVec (rust_memory_as_rvals memory)) ->
    eval_expr env (EVectorLength (rvar "memory")) =
      Some (RVUsize (N.of_nat RUST_MEMORY_SIZE)).
Proof.
  intros env memory Hmemory.
  unfold eval_expr, rvar.
  simpl.
  rewrite Hmemory.
  unfold rust_memory_as_rvals, rust_words_as_rvals.
  rewrite List.length_map, VectorSpec.length_to_list.
  reflexivity.
Qed.

Lemma N_ltb_to_nat :
  forall value bound,
    N.ltb value (N.of_nat bound) =
    Nat.ltb (N.to_nat value) bound.
Proof.
  intros value bound.
  unfold N.ltb.
  rewrite N2Nat.inj_compare.
  rewrite Nat2N.id.
  rewrite Nat.ltb_compare.
  reflexivity.
Qed.

Lemma eval_memory_address_valid :
  forall env memory address,
    lookup "memory" env =
      Some (RVVec (rust_memory_as_rvals memory)) ->
    eval_expr env
      (ELessThan (rsize (rust_word_value address))
        (EVectorLength (rvar "memory"))) =
      Some (RVBool
        (Nat.ltb (N.to_nat address) RUST_MEMORY_SIZE)).
Proof.
  intros env memory address Hmemory.
  cbn [eval_expr rsize rconst rvar].
  rewrite Hmemory.
  unfold rust_memory_as_rvals, rust_words_as_rvals.
  rewrite List.length_map, VectorSpec.length_to_list.
  rewrite N_ltb_to_nat.
  reflexivity.
Qed.

Lemma nth_error_rust_memory_as_rvals :
  forall memory (address : RustWord)
    (bound : N.to_nat (rust_word_value address) < RUST_MEMORY_SIZE),
    nth_error (rust_memory_as_rvals memory) (N.to_nat (rust_word_value address)) =
      Some (rust_word_value_as_rval
        (Vector.nth memory (Fin.of_nat_lt bound))).
Proof.
  intros memory [address Haddress] bound.
  simpl in *.
  unfold rust_memory_as_rvals, rust_words_as_rvals.
  rewrite List.nth_error_map.
  rewrite (@List.nth_error_nth' RustWord (Vector.to_list memory)
    (N.to_nat address) rust_word_zero).
  2: {
    rewrite VectorSpec.length_to_list.
    exact bound.
  }
  pose proof (@VectorSpec.to_list_nth_order RustWord RUST_MEMORY_SIZE memory
    (N.to_nat address) bound rust_word_zero) as Hnth.
  rewrite <- Hnth.
  reflexivity.
Qed.

Lemma eval_memory_index_valid :
  forall env memory (address : RustWord)
    (bound : N.to_nat (rust_word_value address) < RUST_MEMORY_SIZE),
    lookup "memory" env =
      Some (RVVec (rust_memory_as_rvals memory)) ->
    eval_expr env
      (EVectorIndex (rvar "memory")
        (rsize (rust_word_value address))) =
      Some (rust_word_value_as_rval
        (Vector.nth memory (Fin.of_nat_lt bound))).
Proof.
  intros env memory address bound Hmemory.
  cbn [eval_expr rvar rsize rconst].
  rewrite Hmemory.
  apply nth_error_rust_memory_as_rvals.
Qed.

Lemma vector_replace_to_list_at :
  forall (A : Type) position size (values : Vector.t A size)
    (bound : position < size) replacement,
    Vector.to_list (Vector.replace values (Fin.of_nat_lt bound) replacement) =
    List.app (List.firstn position (Vector.to_list values))
      (replacement :: List.skipn (S position) (Vector.to_list values)).
Proof.
  intros A position.
  induction position as [|position IH];
    intros size values bound replacement.
  - destruct size as [|size].
    + lia.
    + destruct values as [|head size' tail].
      * simpl in bound. lia.
      * simpl. reflexivity.
  - destruct size as [|size].
    + lia.
    + destruct values as [|head size' tail].
      * simpl in bound. lia.
      * change
          (head :: Vector.to_list
            (Vector.replace tail
              (Fin.of_nat_lt
                (proj2 (Nat.succ_lt_mono position size') bound))
              replacement) =
           head :: List.app (List.firstn position (Vector.to_list tail))
             (replacement ::
               List.skipn (S position) (Vector.to_list tail))).
        rewrite (IH size' tail
          (proj2 (Nat.succ_lt_mono position size') bound) replacement).
        reflexivity.
Qed.

Lemma rust_memory_replace_rvals :
  forall memory position
    (bound : position < RUST_MEMORY_SIZE) replacement,
    rust_memory_as_rvals
      (Vector.replace memory (Fin.of_nat_lt bound) replacement) =
    List.app
      (List.firstn position (rust_memory_as_rvals memory))
      (rust_word_value_as_rval replacement ::
        List.skipn (S position) (rust_memory_as_rvals memory)).
Proof.
  intros memory position bound replacement.
  unfold rust_memory_as_rvals, rust_words_as_rvals.
  rewrite vector_replace_to_list_at.
  rewrite List.map_app.
  rewrite List.firstn_map, List.skipn_map.
  reflexivity.
Qed.

Lemma eval_memory_replace_valid :
  forall env memory address
    (bound : N.to_nat (rust_word_value address) < RUST_MEMORY_SIZE)
    word,
    lookup "memory" env =
      Some (RVVec (rust_memory_as_rvals memory)) ->
    lookup "$stored" env = Some (rust_word_value_as_rval word) ->
    eval_expr env
      (EVectorReplace (rvar "memory")
        (rsize (rust_word_value address)) (rvar "$stored")) =
    Some
      (RVVec
        (rust_memory_as_rvals
          (Vector.replace memory (Fin.of_nat_lt bound) word))).
Proof.
  intros env memory address bound word Hmemory Hstored.
  cbn [eval_expr rvar rsize rconst].
  rewrite Hmemory, Hstored.
  rewrite (@List.nth_error_nth' rval
    (rust_memory_as_rvals memory)
    (N.to_nat (rust_word_value address)) RVUnit).
  2: {
    unfold rust_memory_as_rvals, rust_words_as_rvals.
    rewrite List.length_map, VectorSpec.length_to_list.
    exact bound.
  }
  rewrite rust_memory_replace_rvals.
  reflexivity.
Qed.

Theorem load_invalid_address_simulation :
  forall code_length pc memory stack_values
    (stack_bound : List.length stack_values <= RUST_STACK_CAPACITY)
    (address : RustWord) env,
    RUST_MEMORY_SIZE <= N.to_nat (rust_word_value address) ->
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := stack_values;
                          rust_stack_bounded := stack_bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TLoadChecked address)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := stack_values;
                            rust_stack_bounded := stack_bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 8 (lower_target_step code_length (TLoadChecked address)) env).
Proof.
  intros code_length pc memory stack_values stack_bound address env
    Hinvalid Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := stack_values;
                        rust_stack_bounded := stack_bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Haddress :
    eval_expr env
      (ELessThan (rsize (rust_word_value address))
        (EVectorLength (rvar "memory"))) =
    Some (RVBool false)).
  {
    rewrite (eval_memory_address_valid env memory address Hmemory).
    f_equal.
    f_equal.
    apply (proj2 (Nat.ltb_ge _ _)).
    exact Hinvalid.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 7 (rvar "halted") RSkip
    (lower_target_instruction code_length (TLoadChecked address)) env Hflag).
  unfold lower_target_instruction, load_instruction.
  rewrite (exec_if_false 6
    (ELessThan (rsize (rust_word_value address))
      (EVectorLength (rvar "memory")))
    (RSeq
      (RLet "$loaded"
        (EVectorIndex (rvar "memory")
          (rsize (rust_word_value address)))
        )
      (stack_has_room
        (RSeq (RPush "stack" (rvar "$loaded")) advance_pc)
        1%N))
    (trap_stmt 3%N) env Haddress).
  rewrite exec_trap_stmt by lia.
  unfold target_eval, rust_memory_load_word.
  simpl.
  destruct (Compare_dec.lt_dec
    (N.to_nat (rust_word_value address)) RUST_MEMORY_SIZE)
    as [Hvalid|Hinvalid_again].
  - exfalso. lia.
  - apply StepOutcomeFailure with
      (error := RustMemoryOutOfBounds) (state := state0)
      (env := update "$trap" (RVUsize 3%N) env).
    + unfold state0. apply st_rel_trap_update. exact Hstate.
    + apply lookup_update_same.
Qed.

Theorem load_stack_overflow_simulation :
  forall code_length pc memory stack_values
    (stack_bound : List.length stack_values <= RUST_STACK_CAPACITY)
    (address : RustWord) env
    (address_bound :
      N.to_nat (rust_word_value address) < RUST_MEMORY_SIZE),
    List.length stack_values = RUST_STACK_CAPACITY ->
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := stack_values;
                          rust_stack_bounded := stack_bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TLoadChecked address)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := stack_values;
                            rust_stack_bounded := stack_bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 12 (lower_target_step code_length (TLoadChecked address)) env).
Proof.
  intros code_length pc memory stack_values stack_bound address env
    address_bound Hfull Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := stack_values;
                        rust_stack_bounded := stack_bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Haddress :
    eval_expr env
      (ELessThan (rsize (rust_word_value address))
        (EVectorLength (rvar "memory"))) =
    Some (RVBool true)).
  {
    rewrite (eval_memory_address_valid env memory address Hmemory).
    f_equal.
    f_equal.
    apply (proj2 (Nat.ltb_lt _ _)).
    exact address_bound.
  }
  assert (Hloaded_eval :
    eval_expr env
      (EVectorIndex (rvar "memory")
        (rsize (rust_word_value address))) =
    Some (rust_word_value_as_rval
      (Vector.nth memory (Fin.of_nat_lt address_bound)))).
  { apply eval_memory_index_valid; assumption. }
  set (loaded := rust_word_value_as_rval
    (Vector.nth memory (Fin.of_nat_lt address_bound))).
  set (env1 := update "$loaded" loaded env).
  assert (Hlet :
    exec 9
      (RLet "$loaded"
        (EVectorIndex (rvar "memory")
          (rsize (rust_word_value address)))) env =
    ROk env1 CNormal).
  {
    unfold env1, loaded.
    eapply exec_let_of_evaluated_expression.
    exact Hloaded_eval.
  }
  assert (Hstack1 :
    lookup "stack" env1 = Some (RVVec (rust_words_as_rvals stack_values))).
  {
    unfold env1.
    rewrite (lookup_update_other "stack" "$loaded" loaded env
      ltac:(discriminate)).
    exact Hstack.
  }
  assert (Hroom_eval :
    eval_expr env1
      (ELessThan (EVectorLength (rvar "stack"))
        (rsize (N.of_nat RUST_STACK_CAPACITY))) =
    Some (RVBool false)).
  {
    rewrite (eval_stack_room_rvals env1 (rust_words_as_rvals stack_values)
      Hstack1).
    unfold rust_words_as_rvals.
    rewrite List.length_map, Hfull.
    reflexivity.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 11 (rvar "halted") RSkip
    (lower_target_instruction code_length (TLoadChecked address)) env Hflag).
  unfold lower_target_instruction, load_instruction.
  rewrite (exec_if_true 10
    (ELessThan (rsize (rust_word_value address))
      (EVectorLength (rvar "memory")))
    (RSeq
      (RLet "$loaded"
        (EVectorIndex (rvar "memory")
          (rsize (rust_word_value address))))
      (stack_has_room
        (RSeq (RPush "stack" (rvar "$loaded")) advance_pc)
        1%N))
    (trap_stmt 3%N) env Haddress).
  rewrite (exec_seq_normal 9
    (RLet "$loaded"
      (EVectorIndex (rvar "memory")
        (rsize (rust_word_value address))))
    (stack_has_room
      (RSeq (RPush "stack" (rvar "$loaded")) advance_pc)
      1%N)
    env env1 Hlet).
  unfold stack_has_room at 1.
  rewrite (exec_if_false 8
    (ELessThan (EVectorLength (rvar "stack"))
      (rsize (N.of_nat RUST_STACK_CAPACITY)))
    (RSeq (RPush "stack" (rvar "$loaded")) advance_pc)
    (trap_stmt 1%N) env1 Hroom_eval).
  rewrite exec_trap_stmt by lia.
  unfold target_eval, rust_memory_load_word.
  simpl.
  destruct (Compare_dec.lt_dec
    (N.to_nat (rust_word_value address)) RUST_MEMORY_SIZE)
    as [Hvalid|Hinvalid].
  2: { exfalso. lia. }
  rewrite (rust_stack_push_at_capacity_overflows
    (Vector.nth memory (Fin.of_nat_lt Hvalid))
    {| rust_stack_values := stack_values;
       rust_stack_bounded := stack_bound |} Hfull).
  apply StepOutcomeFailure with
    (error := RustStackOverflow) (state := state0)
    (env := update "$trap" (RVUsize 1%N) env1).
  - unfold state0, env1.
    apply st_rel_trap_update.
    eapply st_rel_update_private; try exact Hstate; discriminate.
  - apply lookup_update_same.
Qed.

Theorem load_instruction_success_simulation :
  forall code_length pc memory stack_values
    (stack_bound : List.length stack_values <= RUST_STACK_CAPACITY)
    (address : RustWord) env
    (address_bound :
      N.to_nat (rust_word_value address) < RUST_MEMORY_SIZE),
    (List.length stack_values < RUST_STACK_CAPACITY)%nat ->
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := stack_values;
                          rust_stack_bounded := stack_bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TLoadChecked address)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := stack_values;
                            rust_stack_bounded := stack_bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 16 (lower_target_step code_length (TLoadChecked address)) env).
Proof.
  intros code_length pc memory stack_values stack_bound address env
    address_bound Hroom Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := stack_values;
                        rust_stack_bounded := stack_bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Haddress :
    eval_expr env
      (ELessThan (rsize (rust_word_value address))
        (EVectorLength (rvar "memory"))) =
    Some (RVBool true)).
  {
    rewrite (eval_memory_address_valid env memory address Hmemory).
    f_equal.
    f_equal.
    apply (proj2 (Nat.ltb_lt _ _)).
    exact address_bound.
  }
  assert (Hloaded_eval :
    eval_expr env
      (EVectorIndex (rvar "memory")
        (rsize (rust_word_value address))) =
    Some (rust_word_value_as_rval
      (Vector.nth memory (Fin.of_nat_lt address_bound)))).
  { apply eval_memory_index_valid; assumption. }
  set (loaded := rust_word_value_as_rval
    (Vector.nth memory (Fin.of_nat_lt address_bound))).
  set (env1 := update "$loaded" loaded env).
  assert (Hlet :
    exec 13
      (RLet "$loaded"
        (EVectorIndex (rvar "memory")
          (rsize (rust_word_value address)))) env =
    ROk env1 CNormal).
  {
    unfold env1, loaded.
    eapply exec_let_of_evaluated_expression.
    exact Hloaded_eval.
  }
  assert (Hstack1 :
    lookup "stack" env1 = Some (RVVec (rust_words_as_rvals stack_values))).
  {
    unfold env1.
    rewrite (lookup_update_other "stack" "$loaded" loaded env
      ltac:(discriminate)).
    exact Hstack.
  }
  set (stack1 := rust_stack_with_push
    (Vector.nth memory (Fin.of_nat_lt address_bound))
    {| rust_stack_values := stack_values;
       rust_stack_bounded := stack_bound |} Hroom).
  set (env2 := update "stack"
    (RVVec (loaded :: rust_words_as_rvals stack_values)) env1).
  assert (Hpush :
    exec 11 (RPush "stack" (rvar "$loaded")) env1 =
      ROk env2 CNormal).
  {
    unfold env2.
    apply exec_push_expression with
      (values := rust_words_as_rvals stack_values)
      (value := loaded).
    - exact Hstack1.
    - unfold loaded.
      cbn [eval_expr rvar].
      apply lookup_update_same.
  }
  assert (Hrel1 :
    st_rel (rust_state_with_stack state0 stack1) env2).
  {
    unfold env2, loaded, stack1.
    apply st_rel_update_stack.
    unfold state0.
    apply st_rel_update_private with (name := "$loaded") (value := loaded);
      try assumption; discriminate.
  }
  assert (Hpc_eval :
    eval_expr env2 (EWrapAdd (rvar "pc") (rword rust_word_one)) =
      Some (rust_word_value_as_rval (rust_word_wrap (pc + 1)))).
  {
    rewrite (eval_pc_advance (rust_state_with_stack state0 stack1) env2 Hrel1).
    replace (rust_word_value rust_word_one) with 1%N by reflexivity.
    rewrite <- rust_pc_advance_rval_matches.
    reflexivity.
  }
  set (pc1 := rust_word_wrap (pc + 1)).
  set (env3 := update "pc" (rust_word_value_as_rval pc1) env2).
  assert (Hadvance : exec 11 advance_pc env2 = ROk env3 CNormal).
  {
    unfold advance_pc, env3, pc1.
    eapply exec_let_of_evaluated_expression.
    exact Hpc_eval.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 15 (rvar "halted") RSkip
    (lower_target_instruction code_length (TLoadChecked address)) env Hflag).
  unfold lower_target_instruction, load_instruction.
  rewrite (exec_if_true 14
    (ELessThan (rsize (rust_word_value address))
      (EVectorLength (rvar "memory")))
    (RSeq
      (RLet "$loaded"
        (EVectorIndex (rvar "memory")
          (rsize (rust_word_value address))))
      (stack_has_room
        (RSeq (RPush "stack" (rvar "$loaded")) advance_pc)
        1%N))
    (trap_stmt 3%N) env Haddress).
  rewrite (exec_seq_normal 13
    (RLet "$loaded"
      (EVectorIndex (rvar "memory")
        (rsize (rust_word_value address))))
    (stack_has_room
      (RSeq (RPush "stack" (rvar "$loaded")) advance_pc)
      1%N)
    env env1 Hlet).
  rewrite (exec_stack_has_room_rvals 12
    (rust_words_as_rvals stack_values)
    (RSeq (RPush "stack" (rvar "$loaded")) advance_pc)
    1%N env1 Hstack1).
  2: {
    unfold rust_words_as_rvals.
    rewrite List.length_map.
    exact Hroom.
  }
  rewrite (exec_seq_normal 11
    (RPush "stack" (rvar "$loaded")) advance_pc env1 env2 Hpush).
  rewrite Hadvance.
  unfold target_eval, rust_memory_load_word.
  simpl.
  destruct (Compare_dec.lt_dec
    (N.to_nat (rust_word_value address)) RUST_MEMORY_SIZE)
    as [Hvalid|Hinvalid].
  2: { exfalso. lia. }
  unfold rust_stack_push.
  simpl.
  destruct (Compare_dec.lt_dec
    (List.length stack_values) RUST_STACK_CAPACITY)
    as [Hpush_room|Hpush_full].
  2: { exfalso. lia. }
  assert (Hindex :
    Fin.of_nat_lt Hvalid = Fin.of_nat_lt address_bound).
  {
    apply Fin.to_nat_inj.
    rewrite !Fin.to_nat_of_nat.
    reflexivity.
  }
  rewrite Hindex.
  assert (Hrel_loaded : st_rel state0 env1).
  {
    unfold env1.
    eapply st_rel_update_private; try exact Hstate; discriminate.
  }
  assert (Hrel_stack :
    st_rel
      (rust_state_with_stack state0
        (rust_stack_with_push
          (Vector.nth memory (Fin.of_nat_lt Hvalid))
          {| rust_stack_values := stack_values;
             rust_stack_bounded := stack_bound |} Hpush_room))
      env2).
  {
    unfold env2, loaded.
    rewrite Hindex.
    apply st_rel_update_stack.
    exact Hrel_loaded.
  }
  apply StepOutcomeSuccess.
  unfold target_advance_pc.
  apply st_rel_update_pc.
  rewrite <- Hindex.
  exact Hrel_stack.
Qed.

Theorem store_invalid_address_simulation :
  forall code_length state env (address : RustWord),
    RUST_MEMORY_SIZE <= N.to_nat (rust_word_value address) ->
    rust_status state = RustRunning ->
    st_rel state env ->
    step_outcome_rel
      (target_eval code_length (TStoreChecked address) state)
      (exec 8 (lower_target_step code_length (TStoreChecked address)) env).
Proof.
  intros code_length state env address Hinvalid Hrunning Hrel.
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { eapply eval_running_flag; eassumption. }
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  assert (Haddress :
    eval_expr env
      (ELessThan (rsize (rust_word_value address))
        (EVectorLength (rvar "memory"))) = Some (RVBool false)).
  {
    rewrite (eval_memory_address_valid env (rust_memory state) address
      Hmemory).
    f_equal. f_equal.
    apply (proj2 (Nat.ltb_ge _ _)).
    exact Hinvalid.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 7 (rvar "halted") RSkip
    (lower_target_instruction code_length (TStoreChecked address)) env Hflag).
  unfold lower_target_instruction, store_instruction.
  rewrite (exec_if_false 6
    (ELessThan (rsize (rust_word_value address))
      (EVectorLength (rvar "memory")))
    (guard_not_empty "stack" 2%N
      (RSeq
        (RPop "stack" "$stored" (rword rust_word_zero))
        (RSeq
          (RLet "memory"
            (EVectorReplace (rvar "memory")
              (rsize (rust_word_value address))
              (rvar "$stored")))
          advance_pc)))
    (trap_stmt 3%N) env Haddress).
  rewrite exec_trap_stmt by lia.
  unfold target_eval.
  rewrite Hrunning.
  simpl.
  destruct (Compare_dec.lt_dec
    (N.to_nat (rust_word_value address)) RUST_MEMORY_SIZE)
    as [Hvalid|Hinvalid_again].
  - exfalso. lia.
  - apply StepOutcomeFailure with
      (error := RustMemoryOutOfBounds) (state := state)
      (env := update "$trap" (RVUsize 3%N) env).
    + apply st_rel_trap_update. exact (conj Hpc (conj Hstack (conj Hmemory Hhalted))).
    + apply lookup_update_same.
Qed.

Theorem store_underflow_simulation :
  forall code_length pc memory
    (stack_bound : (0 <= RUST_STACK_CAPACITY)%nat)
    (address : RustWord) env
    (address_bound :
      N.to_nat (rust_word_value address) < RUST_MEMORY_SIZE),
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := [];
                          rust_stack_bounded := stack_bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TStoreChecked address)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := [];
                            rust_stack_bounded := stack_bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 12 (lower_target_step code_length (TStoreChecked address)) env).
Proof.
  intros code_length pc memory stack_bound address env address_bound Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := [];
                        rust_stack_bounded := stack_bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Haddress :
    eval_expr env
      (ELessThan (rsize (rust_word_value address))
        (EVectorLength (rvar "memory"))) = Some (RVBool true)).
  {
    rewrite (eval_memory_address_valid env memory address Hmemory).
    f_equal. f_equal.
    apply (proj2 (Nat.ltb_lt _ _)).
    exact address_bound.
  }
  assert (Hempty : lookup "stack" env = Some (RVVec [])).
  { simpl in Hstack. exact Hstack. }
  unfold lower_target_step.
  rewrite (exec_if_false 11 (rvar "halted") RSkip
    (lower_target_instruction code_length (TStoreChecked address)) env Hflag).
  unfold lower_target_instruction, store_instruction.
  rewrite (exec_if_true 10
    (ELessThan (rsize (rust_word_value address))
      (EVectorLength (rvar "memory")))
    (guard_not_empty "stack" 2%N
      (RSeq
        (RPop "stack" "$stored" (rword rust_word_zero))
        (RSeq
          (RLet "memory"
            (EVectorReplace (rvar "memory")
              (rsize (rust_word_value address))
              (rvar "$stored")))
          advance_pc)))
    (trap_stmt 3%N) env Haddress).
  rewrite (exec_guard_empty_stack 9 2%N
    (RSeq
      (RPop "stack" "$stored" (rword rust_word_zero))
      (RSeq
        (RLet "memory"
          (EVectorReplace (rvar "memory")
            (rsize (rust_word_value address))
            (rvar "$stored")))
        advance_pc))
    env ltac:(lia) Hempty).
  unfold target_eval.
  simpl.
  destruct (Compare_dec.lt_dec
    (N.to_nat (rust_word_value address)) RUST_MEMORY_SIZE)
    as [Hvalid|Hinvalid].
  2: { exfalso. lia. }
  apply StepOutcomeFailure with
    (error := RustStackUnderflow) (state := state0)
    (env := update "$trap" (RVUsize 2%N) env).
  - unfold state0. apply st_rel_trap_update. exact Hstate.
  - apply lookup_update_same.
Qed.

Theorem store_success_simulation :
  forall code_length pc memory head tail
    (stack_bound : List.length (head :: tail) <= RUST_STACK_CAPACITY)
    (address : RustWord) env
    (address_bound :
      N.to_nat (rust_word_value address) < RUST_MEMORY_SIZE),
    st_rel
      {| rust_pc := pc;
         rust_stack := {| rust_stack_values := head :: tail;
                          rust_stack_bounded := stack_bound |};
         rust_memory := memory;
         rust_status := RustRunning |}
      env ->
    step_outcome_rel
      (target_eval code_length (TStoreChecked address)
        {| rust_pc := pc;
           rust_stack := {| rust_stack_values := head :: tail;
                            rust_stack_bounded := stack_bound |};
           rust_memory := memory;
           rust_status := RustRunning |})
      (exec 20 (lower_target_step code_length (TStoreChecked address)) env).
Proof.
  intros code_length pc memory head tail stack_bound address env
    address_bound Hrel.
  destruct Hrel as [Hpc [Hstack [Hmemory Hhalted]]].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack := {| rust_stack_values := head :: tail;
                        rust_stack_bounded := stack_bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. repeat split; assumption. }
  assert (Hflag : eval_expr env (rvar "halted") = Some (RVBool false)).
  { apply eval_running_flag with (state := state0); [exact Hstate|reflexivity]. }
  assert (Haddress :
    eval_expr env
      (ELessThan (rsize (rust_word_value address))
        (EVectorLength (rvar "memory"))) = Some (RVBool true)).
  {
    rewrite (eval_memory_address_valid env memory address Hmemory).
    f_equal. f_equal.
    apply (proj2 (Nat.ltb_lt _ _)).
    exact address_bound.
  }
  assert (Hstack0 :
    lookup "stack" env =
      Some (RVVec (rust_word_value_as_rval head ::
        rust_words_as_rvals tail))).
  { exact Hstack. }
  pose proof stack_bound as Htail_bound.
  simpl in Htail_bound.
  set (stack1 := rust_stack_with_tail tail Htail_bound).
  set (env1 :=
    update "$stored" (rust_word_value_as_rval head)
      (update "stack" (RVVec (rust_words_as_rvals tail)) env)).
  assert (Hpop :
    exec 16 (RPop "stack" "$stored" (rword rust_word_zero)) env =
    ROk env1 CNormal).
  {
    unfold env1.
    apply exec_pop_nonempty_stack.
    exact Hstack0.
  }
  assert (Hstate1 :
    st_rel (rust_state_with_stack state0 stack1) env1).
  {
    unfold env1, stack1.
    apply st_rel_update_private with
      (name := "$stored") (value := rust_word_value_as_rval head).
    - apply st_rel_update_stack.
      exact Hstate.
    - discriminate.
    - discriminate.
    - discriminate.
    - discriminate.
  }
  assert (Hmemory1 :
    lookup "memory" env1 = Some (RVVec (rust_memory_as_rvals memory))).
  {
    unfold env1.
    rewrite (lookup_update_other "memory" "$stored"
      (rust_word_value_as_rval head)
      (update "stack" (RVVec (rust_words_as_rvals tail)) env)
      ltac:(discriminate)).
    rewrite (lookup_update_other "memory" "stack"
      (RVVec (rust_words_as_rvals tail)) env ltac:(discriminate)).
    exact Hmemory.
  }
  assert (Hstored :
    lookup "$stored" env1 = Some (rust_word_value_as_rval head)).
  { unfold env1. apply lookup_update_same. }
  set (memory1 :=
    Vector.replace memory (Fin.of_nat_lt address_bound) head).
  set (env2 := update "memory" (RVVec (rust_memory_as_rvals memory1)) env1).
  assert (Hreplace_eval :
    eval_expr env1
      (EVectorReplace (rvar "memory")
        (rsize (rust_word_value address)) (rvar "$stored")) =
    Some (RVVec (rust_memory_as_rvals memory1))).
  {
    unfold memory1.
    apply eval_memory_replace_valid; assumption.
  }
  assert (Hmemory_let :
    exec 15
      (RLet "memory"
        (EVectorReplace (rvar "memory")
          (rsize (rust_word_value address))
          (rvar "$stored"))) env1 =
    ROk env2 CNormal).
  {
    unfold env2.
    eapply exec_let_of_evaluated_expression.
    exact Hreplace_eval.
  }
  assert (Hstate2 :
    st_rel (rust_state_with_memory
      (rust_state_with_stack state0 stack1) memory1) env2).
  {
    unfold env2, memory1.
    apply st_rel_update_memory.
    exact Hstate1.
  }
  assert (Hpc_eval :
    eval_expr env2 (EWrapAdd (rvar "pc") (rword rust_word_one)) =
      Some (rust_word_value_as_rval (rust_word_wrap (pc + 1)))).
  {
    rewrite (eval_pc_advance
      (rust_state_with_memory
        (rust_state_with_stack state0 stack1) memory1)
      env2 Hstate2).
    replace (rust_word_value rust_word_one) with 1%N by reflexivity.
    rewrite <- rust_pc_advance_rval_matches.
    reflexivity.
  }
  set (pc1 := rust_word_wrap (pc + 1)).
  set (env3 := update "pc" (rust_word_value_as_rval pc1) env2).
  assert (Hadvance : exec 15 advance_pc env2 = ROk env3 CNormal).
  {
    unfold advance_pc, env3, pc1.
    eapply exec_let_of_evaluated_expression.
    exact Hpc_eval.
  }
  unfold lower_target_step.
  rewrite (exec_if_false 19 (rvar "halted") RSkip
    (lower_target_instruction code_length (TStoreChecked address)) env Hflag).
  unfold lower_target_instruction, store_instruction.
  rewrite (exec_if_true 18
    (ELessThan (rsize (rust_word_value address))
      (EVectorLength (rvar "memory")))
    (guard_not_empty "stack" 2%N
      (RSeq
        (RPop "stack" "$stored" (rword rust_word_zero))
        (RSeq
          (RLet "memory"
            (EVectorReplace (rvar "memory")
              (rsize (rust_word_value address))
              (rvar "$stored")))
          advance_pc)))
    (trap_stmt 3%N) env Haddress).
  rewrite (exec_guard_nonempty_stack 17
    (rust_word_value_as_rval head) (rust_words_as_rvals tail)
    2%N
    (RSeq
      (RPop "stack" "$stored" (rword rust_word_zero))
      (RSeq
        (RLet "memory"
          (EVectorReplace (rvar "memory")
            (rsize (rust_word_value address))
            (rvar "$stored")))
        advance_pc))
    env Hstack0).
  rewrite (exec_seq_normal 16
    (RPop "stack" "$stored" (rword rust_word_zero))
    (RSeq
      (RLet "memory"
        (EVectorReplace (rvar "memory")
          (rsize (rust_word_value address))
          (rvar "$stored")))
      advance_pc)
    env env1 Hpop).
  rewrite (exec_seq_normal 15
    (RLet "memory"
      (EVectorReplace (rvar "memory")
        (rsize (rust_word_value address))
        (rvar "$stored")))
    advance_pc env1 env2 Hmemory_let).
  rewrite Hadvance.
  unfold target_eval.
  simpl.
  destruct (Compare_dec.lt_dec
    (N.to_nat (rust_word_value address)) RUST_MEMORY_SIZE)
    as [Hvalid|Hinvalid].
  2: { exfalso. lia. }
  assert (Hindex :
    Fin.of_nat_lt Hvalid = Fin.of_nat_lt address_bound).
  {
    apply Fin.to_nat_inj.
    rewrite !Fin.to_nat_of_nat.
    reflexivity.
  }
  rewrite Hindex.
  unfold target_advance_pc.
  apply StepOutcomeSuccess.
  apply st_rel_update_pc.
  exact Hstate2.
Qed.


Theorem lower_program_step_from_instruction_simulation :
  forall program state env index instruction next instruction_fuel next_env,
    rust_status state = RustRunning ->
    st_rel state env ->
    N.to_nat (rust_word_value (rust_pc state)) = index ->
    nth_error program index = Some instruction ->
    target_eval (List.length program) instruction state = Success next ->
    exec (S instruction_fuel)
      (lower_target_step (List.length program) instruction) env =
      ROk next_env CNormal ->
    st_rel next next_env ->
    exec (S (S (index + instruction_fuel)))
      (lower_target_program_step program) env =
      ROk next_env CNormal.
Proof.
  intros program state env index instruction next instruction_fuel next_env
    Hrunning Hrel Hpc Hfetch Htarget Hinstruction Hnext.
  assert (Hhalted :
    eval_expr env (rvar "halted") = Some (RVBool false)).
  { eapply eval_running_flag; eassumption. }
  assert (Hguards :
    forall offset, offset <= index ->
      lower_fetch_guard env offset index).
  {
    intros offset Hoff.
    eapply lower_fetch_guard_from_st_rel; eassumption.
  }
  unfold lower_target_program_step.
  rewrite (exec_if_false
    (S (index + instruction_fuel))
    (rvar "halted") RSkip
    (lower_fetch (List.length program) 0 program)
    env Hhalted).
  rewrite (lower_fetch_dispatch_at_index
    (List.length program) 0 index program instruction env
    instruction_fuel Hfetch).
  2: {
    intros offset Hoff.
    specialize (Hguards offset Hoff) as [Hbound Hequal].
    unfold lower_fetch_guard in *.
    replace (0 + offset) with offset in * by lia.
    replace (0 + index) with index in * by lia.
    exact (conj Hbound Hequal).
  }
  unfold lower_target_step in Hinstruction.
  rewrite (exec_if_false instruction_fuel
    (rvar "halted") RSkip
    (lower_target_instruction (List.length program) instruction)
    env Hhalted) in Hinstruction.
  exact Hinstruction.
Qed.

Theorem target_eval_running_simulation :
  forall code_length instruction state env,
    rust_status state = RustRunning ->
    st_rel state env ->
    exists fuel,
      step_outcome_rel
        (target_eval code_length instruction state)
        (exec fuel (lower_target_step code_length instruction) env).
Proof.
  intros code_length instruction
    [pc [values stack_bound] memory status] env Hrunning Hrel.
  simpl in Hrunning.
  destruct status; [|discriminate].
  set (state0 :=
    {| rust_pc := pc;
       rust_stack :=
         {| rust_stack_values := values;
            rust_stack_bounded := stack_bound |};
       rust_memory := memory;
       rust_status := RustRunning |}).
  assert (Hstate : st_rel state0 env).
  { unfold state0, st_rel. simpl. exact Hrel. }
  unfold state0 in Hstate.
  simpl in Hstate.
  pose proof (proj1 (proj2 Hstate)) as Hstack_env.
  destruct instruction as [word| | | | |address|address|target|target|].
  -
    destruct (Compare_dec.lt_dec (List.length values) RUST_STACK_CAPACITY)
      as [Hroom|Hfull].
    + exists 8.
      eapply push_instruction_success_simulation; eauto.
    + assert (Hcapacity : List.length values = RUST_STACK_CAPACITY) by lia.
      exists 8.
      eapply push_capacity_overflow_simulation; eauto.
  - destruct values as [|right [|left tail]].
    + exists 16.
    eapply binary_first_pop_underflow_simulation; eauto.
    + exists 16.
      eapply binary_second_pop_underflow_simulation; eauto.
    + exists 16.
      eapply binary_success_simulation; eauto.
  - destruct values as [|right [|left tail]].
    + exists 16.
      eapply binary_first_pop_underflow_simulation; eauto.
    + exists 16.
      eapply binary_second_pop_underflow_simulation; eauto.
    + exists 16.
      eapply binary_success_simulation; eauto.
  - destruct values as [|head tail].
    + exists 12.
      eapply duplicate_empty_simulation; eauto.
    + exists 12.
      destruct (Compare_dec.lt_dec
        (S (List.length tail)) RUST_STACK_CAPACITY)
        as [Hroom|Hfull].
      * eapply duplicate_nonempty_simulation; eauto.
      * assert (Hcapacity :
          S (List.length tail) = RUST_STACK_CAPACITY).
        { unfold RUST_STACK_CAPACITY in *.
          simpl in stack_bound.
          lia. }
        eapply duplicate_capacity_overflow_simulation; eauto.
  - destruct values as [|head tail].
    + exists 8.
      eapply drop_empty_simulation; eauto.
    + exists 8.
      eapply drop_nonempty_simulation; eauto.
  - destruct (Compare_dec.lt_dec
      (N.to_nat (rust_word_value address)) RUST_MEMORY_SIZE)
      as [Hvalid|Hinvalid].
    + destruct (Compare_dec.lt_dec
        (List.length values) RUST_STACK_CAPACITY)
        as [Hroom|Hfull].
      * exists 16.
        eapply load_instruction_success_simulation; eauto.
      * assert (Hcapacity :
          List.length values = RUST_STACK_CAPACITY) by lia.
        exists 12.
        eapply load_stack_overflow_simulation; eauto.
    + assert (Hout : RUST_MEMORY_SIZE <=
        N.to_nat (rust_word_value address)) by lia.
      exists 8.
      eapply load_invalid_address_simulation; eauto.
  - destruct (Compare_dec.lt_dec
      (N.to_nat (rust_word_value address)) RUST_MEMORY_SIZE)
      as [Hvalid|Hinvalid].
    + destruct values as [|head tail].
      * exists 12.
        eapply store_underflow_simulation; eauto.
      * exists 20.
        eapply store_success_simulation; eauto.
    + assert (Hout : RUST_MEMORY_SIZE <=
        N.to_nat (rust_word_value address)) by lia.
      exists 8.
      eapply store_invalid_address_simulation; eauto.
  - destruct (target_valid_pc code_length target) eqn:Htarget.
    + exists 8.
      eapply jump_valid_simulation; eauto.
    + exists 8.
      eapply jump_invalid_simulation; eauto.
  - destruct values as [|condition tail].
    + exists 8.
      eapply jump_zero_underflow_simulation; eauto.
    + exists 20.
      eapply jump_zero_nonempty_simulation; eauto.
  - exists 4.
    unfold lower_target_step.
    rewrite (exec_if_false 3 (rvar "halted") RSkip
      (lower_target_instruction code_length THalt) env).
    2: { apply eval_running_flag with
          (state := state0); [exact Hstate|reflexivity]. }
    unfold lower_target_instruction.
    simpl.
    unfold target_eval.
    simpl.
    apply StepOutcomeSuccess.
    unfold st_rel, rust_state_with_status.
    simpl.
    destruct Hstate as [Hpc [Hstack [Hmemory Hhalted]]].
    simpl in Hpc, Hstack, Hmemory.
    split.
    + rewrite (lookup_update_other "pc" "halted" _ env
        ltac:(discriminate)).
      exact Hpc.
    + split.
      * rewrite (lookup_update_other "stack" "halted" _ env
          ltac:(discriminate)).
        exact Hstack.
      * split.
        -- rewrite (lookup_update_other "memory" "halted" _ env
             ltac:(discriminate)).
           exact Hmemory.
        -- apply lookup_update_same.
Qed.

Theorem target_step_simulation :
  forall program state env next,
    st_rel state env ->
    target_step program state = Success next ->
    exists fuel next_env,
      exec fuel (lower_target_program_step program) env =
        ROk next_env CNormal /\
      st_rel next next_env.
Proof.
  intros program state env next Hrel Hstep.
  destruct (rust_status state) as [|] eqn:Hstatus.
  - unfold target_step in Hstep.
    rewrite Hstatus in Hstep.
    destruct (nth_error program (N.to_nat (rust_word_value (rust_pc state))))
      as [instruction|] eqn:Hfetch.
    + assert (Htarget :
        target_eval (List.length program) instruction state = Success next)
        by exact Hstep.
      destruct
        (target_eval_running_simulation
          (List.length program) instruction state env Hstatus Hrel)
        as [step_fuel Hsimulation].
      rewrite Htarget in Hsimulation.
      destruct step_fuel as [|instruction_fuel].
      * simpl in Hsimulation.
        inversion Hsimulation.
      * assert (Hinstruction :
          exists next_env,
            exec (S instruction_fuel)
              (lower_target_step (List.length program) instruction) env =
                ROk next_env CNormal /\
            st_rel next next_env).
        {
          inversion Hsimulation; subst.
          eexists. split; eauto.
        }
        destruct Hinstruction as [next_env [Hexec Hnext_rel]].
        exists (S (S
          (N.to_nat (rust_word_value (rust_pc state)) +
            instruction_fuel))), next_env.
        split.
        -- eapply lower_program_step_from_instruction_simulation
             with (instruction := instruction)
                  (next := next)
                  (instruction_fuel := instruction_fuel)
                  (next_env := next_env); eauto.
        -- exact Hnext_rel.
    + discriminate.
  - unfold target_step in Hstep.
    rewrite Hstatus in Hstep.
    inversion Hstep; subst next.
    pose proof Hrel as Hrel_keep.
    destruct Hrel as [_ [_ [_ Hhalted]]].
    rewrite Hstatus in Hhalted.
    simpl in Hhalted.
    assert (Hflag :
      eval_expr env (rvar "halted") = Some (RVBool true)).
    { unfold rvar. simpl. exact Hhalted. }
    exists 2, env.
    split.
    + unfold lower_target_program_step.
      rewrite (exec_if_true 1 (rvar "halted") RSkip
        (lower_fetch (List.length program) 0 program) env Hflag).
      reflexivity.
    + exact Hrel_keep.
Qed.
