(* A small, deterministic, fuel-bounded model of the Rust subset used by the VM. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import String.
From Stdlib Require Import Lia.

Import ListNotations.
Open Scope string_scope.

Definition word_modulus : N := (2 ^ 32)%N.

Definition w32 (value : N) : N := N.modulo value word_modulus.

Definition u32_value := N.

Lemma word_modulus_positive : (0 < word_modulus)%N.
Proof.
  unfold word_modulus.
  vm_compute.
  reflexivity.
Qed.

Theorem w32_range :
  forall value, (w32 value < word_modulus)%N.
Proof.
  intros value.
  unfold w32.
  apply N.mod_lt.
  pose proof word_modulus_positive.
  lia.
Qed.

Theorem w32_idem :
  forall value, w32 (w32 value) = w32 value.
Proof.
  intros value.
  unfold w32.
  apply N.mod_small.
  apply w32_range.
Qed.

Definition u32_of_N (value : N) : u32_value :=
  w32 value.

Inductive rval : Type :=
| RVU32 (value : u32_value)
| RVUsize (value : N)
| RVBool (value : bool)
| RVVec (values : list rval)
| RVUnit.

Definition environment := list (string * rval).

Inductive rexpr : Type :=
| EConst (value : rval)
| EVar (name : string)
| EWrapAdd (lhs rhs : rexpr)
| EWrapSub (lhs rhs : rexpr)
| ECheckedUsizeAdd (maximum : N) (lhs rhs : rexpr)
| ECheckedUsizeSub (lhs rhs : rexpr)
| EEqual (lhs rhs : rexpr)
| EIsEmpty (vector : rexpr)
| EIsZero (value : rexpr)
| ELessThan (lhs rhs : rexpr)
| EVectorLength (vector : rexpr)
| EVectorIndex (vector index : rexpr)
| EVectorReplace (vector index value : rexpr).

Fixpoint lookup (name : string) (env : environment) : option rval :=
  match env with
  | [] => None
  | (key, value) :: tail =>
      if String.eqb name key then Some value else lookup name tail
  end.

Fixpoint update (name : string) (value : rval) (env : environment)
    : environment :=
  match env with
  | [] => [(name, value)]
  | (key, old_value) :: tail =>
      if String.eqb name key
      then (key, value) :: tail
      else (key, old_value) :: update name value tail
  end.

Definition rval_eqb (lhs rhs : rval) : option bool :=
  match lhs, rhs with
  | RVU32 x, RVU32 y => Some (N.eqb x y)
  | RVUsize x, RVUsize y => Some (N.eqb x y)
  | RVBool x, RVBool y => Some (Bool.eqb x y)
  | RVUnit, RVUnit => Some true
  | _, _ => None
  end.

Fixpoint eval_expr (env : environment) (expression : rexpr)
    : option rval :=
  match expression with
  | EConst value => Some value
  | EVar name => lookup name env
  | EWrapAdd lhs rhs =>
      match eval_expr env lhs, eval_expr env rhs with
      | Some (RVU32 x), Some (RVU32 y) =>
          Some (RVU32 (u32_of_N (x + y)))
      | _, _ => None
      end
  | EWrapSub lhs rhs =>
      match eval_expr env lhs, eval_expr env rhs with
      | Some (RVU32 x), Some (RVU32 y) =>
          Some (RVU32 (u32_of_N
            (x + word_modulus - y)))
      | _, _ => None
      end
  | ECheckedUsizeAdd maximum lhs rhs =>
      match eval_expr env lhs, eval_expr env rhs with
      | Some (RVUsize x), Some (RVUsize y) =>
          if (x + y <=? maximum)%N then Some (RVUsize (x + y)) else None
      | _, _ => None
      end
  | ECheckedUsizeSub lhs rhs =>
      match eval_expr env lhs, eval_expr env rhs with
      | Some (RVUsize x), Some (RVUsize y) =>
          if (y <=? x)%N then Some (RVUsize (x - y)) else None
      | _, _ => None
      end
  | EEqual lhs rhs =>
      match eval_expr env lhs, eval_expr env rhs with
      | Some x, Some y =>
          match rval_eqb x y with
          | Some equal => Some (RVBool equal)
          | None => None
          end
      | _, _ => None
      end
  | EIsEmpty vector =>
      match eval_expr env vector with
      | Some (RVVec values) => Some (RVBool (match values with [] => true | _ => false end))
      | _ => None
      end
  | EIsZero value =>
      match eval_expr env value with
      | Some (RVU32 word) => Some (RVBool (N.eqb word 0))
      | Some (RVUsize size) => Some (RVBool (N.eqb size 0))
      | _ => None
      end
  | ELessThan lhs rhs =>
      match eval_expr env lhs, eval_expr env rhs with
      | Some (RVU32 x), Some (RVU32 y) =>
          Some (RVBool (N.ltb x y))
      | Some (RVUsize x), Some (RVUsize y) =>
          Some (RVBool (N.ltb x y))
      | _, _ => None
      end
  | EVectorLength vector =>
      match eval_expr env vector with
      | Some (RVVec values) => Some (RVUsize (N.of_nat (List.length values)))
      | _ => None
      end
  | EVectorIndex vector index =>
      match eval_expr env vector, eval_expr env index with
      | Some (RVVec values), Some (RVU32 offset) =>
          List.nth_error values (N.to_nat offset)
      | Some (RVVec values), Some (RVUsize offset) =>
          List.nth_error values (N.to_nat offset)
      | _, _ => None
      end
  | EVectorReplace vector index value =>
      match eval_expr env vector, eval_expr env index, eval_expr env value with
      | Some (RVVec values), Some (RVU32 offset), Some replacement =>
          let position := N.to_nat offset in
          match List.nth_error values position with
          | Some _ => Some (RVVec (firstn position values ++ replacement ::
              skipn (S position) values))
          | None => None
          end
      | Some (RVVec values), Some (RVUsize offset), Some replacement =>
          let position := N.to_nat offset in
          match List.nth_error values position with
          | Some _ => Some (RVVec (firstn position values ++ replacement ::
              skipn (S position) values))
          | None => None
          end
      | _, _, _ => None
      end
  end.

Inductive rstmt : Type :=
| RSkip
| RSeq (first second : rstmt)
| RLet (name : string) (value : rexpr)
| RPush (vector_name : string) (value : rexpr)
| RPop (vector_name result_name : string) (empty_fallback : rexpr)
| RIf (condition : rexpr) (then_branch else_branch : rstmt)
| RLoop (body : rstmt)
| RBreak
| RReturn (value : option rexpr)
| RTrap.

Inductive control : Type :=
| CNormal
| CBreak
| CRet (value : option rval).

Inductive exec_result : Type :=
| ROk (env : environment) (flow : control)
| RStuck (env : environment)
| RFuel (env : environment).

Fixpoint exec (fuel : nat) (statement : rstmt) (env : environment)
    {struct fuel} : exec_result :=
  match fuel with
  | O => RFuel env
  | S remaining =>
      match statement with
      | RSkip => ROk env CNormal
      | RSeq first second =>
          match exec remaining first env with
          | ROk next_env CNormal => exec remaining second next_env
          | ROk next_env CBreak => ROk next_env CBreak
          | ROk next_env (CRet value) => ROk next_env (CRet value)
          | RStuck next_env => RStuck next_env
          | RFuel next_env => RFuel next_env
          end
      | RLet name expression =>
          match eval_expr env expression with
          | Some value => ROk (update name value env) CNormal
          | None => RStuck env
          end
      | RPush vector_name expression =>
          match lookup vector_name env, eval_expr env expression with
          | Some (RVVec values), Some value =>
              ROk (update vector_name (RVVec (value :: values)) env) CNormal
          | _, _ => RStuck env
          end
      | RPop vector_name result_name fallback =>
          match lookup vector_name env with
          | Some (RVVec (value :: tail)) =>
              ROk (update result_name value
                (update vector_name (RVVec tail) env)) CNormal
          | Some (RVVec []) =>
              match eval_expr env fallback with
              | Some value => ROk (update result_name value env) CNormal
              | None => RStuck env
              end
          | _ => RStuck env
          end
      | RIf condition then_branch else_branch =>
          match eval_expr env condition with
          | Some (RVBool true) => exec remaining then_branch env
          | Some (RVBool false) => exec remaining else_branch env
          | _ => RStuck env
          end
      | RLoop body =>
          match exec remaining body env with
          | ROk next_env CNormal => exec remaining (RLoop body) next_env
          | ROk next_env CBreak => ROk next_env CNormal
          | ROk next_env (CRet value) => ROk next_env (CRet value)
          | RStuck next_env => RStuck next_env
          | RFuel next_env => RFuel next_env
          end
      | RBreak => ROk env CBreak
      | RReturn expression =>
          match expression with
          | None => ROk env (CRet None)
          | Some value =>
              match eval_expr env value with
              | Some result => ROk env (CRet (Some result))
              | None => RStuck env
              end
          end
      | RTrap => RStuck env
      end
  end.

Theorem exec_det :
  forall fuel statement env first second,
    exec fuel statement env = first ->
    exec fuel statement env = second ->
    first = second.
Proof.
  intros fuel statement env first second Hfirst Hsecond.
  congruence.
Qed.

Lemma exec_fuel_mono_aux :
  forall fuel,
    forall statement env larger result,
      fuel <= larger ->
      exec fuel statement env = result ->
      (forall fuel_env, result <> RFuel fuel_env) ->
      exec larger statement env = result.
Proof.
  induction fuel as [|fuel IH];
    intros statement env larger result Hle Hrun Hnotfuel.
  - simpl in Hrun.
    subst result.
    exfalso.
    apply (Hnotfuel env).
    reflexivity.
  - destruct larger as [|larger].
    + lia.
    + destruct statement as
        [|statement1 statement2|s r|s r|s s0 r|r statement1 statement2
         |statement| |o|]; simpl in Hrun |- *.
      * inversion Hrun; reflexivity.
      * destruct (exec fuel statement1 env) as [next_env flow|stuck_env|fuel_env]
          eqn:Hfirst.
        -- destruct flow as [| |returned].
           ++ destruct (exec fuel statement2 next_env) as [next2 flow2|stuck2|fuel2]
                eqn:Hsecond.
              ** inversion Hrun; subst.
                 specialize (IH statement1 env larger (ROk next_env CNormal) ltac:(lia)
                   Hfirst ltac:(intros; discriminate)) as IHfirst.
                 rewrite IHfirst.
                 specialize (IH statement2 next_env larger (ROk next2 flow2)
                   ltac:(lia) Hsecond ltac:(intros; discriminate)) as IHsecond.
                 rewrite IHsecond.
                 reflexivity.
              ** inversion Hrun; subst.
                 specialize (IH statement1 env larger (ROk next_env CNormal) ltac:(lia)
                   Hfirst ltac:(intros; discriminate)) as IHfirst.
                 rewrite IHfirst.
                 specialize (IH statement2 next_env larger (RStuck stuck2)
                   ltac:(lia) Hsecond ltac:(intros; discriminate)) as IHsecond.
                 rewrite IHsecond.
                 reflexivity.
              ** inversion Hrun; subst.
                 exfalso.
                 apply (Hnotfuel fuel2).
                 reflexivity.
           ++ inversion Hrun; subst.
              specialize (IH statement1 env larger (ROk next_env CBreak)
                ltac:(lia) Hfirst ltac:(intros; discriminate)) as IHfirst.
              rewrite IHfirst.
              reflexivity.
           ++ inversion Hrun; subst.
              specialize (IH statement1 env larger (ROk next_env (CRet returned))
                ltac:(lia) Hfirst ltac:(intros; discriminate)) as IHfirst.
              rewrite IHfirst.
              reflexivity.
        -- inversion Hrun; subst.
           specialize (IH statement1 env larger (RStuck stuck_env)
             ltac:(lia) Hfirst ltac:(intros; discriminate)) as IHfirst.
           rewrite IHfirst.
           reflexivity.
        -- inversion Hrun; subst.
           exfalso.
           apply (Hnotfuel fuel_env).
           reflexivity.
      * inversion Hrun; reflexivity.
      * inversion Hrun; reflexivity.
      * inversion Hrun; reflexivity.
      * destruct (eval_expr env r) as [value|] eqn:Heval.
        -- destruct value as [word|size|flag|values|]; try (inversion Hrun; reflexivity).
           destruct flag.
           ++ eapply IH; try eassumption; lia.
           ++ eapply IH; try eassumption; lia.
        -- inversion Hrun; reflexivity.
      * destruct (exec fuel statement env) as [next_env flow|stuck_env|fuel_env]
          eqn:Hbody.
        -- destruct flow as [| |returned].
           ++ inversion Hrun; subst.
              pose proof (IH statement env larger
                (ROk next_env CNormal) ltac:(lia) Hbody
                ltac:(intros; discriminate)) as IHbody.
              rewrite IHbody.
              eapply IH.
              { lia. }
              { reflexivity. }
              exact Hnotfuel.
           ++ inversion Hrun; subst.
              specialize (IH statement env larger (ROk next_env CBreak)
                ltac:(lia) Hbody ltac:(intros; discriminate)) as IHbody.
              rewrite IHbody.
              reflexivity.
           ++ inversion Hrun; subst.
              specialize (IH statement env larger (ROk next_env (CRet returned))
                ltac:(lia) Hbody ltac:(intros; discriminate)) as IHbody.
              rewrite IHbody.
              reflexivity.
        -- inversion Hrun; subst.
           specialize (IH statement env larger (RStuck stuck_env)
             ltac:(lia) Hbody ltac:(intros; discriminate)) as IHbody.
           rewrite IHbody.
           reflexivity.
        -- inversion Hrun; subst.
           exfalso.
           apply (Hnotfuel fuel_env).
           reflexivity.
      * inversion Hrun; reflexivity.
      * destruct o as [expression|].
        -- destruct (eval_expr env expression) as [value|]; inversion Hrun; reflexivity.
        -- inversion Hrun; reflexivity.
      * inversion Hrun; reflexivity.
Qed.

Theorem exec_fuel_mono :
  forall small large statement env result,
    small <= large ->
    exec small statement env = result ->
    (forall fuel_env, result <> RFuel fuel_env) ->
    exec large statement env = result.
Proof.
  intros small large statement env result Hle Hexec Hnotfuel.
  eapply exec_fuel_mono_aux; eauto.
Qed.
