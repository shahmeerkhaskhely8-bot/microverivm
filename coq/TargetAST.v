(* A typed, allocation-free target instruction language and its semantics. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Vectors.Vector.
From MicroVeriVM Require Import RustModel.
From MicroVeriVM Require Import Correspondence.
From MicroVeriVM Require Import CanonicalAST.
From MicroVeriVM Require Import Soundness.

Import ListNotations.

Inductive TargetInstruction : Type :=
| TPush (word : RustWord)
| TAddWrapping
| TSubWrapping
| TDuplicateTop
| TDropTop
| TLoadChecked (address : RustWord)
| TStoreChecked (address : RustWord)
| TJumpChecked (target : RustWord)
| TJumpZeroChecked (target : RustWord)
| THalt.

Definition target_of_canonical
    (instruction : CanonicalInstruction) : TargetInstruction :=
  match instruction with
  | CConst value => TPush value
  | CAdd => TAddWrapping
  | CSub => TSubWrapping
  | CDup => TDuplicateTop
  | CDrop => TDropTop
  | CLoad address => TLoadChecked address
  | CStore address => TStoreChecked address
  | CJmp target => TJumpChecked target
  | CJz target => TJumpZeroChecked target
  | CHalt => THalt
  end.

Definition target_advance_pc (state : RustState) : RustState :=
  rust_state_with_pc state (rust_word_wrap (rust_pc state + 1)).

Definition target_valid_pc (code_length : nat) (target : RustWord) : bool :=
  Nat.ltb (N.to_nat target) code_length.

Definition target_binary
    (is_add : bool) (state : RustState) : RustResult :=
  match rust_stack_pop (rust_stack state) with
  | RustPopFailure error _ => Failure error state
  | RustPopSuccess right_value after_right =>
      let state_after_right := rust_state_with_stack state after_right in
      match rust_stack_pop after_right with
      | RustPopFailure error _ => Failure error state_after_right
      | RustPopSuccess left_value after_left =>
          let result :=
            if is_add then rust_wrapping_add left_value right_value
            else rust_wrapping_sub left_value right_value in
          match rust_stack_push result after_left with
          | RustPushSuccess stack =>
              Success (target_advance_pc (rust_state_with_stack state stack))
          | RustPushFailure error _ =>
              Failure error (rust_state_with_stack state after_left)
          end
      end
  end.

Definition target_eval
    (code_length : nat)
    (instruction : TargetInstruction)
    (state : RustState) : RustResult :=
  match rust_status state with
  | RustHalted => Success state
  | RustRunning =>
      match instruction with
      | TPush word =>
          match rust_stack_push word (rust_stack state) with
          | RustPushSuccess stack =>
              Success (target_advance_pc (rust_state_with_stack state stack))
          | RustPushFailure error _ => Failure error state
          end
      | TDropTop =>
          match rust_stack_pop (rust_stack state) with
          | RustPopSuccess _ stack =>
              Success (target_advance_pc (rust_state_with_stack state stack))
          | RustPopFailure error _ => Failure error state
          end
      | TDuplicateTop =>
          match rust_stack_values (rust_stack state) with
          | [] => Failure RustStackUnderflow state
          | word :: _ =>
              match rust_stack_push word (rust_stack state) with
              | RustPushSuccess stack =>
                  Success (target_advance_pc (rust_state_with_stack state stack))
              | RustPushFailure error _ => Failure error state
              end
          end
      | TAddWrapping => target_binary true state
      | TSubWrapping => target_binary false state
      | TLoadChecked address =>
          match rust_memory_load_word (rust_memory state) address with
          | None => Failure RustMemoryOutOfBounds state
          | Some word =>
              match rust_stack_push word (rust_stack state) with
              | RustPushSuccess stack =>
                  Success (target_advance_pc (rust_state_with_stack state stack))
              | RustPushFailure error _ => Failure error state
              end
          end
      | TStoreChecked address =>
          match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
          | right _ => Failure RustMemoryOutOfBounds state
          | left bound =>
              match rust_stack_pop (rust_stack state) with
              | RustPopFailure error _ => Failure error state
              | RustPopSuccess word stack =>
                  let memory := Vector.replace (rust_memory state)
                    (Fin.of_nat_lt bound) word in
                  Success (target_advance_pc
                    (rust_state_with_memory
                      (rust_state_with_stack state stack) memory))
              end
          end
      | TJumpChecked target =>
          if target_valid_pc code_length target then
            Success (rust_state_with_pc state target)
          else Failure RustInvalidProgramCounter state
      | TJumpZeroChecked target =>
          match rust_stack_pop (rust_stack state) with
          | RustPopFailure error _ => Failure error state
          | RustPopSuccess condition stack =>
              let state_after_pop := rust_state_with_stack state stack in
              if N.eqb condition 0 then
                if target_valid_pc code_length target then
                  Success (rust_state_with_pc state_after_pop target)
                else Failure RustInvalidProgramCounter state_after_pop
              else Success (target_advance_pc state_after_pop)
          end
      | THalt => Success (rust_state_with_status state RustHalted)
      end
  end.

Definition target_step
    (program : list TargetInstruction)
    (state : RustState) : RustResult :=
  match rust_status state with
  | RustHalted => Success state
  | RustRunning =>
      match nth_error program (N.to_nat (rust_pc state)) with
      | Some instruction => target_eval (length program) instruction state
      | None => Failure RustInvalidProgramCounter state
      end
  end.

Definition target_program_of_canonical
    (program : list CanonicalInstruction) : list TargetInstruction :=
  List.map target_of_canonical program.

Lemma target_eval_preserves_canonical :
  forall code_length instruction state,
    target_eval code_length (target_of_canonical instruction) state =
    canonical_eval_instruction code_length instruction state.
Proof.
  intros code_length instruction state.
  destruct instruction; reflexivity.
Qed.

Lemma target_program_length :
  forall program,
    length (target_program_of_canonical program) = length program.
Proof.
  intros program.
  unfold target_program_of_canonical.
  apply List.length_map.
Qed.

Lemma target_fetch_some :
  forall program index instruction,
    nth_error program index = Some instruction ->
    nth_error (target_program_of_canonical program) index =
      Some (target_of_canonical instruction).
Proof.
  intros program.
  induction program as [|head tail IH]; intros [|index] instruction Hfetch;
    simpl in *; try discriminate.
  - inversion Hfetch; reflexivity.
  - eapply IH; exact Hfetch.
Qed.

Lemma target_fetch_none :
  forall program index,
    nth_error program index = None ->
    nth_error (target_program_of_canonical program) index = None.
Proof.
  intros program.
  induction program as [|head tail IH]; intros [|index] Hfetch;
    simpl in *; try discriminate; auto.
Qed.

Theorem canonical_step_target_step_preservation :
  forall program state,
    target_step (target_program_of_canonical program) state =
    canonical_step program state.
Proof.
  intros program state.
  unfold target_step, canonical_step.
  destruct (rust_status state) as [|].
  - destruct (nth_error program (N.to_nat (rust_pc state)))
      as [instruction|] eqn:Hfetch.
    + rewrite target_program_length.
      rewrite (target_fetch_some program
        (N.to_nat (rust_pc state)) instruction Hfetch).
      apply target_eval_preserves_canonical.
    + rewrite (target_fetch_none program
        (N.to_nat (rust_pc state)) Hfetch).
      reflexivity.
  - reflexivity.
Qed.

Theorem target_step_refines_rust_step_model :
  forall program state,
    target_step
      (target_program_of_canonical (canonical_program_of_rust program))
      state =
    rust_step_model program state.
Proof.
  intros program state.
  rewrite canonical_step_target_step_preservation.
  apply canonical_step_refines_rust_step_model.
Qed.

Inductive canonical_success_trace
    (program : list CanonicalInstruction) : RustState -> RustState -> Prop :=
| CanonicalTraceRefl : forall state,
    canonical_success_trace program state state
| CanonicalTraceStep : forall state next finish,
    canonical_step program state = Success next ->
    canonical_success_trace program next finish ->
    canonical_success_trace program state finish.

Inductive target_success_trace
    (program : list TargetInstruction) : RustState -> RustState -> Prop :=
| TargetTraceRefl : forall state,
    target_success_trace program state state
| TargetTraceStep : forall state next finish,
    target_step program state = Success next ->
    target_success_trace program next finish ->
    target_success_trace program state finish.

Theorem canonical_target_trace_forward :
  forall program start finish,
    canonical_success_trace program start finish ->
    target_success_trace (target_program_of_canonical program) start finish.
Proof.
  intros program start finish Htrace.
  induction Htrace.
  - constructor.
  - econstructor.
    + rewrite canonical_step_target_step_preservation.
      exact H.
    + exact IHHtrace.
Qed.

Theorem canonical_target_trace_backward :
  forall program start finish,
    target_success_trace (target_program_of_canonical program) start finish ->
    canonical_success_trace program start finish.
Proof.
  intros program start finish Htrace.
  induction Htrace.
  - constructor.
  - econstructor.
    + rewrite <- canonical_step_target_step_preservation.
      exact H.
    + exact IHHtrace.
Qed.

Theorem canonical_target_trace_equivalence :
  forall program start finish,
    canonical_success_trace program start finish <->
    target_success_trace (target_program_of_canonical program) start finish.
Proof.
  intros program start finish.
  split.
  - apply canonical_target_trace_forward.
  - apply canonical_target_trace_backward.
Qed.

Theorem target_failure_poststate_exact :
  forall program state error after,
    target_step (target_program_of_canonical program) state =
      Failure error after ->
    canonical_step program state = Failure error after.
Proof.
  intros program state error after Hfailure.
  rewrite <- canonical_step_target_step_preservation.
  exact Hfailure.
Qed.

Theorem target_rust_failure_poststate_exact :
  forall program state error after,
    target_step
      (target_program_of_canonical (canonical_program_of_rust program))
      state = Failure error after ->
    rust_step_model program state = Failure error after.
Proof.
  intros program state error after Hfailure.
  rewrite target_step_refines_rust_step_model in Hfailure.
  exact Hfailure.
Qed.
