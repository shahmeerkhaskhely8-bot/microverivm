(* Canonical, typed instruction AST and its executable one-step semantics. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Vectors.Vector.
From MicroVeriVM Require Import RustModel.
From MicroVeriVM Require Import Correspondence.
From MicroVeriVM Require Import Soundness.

Import ListNotations.

Inductive CanonicalInstruction : Type :=
| CConst (value : RustWord)
| CAdd
| CSub
| CDup
| CDrop
| CLoad (address : RustWord)
| CStore (address : RustWord)
| CJmp (target : RustWord)
| CJz (target : RustWord)
| CHalt.

Definition canonical_instruction_of_rust
    (instruction : RustInstruction) : CanonicalInstruction :=
  match instruction with
  | RustCONST value => CConst value
  | RustADD => CAdd
  | RustSUB => CSub
  | RustDUP => CDup
  | RustDROP => CDrop
  | RustLOAD address => CLoad address
  | RustSTORE address => CStore address
  | RustJMP target => CJmp target
  | RustJZ target => CJz target
  | RustHALT => CHalt
  end.

Definition canonical_program_of_rust
    (program : list RustInstruction) : list CanonicalInstruction :=
  List.map canonical_instruction_of_rust program.

Definition canonical_advance_pc (state : RustState) : RustState :=
  rust_state_with_pc state (rust_word_wrap (rust_pc state + 1)).

Definition canonical_target_valid (code_length : nat) (target : RustWord) : bool :=
  Nat.ltb (N.to_nat target) code_length.

Definition canonical_eval_instruction
    (code_length : nat)
    (instruction : CanonicalInstruction)
    (state : RustState) : RustResult :=
  match rust_status state with
  | RustHalted => Success state
  | RustRunning =>
      match instruction with
      | CConst value =>
          match rust_stack_push value (rust_stack state) with
          | RustPushSuccess stack =>
              Success (canonical_advance_pc (rust_state_with_stack state stack))
          | RustPushFailure error _ => Failure error state
          end
      | CDrop =>
          match rust_stack_pop (rust_stack state) with
          | RustPopSuccess _ stack =>
              Success (canonical_advance_pc (rust_state_with_stack state stack))
          | RustPopFailure error _ => Failure error state
          end
      | CDup =>
          match rust_stack_values (rust_stack state) with
          | [] => Failure RustStackUnderflow state
          | value :: _ =>
              match rust_stack_push value (rust_stack state) with
              | RustPushSuccess stack =>
                  Success (canonical_advance_pc (rust_state_with_stack state stack))
              | RustPushFailure error _ => Failure error state
              end
          end
      | CAdd | CSub =>
          match rust_stack_pop (rust_stack state) with
          | RustPopFailure error _ => Failure error state
          | RustPopSuccess right_value after_right =>
              let after_right_state := rust_state_with_stack state after_right in
              match rust_stack_pop after_right with
              | RustPopFailure error _ => Failure error after_right_state
              | RustPopSuccess left_value after_left =>
                  let value :=
                    match instruction with
                    | CAdd => rust_wrapping_add left_value right_value
                    | _ => rust_wrapping_sub left_value right_value
                    end in
                  match rust_stack_push value after_left with
                  | RustPushSuccess stack =>
                      Success (canonical_advance_pc
                        (rust_state_with_stack state stack))
                  | RustPushFailure error _ =>
                      Failure error (rust_state_with_stack state after_left)
                  end
              end
          end
      | CLoad address =>
          match rust_memory_load_word (rust_memory state) address with
          | None => Failure RustMemoryOutOfBounds state
          | Some value =>
              match rust_stack_push value (rust_stack state) with
              | RustPushSuccess stack =>
                  Success (canonical_advance_pc
                    (rust_state_with_stack state stack))
              | RustPushFailure error _ => Failure error state
              end
          end
      | CStore address =>
          match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
          | right _ => Failure RustMemoryOutOfBounds state
          | left bound =>
              match rust_stack_pop (rust_stack state) with
              | RustPopFailure error _ => Failure error state
              | RustPopSuccess value stack =>
                  let memory := Vector.replace (rust_memory state)
                    (Fin.of_nat_lt bound) value in
                  Success (canonical_advance_pc
                    (rust_state_with_memory
                      (rust_state_with_stack state stack) memory))
              end
          end
      | CJmp target =>
          if canonical_target_valid code_length target then
            Success (rust_state_with_pc state target)
          else Failure RustInvalidProgramCounter state
      | CJz target =>
          match rust_stack_pop (rust_stack state) with
          | RustPopFailure error _ => Failure error state
          | RustPopSuccess condition stack =>
              let after_pop := rust_state_with_stack state stack in
              if N.eqb condition 0 then
                if canonical_target_valid code_length target then
                  Success (rust_state_with_pc after_pop target)
                else Failure RustInvalidProgramCounter after_pop
              else Success (canonical_advance_pc after_pop)
          end
      | CHalt => Success (rust_state_with_status state RustHalted)
      end
  end.

Definition canonical_step
    (program : list CanonicalInstruction)
    (state : RustState) : RustResult :=
  match rust_status state with
  | RustHalted => Success state
  | RustRunning =>
      match nth_error program (N.to_nat (rust_pc state)) with
      | Some instruction =>
          canonical_eval_instruction (length program) instruction state
      | None => Failure RustInvalidProgramCounter state
      end
  end.

Inductive canonical_transition
    (program : list CanonicalInstruction) : RustState -> RustResult -> Prop :=
| CanonicalStep : forall state result,
    canonical_step program state = result ->
    canonical_transition program state result.

Lemma canonical_instruction_evaluation_refines :
  forall code_length instruction state,
    canonical_eval_instruction code_length
      (canonical_instruction_of_rust instruction) state =
    rust_execute_instruction code_length instruction state.
Proof.
  intros code_length instruction state.
  destruct instruction; reflexivity.
Qed.

Lemma nth_error_map_canonical :
  forall (program : list RustInstruction) index instruction,
    nth_error program index = Some instruction ->
    nth_error (canonical_program_of_rust program) index =
      Some (canonical_instruction_of_rust instruction).
Proof.
  intros program.
  induction program as [|head tail IH]; intros [|index] instruction Hfetch;
    simpl in *; try discriminate.
  - inversion Hfetch; reflexivity.
  - eapply IH; exact Hfetch.
Qed.

Lemma nth_error_map_canonical_none :
  forall (program : list RustInstruction) index,
    nth_error program index = None ->
    nth_error (canonical_program_of_rust program) index = None.
Proof.
  intros program.
  induction program as [|head tail IH]; intros [|index] Hfetch;
    simpl in *; try discriminate; auto.
Qed.

Theorem canonical_step_refines_rust_step_model :
  forall program state,
    canonical_step (canonical_program_of_rust program) state =
    rust_step_model program state.
Proof.
  intros program state.
  unfold canonical_step, rust_step_model.
  destruct (rust_status state) as [|].
  - destruct (nth_error program (N.to_nat (rust_pc state)))
      as [instruction |] eqn:Hfetch.
      + assert (Hlength :
          length (canonical_program_of_rust program) = length program).
        {
          unfold canonical_program_of_rust.
          apply List.length_map.
        }
        rewrite Hlength.
      rewrite (nth_error_map_canonical program
        (N.to_nat (rust_pc state)) instruction Hfetch).
      apply canonical_instruction_evaluation_refines.
    + rewrite (nth_error_map_canonical_none program
        (N.to_nat (rust_pc state)) Hfetch).
      reflexivity.
  - reflexivity.
Qed.

Theorem canonical_transition_refines_rust_step_model :
  forall program state result,
    canonical_transition (canonical_program_of_rust program) state result ->
    result = rust_step_model program state.
Proof.
  intros program state result Htransition.
  inversion Htransition; subst.
  apply canonical_step_refines_rust_step_model.
Qed.
