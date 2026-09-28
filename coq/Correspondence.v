(* Explicit representation relation between RustModel and a separate Rocq state. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Vectors.Vector.
From MicroVeriVM Require Import RustModel.

Import ListNotations.

Inductive RocqStatus : Type :=
| RocqRunning
| RocqHalted.

Definition RocqStack : Type := list N.
Definition RocqMemory : Type := Fin.t RUST_MEMORY_SIZE -> N.

Record RocqState : Type :=
{
  rocq_pc : N;
  rocq_stack : RocqStack;
  rocq_memory : RocqMemory;
  rocq_status : RocqStatus
}.

Inductive RocqInstruction : Type :=
| RocqCONST (value : N)
| RocqADD
| RocqSUB
| RocqDUP
| RocqDROP
| RocqLOAD (address : N)
| RocqSTORE (address : N)
| RocqJMP (target : N)
| RocqJZ (target : N)
| RocqHALT.

Inductive RocqError : Type :=
| RocqStackOverflow
| RocqStackUnderflow
| RocqMemoryOutOfBounds
| RocqInvalidProgramCounter
| RocqInvalidInstruction.

Inductive RocqResult : Type :=
| RocqSuccess (state : RocqState)
| RocqFailure (error : RocqError) (state : RocqState).

Definition rust_status_corresponds
    (rust : RustStatus) (rocq : RocqStatus) : Prop :=
  match rust, rocq with
  | RustRunning, RocqRunning => True
  | RustHalted, RocqHalted => True
  | _, _ => False
  end.

Definition rust_state_corresponds
    (rust : RustState) (rocq : RocqState) : Prop :=
  rust_word_value (rust_pc rust) = rocq_pc rocq /\
  List.map rust_word_value (rust_stack_values (rust_stack rust)) = rocq_stack rocq /\
    (forall address,
        rust_word_value (Vector.nth (rust_memory rust) address) =
            rocq_memory rocq address) /\
  rust_status_corresponds (rust_status rust) (rocq_status rocq).

Inductive rust_instruction_corresponds :
    RustInstruction -> RocqInstruction -> Prop :=
| CorrespondCONST : forall rust_value rocq_value,
    rust_word_value rust_value = rocq_value ->
    rust_instruction_corresponds (RustCONST rust_value) (RocqCONST rocq_value)
| CorrespondADD : rust_instruction_corresponds RustADD RocqADD
| CorrespondSUB : rust_instruction_corresponds RustSUB RocqSUB
| CorrespondDUP : rust_instruction_corresponds RustDUP RocqDUP
| CorrespondDROP : rust_instruction_corresponds RustDROP RocqDROP
| CorrespondLOAD : forall rust_address rocq_address,
    rust_word_value rust_address = rocq_address ->
    rust_instruction_corresponds (RustLOAD rust_address) (RocqLOAD rocq_address)
| CorrespondSTORE : forall rust_address rocq_address,
    rust_word_value rust_address = rocq_address ->
    rust_instruction_corresponds (RustSTORE rust_address) (RocqSTORE rocq_address)
| CorrespondJMP : forall rust_target rocq_target,
    rust_word_value rust_target = rocq_target ->
    rust_instruction_corresponds (RustJMP rust_target) (RocqJMP rocq_target)
| CorrespondJZ : forall rust_target rocq_target,
    rust_word_value rust_target = rocq_target ->
    rust_instruction_corresponds (RustJZ rust_target) (RocqJZ rocq_target)
| CorrespondHALT : rust_instruction_corresponds RustHALT RocqHALT.

Inductive rust_error_corresponds : RustError -> RocqError -> Prop :=
| CorrespondStackOverflow :
    rust_error_corresponds RustStackOverflow RocqStackOverflow
| CorrespondStackUnderflow :
    rust_error_corresponds RustStackUnderflow RocqStackUnderflow
| CorrespondMemoryOutOfBounds :
    rust_error_corresponds RustMemoryOutOfBounds RocqMemoryOutOfBounds
| CorrespondInvalidProgramCounter :
    rust_error_corresponds RustInvalidProgramCounter RocqInvalidProgramCounter
| CorrespondInvalidInstruction :
    rust_error_corresponds RustInvalidInstruction RocqInvalidInstruction.

Inductive rust_result_corresponds : RustResult -> RocqResult -> Prop :=
| CorrespondSuccess : forall rust_state rocq_state,
    rust_state_corresponds rust_state rocq_state ->
    rust_result_corresponds (Success rust_state) (RocqSuccess rocq_state)
| CorrespondFailure : forall rust_error rocq_error rust_state rocq_state,
    rust_error_corresponds rust_error rocq_error ->
    rust_state_corresponds rust_state rocq_state ->
    rust_result_corresponds (Failure rust_error rust_state)
      (RocqFailure rocq_error rocq_state).

Definition rust_program_corresponds
    (rust_program : list RustInstruction)
    (rocq_program : list RocqInstruction) : Prop :=
    List.Forall2 rust_instruction_corresponds rust_program rocq_program.

Inductive RocqStackResult : Type :=
| RocqStackPushed (stack : RocqStack)
| RocqStackPopped (value : N) (stack : RocqStack)
| RocqStackFailure (error : RocqError) (stack : RocqStack).

Definition rocq_stack_push (value : N) (stack : RocqStack) : RocqStackResult :=
    if Nat.ltb (length stack) RUST_STACK_CAPACITY then
        RocqStackPushed (value :: stack)
    else RocqStackFailure RocqStackOverflow stack.

Definition rocq_stack_pop (stack : RocqStack) : RocqStackResult :=
    match stack with
    | [] => RocqStackFailure RocqStackUnderflow stack
    | value :: rest => RocqStackPopped value rest
    end.

Definition rocq_instruction_of_rust
        (instruction : RustInstruction) : RocqInstruction :=
    match instruction with
    | RustCONST value => RocqCONST value
    | RustADD => RocqADD
    | RustSUB => RocqSUB
    | RustDUP => RocqDUP
    | RustDROP => RocqDROP
    | RustLOAD address => RocqLOAD address
    | RustSTORE address => RocqSTORE address
    | RustJMP target => RocqJMP target
    | RustJZ target => RocqJZ target
    | RustHALT => RocqHALT
    end.

Definition rocq_error_of_rust (error : RustError) : RocqError :=
    match error with
    | RustStackOverflow => RocqStackOverflow
    | RustStackUnderflow => RocqStackUnderflow
    | RustMemoryOutOfBounds => RocqMemoryOutOfBounds
    | RustInvalidProgramCounter => RocqInvalidProgramCounter
    | RustInvalidInstruction => RocqInvalidInstruction
    end.

Definition rocq_status_of_rust (status : RustStatus) : RocqStatus :=
    match status with
    | RustRunning => RocqRunning
    | RustHalted => RocqHalted
    end.

Definition rocq_state_of_rust (state : RustState) : RocqState :=
    {| rocq_pc := rust_pc state;
         rocq_stack := List.map rust_word_value
             (rust_stack_values (rust_stack state));
         rocq_memory := fun address =>
             rust_word_value (Vector.nth (rust_memory state) address);
         rocq_status := rocq_status_of_rust (rust_status state) |}.

Lemma rust_state_corresponds_to_rocq_state_of_rust :
    forall state, rust_state_corresponds state (rocq_state_of_rust state).
Proof.
    intros [pc stack memory status].
    destruct stack as [values bound].
    destruct status.
    - repeat split; reflexivity.
    - repeat split; reflexivity.
Qed.

Lemma rust_instruction_corresponds_to_conversion :
    forall instruction,
        rust_instruction_corresponds instruction
            (rocq_instruction_of_rust instruction).
Proof.
    intros instruction.
    destruct instruction; simpl; constructor; reflexivity.
Qed.

Definition rust_stacks_correspond
        (rust_stack : RustStack) (rocq_stack : RocqStack) : Prop :=
    List.map rust_word_value (rust_stack_values rust_stack) = rocq_stack.

Inductive rust_stack_result_corresponds :
        RustStackResult -> RocqStackResult -> Prop :=
| CorrespondStackPushed : forall rust_stack rocq_stack,
        rust_stacks_correspond rust_stack rocq_stack ->
        rust_stack_result_corresponds (RustStackPushed rust_stack)
            (RocqStackPushed rocq_stack)
| CorrespondStackPopped : forall rust_value rocq_value rust_stack rocq_stack,
        rust_word_value rust_value = rocq_value ->
        rust_stacks_correspond rust_stack rocq_stack ->
        rust_stack_result_corresponds
            (RustStackPopped rust_value rust_stack)
            (RocqStackPopped rocq_value rocq_stack)
| CorrespondStackFailure : forall rust_error rocq_error rust_stack rocq_stack,
        rust_error_corresponds rust_error rocq_error ->
        rust_stacks_correspond rust_stack rocq_stack ->
        rust_stack_result_corresponds
            (RustStackFailure rust_error rust_stack)
            (RocqStackFailure rocq_error rocq_stack).

Lemma rust_stack_push_corresponds :
    forall rust_value rocq_value rust_stack rocq_stack,
        rust_word_value rust_value = rocq_value ->
        rust_stacks_correspond rust_stack rocq_stack ->
        rust_stack_result_corresponds
            (rust_stack_push rust_value rust_stack)
            (rocq_stack_push rocq_value rocq_stack).
Proof.
    intros rust_value rocq_value [rust_values rust_bound] rocq_values Hvalue Hstack.
    unfold rust_stack_push, rocq_stack_push, rust_stacks_correspond in *.
    simpl in Hstack.
    assert (Hlength : length rust_values = length rocq_values).
    {
        pose proof (f_equal (@length N) Hstack) as Hmap_length.
        rewrite List.length_map in Hmap_length.
        exact Hmap_length.
    }
    destruct (Compare_dec.lt_dec (length rust_values) RUST_STACK_CAPACITY)
        as [Hbelow | Hfull].
    - assert (Hbelow_rocq : length rocq_values < RUST_STACK_CAPACITY) by lia.
        rewrite (proj2 (Nat.ltb_lt _ _) Hbelow_rocq).
        constructor.
        unfold rust_stacks_correspond.
        simpl.
        rewrite Hvalue, Hstack.
        reflexivity.
    - assert (Hfull_rocq : ~ length rocq_values < RUST_STACK_CAPACITY) by lia.
        rewrite (proj2 (Nat.ltb_ge _ _) Hfull_rocq).
        constructor.
        + constructor.
        + exact Hstack.
Qed.

Lemma rust_stack_pop_corresponds :
    forall rust_stack rocq_stack,
        rust_stacks_correspond rust_stack rocq_stack ->
        rust_stack_result_corresponds
            (rust_stack_pop rust_stack)
            (rocq_stack_pop rocq_stack).
Proof.
    intros [rust_values rust_bound] rocq_values Hstack.
    unfold rust_stack_pop, rocq_stack_pop, rust_stacks_correspond in *.
    simpl in Hstack.
    destruct rust_values as [|rust_value rust_tail].
    - simpl in Hstack.
        subst rocq_values.
        constructor; [constructor | reflexivity].
    - destruct rocq_values as [|rocq_value rocq_tail].
        + discriminate.
        + inversion Hstack; subst rocq_value rocq_tail.
            constructor; simpl; [reflexivity | reflexivity].
Qed.

Definition rust_state_with_pc (state : RustState) (pc : RustWord) : RustState :=
    {| rust_pc := pc;
         rust_stack := rust_stack state;
         rust_memory := rust_memory state;
         rust_status := rust_status state |}.

Definition rust_state_with_stack
        (state : RustState) (stack : RustStack) : RustState :=
    {| rust_pc := rust_pc state;
         rust_stack := stack;
         rust_memory := rust_memory state;
         rust_status := rust_status state |}.

Definition rust_state_with_memory
        (state : RustState) (memory : RustMemory) : RustState :=
    {| rust_pc := rust_pc state;
         rust_stack := rust_stack state;
         rust_memory := memory;
         rust_status := rust_status state |}.

Definition rust_state_with_status
        (state : RustState) (status : RustStatus) : RustState :=
    {| rust_pc := rust_pc state;
         rust_stack := rust_stack state;
         rust_memory := rust_memory state;
         rust_status := status |}.

Definition rocq_state_with_pc (state : RocqState) (pc : N) : RocqState :=
    {| rocq_pc := pc;
         rocq_stack := rocq_stack state;
         rocq_memory := rocq_memory state;
         rocq_status := rocq_status state |}.

Definition rocq_state_with_stack
        (state : RocqState) (stack : RocqStack) : RocqState :=
    {| rocq_pc := rocq_pc state;
         rocq_stack := stack;
         rocq_memory := rocq_memory state;
         rocq_status := rocq_status state |}.

Definition rocq_state_with_memory
        (state : RocqState) (memory : RocqMemory) : RocqState :=
    {| rocq_pc := rocq_pc state;
         rocq_stack := rocq_stack state;
         rocq_memory := memory;
         rocq_status := rocq_status state |}.

Definition rocq_state_with_status
        (state : RocqState) (status : RocqStatus) : RocqState :=
    {| rocq_pc := rocq_pc state;
         rocq_stack := rocq_stack state;
         rocq_memory := rocq_memory state;
         rocq_status := status |}.

Definition rust_advance_pc (state : RustState) : RustState :=
    rust_state_with_pc state (rust_word_wrap (rust_pc state + 1)).

Definition rocq_advance_pc (state : RocqState) : RocqState :=
    rocq_state_with_pc state
        (N.modulo (rocq_pc state + 1) RUST_WORD_MODULUS).

Definition rust_memory_load_word
        (memory : RustMemory) (address : RustWord) : option RustWord :=
    match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
    | left bound => Some (Vector.nth memory (Fin.of_nat_lt bound))
    | right _ => None
    end.

Definition rust_memory_store_word
        (memory : RustMemory) (address value : RustWord)
        : option RustMemory :=
    match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
    | left bound => Some (Vector.replace memory (Fin.of_nat_lt bound) value)
    | right _ => None
    end.

Definition rocq_target_valid (code_length : nat) (target : N) : bool :=
    Nat.ltb (N.to_nat target) code_length.

Definition rust_target_valid (code_length : nat) (target : RustWord) : bool :=
    Nat.ltb (N.to_nat target) code_length.

Definition rust_execute_instruction
    (code_length : nat) (instruction : RustInstruction) (state : RustState)
    : RustResult :=
  match rust_status state with
  | RustHalted => Success state
  | RustRunning =>
      match instruction with
      | RustCONST value =>
          match rust_stack_push value (rust_stack state) with
          | RustStackPushed stack =>
              Success (rust_advance_pc (rust_state_with_stack state stack))
          | RustStackFailure error _ => Failure error state
          | RustStackPopped _ _ => Failure RustInvalidInstruction state
          end
      | RustDROP =>
          match rust_stack_pop (rust_stack state) with
          | RustStackPopped _ stack =>
              Success (rust_advance_pc (rust_state_with_stack state stack))
          | RustStackFailure error _ => Failure error state
          | RustStackPushed _ => Failure RustInvalidInstruction state
          end
      | RustDUP =>
          match rust_stack_values (rust_stack state) with
          | [] => Failure RustStackUnderflow state
          | value :: _ =>
              match rust_stack_push value (rust_stack state) with
              | RustStackPushed stack =>
                  Success (rust_advance_pc (rust_state_with_stack state stack))
              | RustStackFailure error _ => Failure error state
              | RustStackPopped _ _ => Failure RustInvalidInstruction state
              end
          end
      | RustADD | RustSUB =>
          match rust_stack_pop (rust_stack state) with
          | RustStackFailure error _ => Failure error state
          | RustStackPushed _ => Failure RustInvalidInstruction state
          | RustStackPopped right_value after_right =>
              let after_right_state := rust_state_with_stack state after_right in
              match rust_stack_pop after_right with
              | RustStackFailure error _ => Failure error after_right_state
              | RustStackPushed _ => Failure RustInvalidInstruction after_right_state
              | RustStackPopped left_value after_left =>
                  let value :=
                    match instruction with
                  | RustADD => rust_wrapping_add left_value right_value
                  | _ => rust_wrapping_sub left_value right_value
                    end in
                  match rust_stack_push value after_left with
                  | RustStackPushed stack =>
                      Success (rust_advance_pc (rust_state_with_stack state stack))
                  | RustStackFailure error _ =>
                      Failure error (rust_state_with_stack state after_left)
                  | RustStackPopped _ _ =>
                      Failure RustInvalidInstruction
                        (rust_state_with_stack state after_left)
                  end
              end
          end
      | RustLOAD address =>
          match rust_memory_load_word (rust_memory state) address with
          | None => Failure RustMemoryOutOfBounds state
          | Some value =>
              match rust_stack_push value (rust_stack state) with
              | RustStackPushed stack =>
                  Success (rust_advance_pc (rust_state_with_stack state stack))
              | RustStackFailure error _ => Failure error state
              | RustStackPopped _ _ => Failure RustInvalidInstruction state
              end
          end
      | RustSTORE address =>
          match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
          | right _ => Failure RustMemoryOutOfBounds state
          | left bound =>
              match rust_stack_pop (rust_stack state) with
              | RustStackFailure error _ => Failure error state
              | RustStackPushed _ => Failure RustInvalidInstruction state
              | RustStackPopped value stack =>
                  let memory := Vector.replace (rust_memory state)
                    (Fin.of_nat_lt bound) value in
                  Success (rust_advance_pc
                    (rust_state_with_memory
                      (rust_state_with_stack state stack) memory))
              end
          end
      | RustJMP target =>
          if rust_target_valid code_length target then
            Success (rust_state_with_pc state target)
          else Failure RustInvalidProgramCounter state
      | RustJZ target =>
          match rust_stack_pop (rust_stack state) with
          | RustStackFailure error _ => Failure error state
          | RustStackPushed _ => Failure RustInvalidInstruction state
          | RustStackPopped condition stack =>
              let after_pop := rust_state_with_stack state stack in
              if N.eqb condition 0 then
                if rust_target_valid code_length target then
                  Success (rust_state_with_pc after_pop target)
                else Failure RustInvalidProgramCounter after_pop
              else Success (rust_advance_pc after_pop)
          end
      | RustHALT => Success (rust_state_with_status state RustHalted)
      end
  end.

Definition rocq_execute_instruction
    (code_length : nat) (instruction : RocqInstruction) (state : RocqState)
    : RocqResult :=
  match rocq_status state with
  | RocqHalted => RocqSuccess state
  | RocqRunning =>
      match instruction with
      | RocqCONST value =>
          match rocq_stack_push value (rocq_stack state) with
          | RocqStackPushed stack =>
              RocqSuccess (rocq_advance_pc (rocq_state_with_stack state stack))
          | RocqStackFailure error _ => RocqFailure error state
          | RocqStackPopped _ _ => RocqFailure RocqInvalidInstruction state
          end
      | RocqDROP =>
          match rocq_stack_pop (rocq_stack state) with
          | RocqStackPopped _ stack =>
              RocqSuccess (rocq_advance_pc (rocq_state_with_stack state stack))
          | RocqStackFailure error _ => RocqFailure error state
          | RocqStackPushed _ => RocqFailure RocqInvalidInstruction state
          end
      | RocqDUP =>
          match rocq_stack state with
          | [] => RocqFailure RocqStackUnderflow state
          | value :: _ =>
              match rocq_stack_push value (rocq_stack state) with
              | RocqStackPushed stack =>
                  RocqSuccess (rocq_advance_pc
                    (rocq_state_with_stack state stack))
              | RocqStackFailure error _ => RocqFailure error state
              | RocqStackPopped _ _ => RocqFailure RocqInvalidInstruction state
              end
          end
      | RocqADD | RocqSUB =>
          match rocq_stack_pop (rocq_stack state) with
          | RocqStackFailure error _ => RocqFailure error state
          | RocqStackPushed _ => RocqFailure RocqInvalidInstruction state
          | RocqStackPopped right_value after_right =>
              let after_right_state := rocq_state_with_stack state after_right in
              match rocq_stack_pop after_right with
              | RocqStackFailure error _ =>
                  RocqFailure error after_right_state
              | RocqStackPushed _ =>
                  RocqFailure RocqInvalidInstruction after_right_state
              | RocqStackPopped left_value after_left =>
                  let value :=
                    match instruction with
                    | RocqADD => N.modulo (left_value + right_value)
                        RUST_WORD_MODULUS
                    | _ => N.modulo
                        (left_value + RUST_WORD_MODULUS - right_value)
                        RUST_WORD_MODULUS
                    end in
                  match rocq_stack_push value after_left with
                  | RocqStackPushed stack =>
                      RocqSuccess (rocq_advance_pc
                        (rocq_state_with_stack state stack))
                  | RocqStackFailure error _ =>
                      RocqFailure error (rocq_state_with_stack state after_left)
                  | RocqStackPopped _ _ =>
                      RocqFailure RocqInvalidInstruction
                        (rocq_state_with_stack state after_left)
                  end
              end
          end
      | RocqLOAD address =>
          match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
          | right _ => RocqFailure RocqMemoryOutOfBounds state
          | left bound =>
              let value := rocq_memory state (Fin.of_nat_lt bound) in
              match rocq_stack_push value (rocq_stack state) with
              | RocqStackPushed stack =>
                  RocqSuccess (rocq_advance_pc
                    (rocq_state_with_stack state stack))
              | RocqStackFailure error _ => RocqFailure error state
              | RocqStackPopped _ _ =>
                  RocqFailure RocqInvalidInstruction state
              end
          end
      | RocqSTORE address =>
          match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
          | right _ => RocqFailure RocqMemoryOutOfBounds state
          | left bound =>
              match rocq_stack_pop (rocq_stack state) with
              | RocqStackFailure error _ => RocqFailure error state
              | RocqStackPushed _ => RocqFailure RocqInvalidInstruction state
              | RocqStackPopped value stack =>
                  let index := Fin.of_nat_lt bound in
                  let memory := fun other =>
                    if Fin.eq_dec other index then value
                    else rocq_memory state other in
                  RocqSuccess (rocq_advance_pc
                    (rocq_state_with_memory
                      (rocq_state_with_stack state stack) memory))
              end
          end
      | RocqJMP target =>
          if rocq_target_valid code_length target then
            RocqSuccess (rocq_state_with_pc state target)
          else RocqFailure RocqInvalidProgramCounter state
      | RocqJZ target =>
          match rocq_stack_pop (rocq_stack state) with
          | RocqStackFailure error _ => RocqFailure error state
          | RocqStackPushed _ => RocqFailure RocqInvalidInstruction state
          | RocqStackPopped condition stack =>
              let after_pop := rocq_state_with_stack state stack in
              if N.eqb condition 0 then
                if rocq_target_valid code_length target then
                  RocqSuccess (rocq_state_with_pc after_pop target)
                else RocqFailure RocqInvalidProgramCounter after_pop
              else RocqSuccess (rocq_advance_pc after_pop)
          end
      | RocqHALT =>
          RocqSuccess (rocq_state_with_status state RocqHalted)
      end
  end.
