(* Explicit representation relation between RustModel and a separate Rocq state. *)

Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Program.Equality.
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

Definition rust_view_corresponds
    (view : RustStateView) (rocq : RocqState) : Prop :=
  rust_word_value (rust_view_pc view) = rocq_pc rocq /\
  List.map rust_word_value (rust_view_active_stack view) = rocq_stack rocq /\
  (forall address,
    rust_word_value (Vector.nth (rust_view_memory_data view) address) =
      rocq_memory rocq address) /\
  rust_status_corresponds (rust_view_status view) (rocq_status rocq).

Theorem rust_view_corresponds_iff_projected_state :
  forall view rocq,
    rust_view_corresponds view rocq <->
    rust_state_corresponds (rust_state_from_view view) rocq.
Proof.
  intros view rocq.
  unfold rust_view_corresponds, rust_state_corresponds,
    rust_state_from_view, rust_view_active_stack.
  simpl.
  tauto.
Qed.

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

Inductive RocqPushResult : Type :=
| RocqPushSuccess (stack : RocqStack)
| RocqPushFailure (error : RocqError) (stack : RocqStack).

Inductive RocqPopResult : Type :=
| RocqPopSuccess (value : N) (stack : RocqStack)
| RocqPopFailure (error : RocqError) (stack : RocqStack).

Definition rocq_stack_push (value : N) (stack : RocqStack) : RocqPushResult :=
    match Compare_dec.lt_dec (length stack) RUST_STACK_CAPACITY with
    | left _ => RocqPushSuccess (value :: stack)
    | right _ => RocqPushFailure RocqStackOverflow stack
    end.

Definition rocq_stack_pop (stack : RocqStack) : RocqPopResult :=
    match stack with
    | [] => RocqPopFailure RocqStackUnderflow stack
    | value :: rest => RocqPopSuccess value rest
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

Inductive rust_push_result_corresponds :
    RustPushResult -> RocqPushResult -> Prop :=
| CorrespondStackPushed : forall rust_stack rocq_stack,
        rust_stacks_correspond rust_stack rocq_stack ->
    rust_push_result_corresponds (RustPushSuccess rust_stack)
        (RocqPushSuccess rocq_stack)
| CorrespondPushFailure : forall rust_error rocq_error rust_stack rocq_stack,
    rust_error_corresponds rust_error rocq_error ->
    rust_stacks_correspond rust_stack rocq_stack ->
    rust_push_result_corresponds (RustPushFailure rust_error rust_stack)
        (RocqPushFailure rocq_error rocq_stack).

Inductive rust_pop_result_corresponds :
    RustPopResult -> RocqPopResult -> Prop :=
| CorrespondStackPopped : forall rust_value rocq_value rust_stack rocq_stack,
        rust_word_value rust_value = rocq_value ->
        rust_stacks_correspond rust_stack rocq_stack ->
    rust_pop_result_corresponds
        (RustPopSuccess rust_value rust_stack)
        (RocqPopSuccess rocq_value rocq_stack)
| CorrespondPopFailure : forall rust_error rocq_error rust_stack rocq_stack,
        rust_error_corresponds rust_error rocq_error ->
        rust_stacks_correspond rust_stack rocq_stack ->
    rust_pop_result_corresponds (RustPopFailure rust_error rust_stack)
        (RocqPopFailure rocq_error rocq_stack).

Lemma rust_stack_push_corresponds :
    forall rust_value rocq_value rust_stack rocq_stack,
        rust_word_value rust_value = rocq_value ->
        rust_stacks_correspond rust_stack rocq_stack ->
        rust_push_result_corresponds
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
        rewrite <- Hlength.
        cbn [rust_stack_values] in *.
                destruct (Compare_dec.lt_dec (length rust_values) RUST_STACK_CAPACITY)
                    as [Hbelow | Hfull] eqn:Hcapacity.
                - dependent rewrite Hcapacity.
                    simpl.
                    constructor.
            unfold rust_stacks_correspond.
            simpl.
            rewrite Hvalue, Hstack.
            reflexivity.
        - dependent rewrite Hcapacity.
            simpl.
            constructor.
            + constructor.
            + exact Hstack.
Qed.

Lemma rust_stack_pop_corresponds :
    forall rust_stack rocq_stack,
        rust_stacks_correspond rust_stack rocq_stack ->
        rust_pop_result_corresponds
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

Definition rocq_memory_load_word
        (memory : RocqMemory) (address : N) : option N :=
    match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
    | left bound => Some (memory (Fin.of_nat_lt bound))
    | right _ => None
    end.

Lemma rust_rocq_memory_load_corresponds :
    forall rust_memory_value rocq_memory_value rust_address rocq_address,
        (forall index,
            rust_word_value (Vector.nth rust_memory_value index) =
                rocq_memory_value index) ->
        rust_word_value rust_address = rocq_address ->
        match rust_memory_load_word rust_memory_value rust_address with
        | None => None
        | Some value => Some (rust_word_value value)
        end = rocq_memory_load_word rocq_memory_value rocq_address.
Proof.
    intros rust_memory_value rocq_memory_value rust_address rocq_address
        Hmemory Haddress.
    unfold rust_memory_load_word, rocq_memory_load_word.
    assert (Hnat : N.to_nat rust_address = N.to_nat rocq_address).
    { now rewrite Haddress. }
    destruct (Compare_dec.lt_dec (N.to_nat rust_address) RUST_MEMORY_SIZE)
        as [Hrust_valid | Hrust_invalid].
    - destruct (Compare_dec.lt_dec (N.to_nat rocq_address) RUST_MEMORY_SIZE)
            as [Hrocq_valid | Hrocq_invalid].
        + f_equal.
            assert (Hindex : Fin.of_nat_lt Hrust_valid = Fin.of_nat_lt Hrocq_valid).
            {
                apply Fin.to_nat_inj.
                rewrite !Fin.to_nat_of_nat.
                simpl.
                exact Hnat.
            }
            rewrite Hindex.
            apply Hmemory.
        + exfalso.
            apply Hrocq_invalid.
            now rewrite <- Hnat.
    - destruct (Compare_dec.lt_dec (N.to_nat rocq_address) RUST_MEMORY_SIZE)
            as [Hrocq_valid | Hrocq_invalid].
        + exfalso.
            apply Hrust_invalid.
            now rewrite Hnat.
        + reflexivity.
Qed.

Definition rust_memory_store_word
        (memory : RustMemory) (address value : RustWord)
        : option RustMemory :=
    match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
    | left bound => Some (Vector.replace memory (Fin.of_nat_lt bound) value)
    | right _ => None
    end.

Definition rocq_memory_store_word
        (memory : RocqMemory) (address value : N) : option RocqMemory :=
    match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
    | left bound =>
            let index := Fin.of_nat_lt bound in
            Some (fun other =>
                if Fin.eq_dec other index then value else memory other)
    | right _ => None
    end.

Inductive rust_rocq_memory_update_corresponds :
        option RustMemory -> option RocqMemory -> Prop :=
| CorrespondMemoryUpdateInvalid :
        rust_rocq_memory_update_corresponds None None
| CorrespondMemoryUpdateValid : forall rust_memory_value rocq_memory_value,
        (forall index,
            rust_word_value (Vector.nth rust_memory_value index) =
                rocq_memory_value index) ->
        rust_rocq_memory_update_corresponds
            (Some rust_memory_value) (Some rocq_memory_value).

Lemma rust_rocq_memory_store_corresponds :
    forall rust_memory_value rocq_memory_value rust_address rocq_address
        rust_value rocq_value,
        (forall index,
            rust_word_value (Vector.nth rust_memory_value index) =
                rocq_memory_value index) ->
        rust_word_value rust_address = rocq_address ->
        rust_word_value rust_value = rocq_value ->
        rust_rocq_memory_update_corresponds
            (rust_memory_store_word rust_memory_value rust_address rust_value)
            (rocq_memory_store_word rocq_memory_value rocq_address rocq_value).
Proof.
    intros rust_memory_value rocq_memory_value rust_address rocq_address
        rust_value rocq_value Hmemory Haddress Hvalue.
    unfold rust_memory_store_word, rocq_memory_store_word.
    assert (Hnat : N.to_nat rust_address = N.to_nat rocq_address).
    { now rewrite Haddress. }
    destruct (Compare_dec.lt_dec (N.to_nat rust_address) RUST_MEMORY_SIZE)
        as [Hrust_valid | Hrust_invalid].
    - destruct (Compare_dec.lt_dec (N.to_nat rocq_address) RUST_MEMORY_SIZE)
            as [Hrocq_valid | Hrocq_invalid].
        + assert (Hindex : Fin.of_nat_lt Hrust_valid = Fin.of_nat_lt Hrocq_valid).
            {
                apply Fin.to_nat_inj.
                rewrite !Fin.to_nat_of_nat.
                simpl.
                exact Hnat.
            }
            constructor.
            intro index.
            destruct (Fin.eq_dec index (Fin.of_nat_lt Hrust_valid)) as [Heq | Hneq].
            * subst index.
                rewrite VectorSpec.nth_replace_eq.
                rewrite Hindex.
                                destruct (Fin.eq_dec (Fin.of_nat_lt Hrocq_valid)
                                    (Fin.of_nat_lt Hrocq_valid)); simpl.
                                -- exact Hvalue.
                                -- contradiction.
              * rewrite VectorSpec.nth_replace_neq by exact Hneq.
                destruct (Fin.eq_dec index (Fin.of_nat_lt Hrocq_valid)) as [Heq | Hneq_rocq].
                -- subst index.
                     exfalso.
                     apply Hneq.
                     rewrite Hindex.
                     reflexivity.
                 -- simpl.
                    apply Hmemory.
        + exfalso.
            apply Hrocq_invalid.
            now rewrite <- Hnat.
    - destruct (Compare_dec.lt_dec (N.to_nat rocq_address) RUST_MEMORY_SIZE)
            as [Hrocq_valid | Hrocq_invalid].
        + exfalso.
            apply Hrust_invalid.
            now rewrite Hnat.
        + constructor.
Qed.

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
          | RustPushSuccess stack =>
              Success (rust_advance_pc (rust_state_with_stack state stack))
          | RustPushFailure error _ => Failure error state
          end
      | RustDROP =>
          match rust_stack_pop (rust_stack state) with
          | RustPopSuccess _ stack =>
              Success (rust_advance_pc (rust_state_with_stack state stack))
          | RustPopFailure error _ => Failure error state
          end
      | RustDUP =>
          match rust_stack_values (rust_stack state) with
          | [] => Failure RustStackUnderflow state
          | value :: _ =>
              match rust_stack_push value (rust_stack state) with
              | RustPushSuccess stack =>
                  Success (rust_advance_pc (rust_state_with_stack state stack))
              | RustPushFailure error _ => Failure error state
              end
          end
      | RustADD | RustSUB =>
          match rust_stack_pop (rust_stack state) with
          | RustPopFailure error _ => Failure error state
          | RustPopSuccess right_value after_right =>
              let after_right_state := rust_state_with_stack state after_right in
              match rust_stack_pop after_right with
              | RustPopFailure error _ => Failure error after_right_state
              | RustPopSuccess left_value after_left =>
                  let value :=
                    match instruction with
                  | RustADD => rust_wrapping_add left_value right_value
                  | _ => rust_wrapping_sub left_value right_value
                    end in
                  match rust_stack_push value after_left with
                  | RustPushSuccess stack =>
                      Success (rust_advance_pc (rust_state_with_stack state stack))
                  | RustPushFailure error _ =>
                      Failure error (rust_state_with_stack state after_left)
                  end
              end
          end
      | RustLOAD address =>
          match rust_memory_load_word (rust_memory state) address with
          | None => Failure RustMemoryOutOfBounds state
          | Some value =>
              match rust_stack_push value (rust_stack state) with
              | RustPushSuccess stack =>
                  Success (rust_advance_pc (rust_state_with_stack state stack))
              | RustPushFailure error _ => Failure error state
              end
          end
      | RustSTORE address =>
          match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
          | right _ => Failure RustMemoryOutOfBounds state
          | left bound =>
              match rust_stack_pop (rust_stack state) with
              | RustPopFailure error _ => Failure error state
              | RustPopSuccess value stack =>
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
          | RustPopFailure error _ => Failure error state
          | RustPopSuccess condition stack =>
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
          | RocqPushSuccess stack =>
              RocqSuccess (rocq_advance_pc (rocq_state_with_stack state stack))
          | RocqPushFailure error _ => RocqFailure error state
          end
      | RocqDROP =>
          match rocq_stack_pop (rocq_stack state) with
          | RocqPopSuccess _ stack =>
              RocqSuccess (rocq_advance_pc (rocq_state_with_stack state stack))
          | RocqPopFailure error _ => RocqFailure error state
          end
      | RocqDUP =>
          match rocq_stack state with
          | [] => RocqFailure RocqStackUnderflow state
          | value :: _ =>
              match rocq_stack_push value (rocq_stack state) with
                            | RocqPushSuccess stack =>
                  RocqSuccess (rocq_advance_pc
                    (rocq_state_with_stack state stack))
                            | RocqPushFailure error _ => RocqFailure error state
              end
          end
      | RocqADD | RocqSUB =>
          match rocq_stack_pop (rocq_stack state) with
          | RocqPopFailure error _ => RocqFailure error state
          | RocqPopSuccess right_value after_right =>
              let after_right_state := rocq_state_with_stack state after_right in
              match rocq_stack_pop after_right with
              | RocqPopFailure error _ =>
                  RocqFailure error after_right_state
              | RocqPopSuccess left_value after_left =>
                  let value :=
                    match instruction with
                    | RocqADD => N.modulo (left_value + right_value)
                        RUST_WORD_MODULUS
                    | _ => N.modulo
                        (left_value + RUST_WORD_MODULUS - right_value)
                        RUST_WORD_MODULUS
                    end in
                  match rocq_stack_push value after_left with
                                    | RocqPushSuccess stack =>
                      RocqSuccess (rocq_advance_pc
                        (rocq_state_with_stack state stack))
                                    | RocqPushFailure error _ =>
                      RocqFailure error (rocq_state_with_stack state after_left)
                  end
              end
          end
      | RocqLOAD address =>
          match rocq_memory_load_word (rocq_memory state) address with
          | None => RocqFailure RocqMemoryOutOfBounds state
          | Some value =>
              match rocq_stack_push value (rocq_stack state) with
                            | RocqPushSuccess stack =>
                  RocqSuccess (rocq_advance_pc
                    (rocq_state_with_stack state stack))
                            | RocqPushFailure error _ => RocqFailure error state
              end
          end
      | RocqSTORE address =>
          match Compare_dec.lt_dec (N.to_nat address) RUST_MEMORY_SIZE with
          | right _ => RocqFailure RocqMemoryOutOfBounds state
          | left bound =>
              match rocq_stack_pop (rocq_stack state) with
              | RocqPopFailure error _ => RocqFailure error state
              | RocqPopSuccess value stack =>
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
          | RocqPopFailure error _ => RocqFailure error state
          | RocqPopSuccess condition stack =>
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

Lemma rust_wrapping_add_corresponds_to_modulo :
    forall left right,
        rust_word_value (rust_wrapping_add left right) =
            N.modulo (left + right) RUST_WORD_MODULUS.
Proof.
    reflexivity.
Qed.

Lemma rust_wrapping_sub_corresponds_to_modulo :
    forall left right,
        rust_word_value (rust_wrapping_sub left right) =
            N.modulo (left + RUST_WORD_MODULUS - right) RUST_WORD_MODULUS.
Proof.
    reflexivity.
Qed.

Lemma rust_state_with_pc_corresponds :
    forall rust_state rocq_state rust_pc_value rocq_pc_value,
        rust_state_corresponds rust_state rocq_state ->
        rust_word_value rust_pc_value = rocq_pc_value ->
        rust_state_corresponds
            (rust_state_with_pc rust_state rust_pc_value)
            (rocq_state_with_pc rocq_state rocq_pc_value).
Proof.
    intros rust_state rocq_state rust_pc_value rocq_pc_value
        [Hpc [Hstack [Hmemory Hstatus]]] Hnewpc.
    unfold rust_state_corresponds, rust_state_with_pc,
        rocq_state_with_pc, rust_stacks_correspond.
    simpl.
    repeat split; assumption.
Qed.

Lemma rust_state_with_stack_corresponds :
    forall rust_state rocq_state rust_stack_value rocq_stack_value,
        rust_state_corresponds rust_state rocq_state ->
        rust_stacks_correspond rust_stack_value rocq_stack_value ->
        rust_state_corresponds
            (rust_state_with_stack rust_state rust_stack_value)
            (rocq_state_with_stack rocq_state rocq_stack_value).
Proof.
    intros rust_state rocq_state rust_stack_value rocq_stack_value
        [Hpc [Hstack [Hmemory Hstatus]]] Hnewstack.
    unfold rust_state_corresponds, rust_state_with_stack,
        rocq_state_with_stack, rust_stacks_correspond.
    simpl.
    repeat split; assumption.
Qed.

Lemma rust_state_with_memory_corresponds :
    forall rust_state rocq_state rust_memory_value rocq_memory_value,
        rust_state_corresponds rust_state rocq_state ->
        (forall index,
            rust_word_value (Vector.nth rust_memory_value index) =
                rocq_memory_value index) ->
        rust_state_corresponds
            (rust_state_with_memory rust_state rust_memory_value)
            (rocq_state_with_memory rocq_state rocq_memory_value).
Proof.
    intros rust_state rocq_state rust_memory_value rocq_memory_value
        [Hpc [Hstack [Hmemory Hstatus]]] Hnewmemory.
    unfold rust_state_corresponds, rust_state_with_memory,
        rocq_state_with_memory, rust_stacks_correspond.
    simpl.
    repeat split; assumption.
Qed.

Lemma rust_state_with_status_corresponds :
    forall rust_state rocq_state rust_status_value rocq_status_value,
        rust_state_corresponds rust_state rocq_state ->
        rust_status_corresponds rust_status_value rocq_status_value ->
        rust_state_corresponds
            (rust_state_with_status rust_state rust_status_value)
            (rocq_state_with_status rocq_state rocq_status_value).
Proof.
    intros rust_state rocq_state rust_status_value rocq_status_value
        [Hpc [Hstack [Hmemory Hstatus]]] Hnewstatus.
    unfold rust_state_corresponds, rust_state_with_status,
        rocq_state_with_status, rust_stacks_correspond.
    simpl.
    repeat split; assumption.
Qed.

Lemma rust_advance_pc_corresponds :
    forall rust_state rocq_state,
        rust_state_corresponds rust_state rocq_state ->
        rust_state_corresponds
            (rust_advance_pc rust_state) (rocq_advance_pc rocq_state).
Proof.
    intros rust_state rocq_state [Hpc [Hstack [Hmemory Hstatus]]].
    change (rust_word_value (rust_pc rust_state) = rocq_pc rocq_state) in Hpc.
    unfold rust_state_corresponds, rust_advance_pc, rocq_advance_pc,
        rust_state_with_pc, rocq_state_with_pc, rust_word_wrap,
        rust_word_of_N.
    simpl.
    rewrite Hpc.
    repeat split; assumption || reflexivity.
Qed.

Lemma rust_jmp_target_valid_corresponds :
    forall code_length rust_target rocq_target,
        rust_word_value rust_target = rocq_target ->
        rust_target_valid code_length rust_target =
            rocq_target_valid code_length rocq_target.
Proof.
    intros code_length rust_target rocq_target Htarget.
    unfold rust_target_valid, rocq_target_valid.
    now rewrite Htarget.
Qed.

Theorem rust_halt_instruction_corresponds :
    forall code_length rust_state rocq_state,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustRunning ->
        rust_result_corresponds
            (rust_execute_instruction code_length RustHALT rust_state)
            (rocq_execute_instruction code_length RocqHALT rocq_state).
Proof.
    intros code_length rust_state rocq_state Hstate Hrunning.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hrunning in Hstatus.
    unfold rust_execute_instruction, rocq_execute_instruction.
    rewrite Hrunning.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - cbn.
        apply CorrespondSuccess.
        unfold rust_state_corresponds, rust_state_with_status,
            rocq_state_with_status, rust_stacks_correspond.
        simpl.
        repeat split; assumption || reflexivity.
    - simpl in Hstatus.
        contradiction.
Qed.

Theorem rust_jmp_instruction_corresponds :
    forall code_length rust_state rocq_state rust_target rocq_target,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustRunning ->
        rust_word_value rust_target = rocq_target ->
        rust_result_corresponds
            (rust_execute_instruction code_length (RustJMP rust_target) rust_state)
            (rocq_execute_instruction code_length (RocqJMP rocq_target) rocq_state).
Proof.
    intros code_length rust_state rocq_state rust_target rocq_target
        Hstate Hrunning Htarget.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hrunning in Hstatus.
    unfold rust_execute_instruction, rocq_execute_instruction.
    rewrite Hrunning.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - pose proof (rust_jmp_target_valid_corresponds
            code_length rust_target rocq_target Htarget) as Hvalid.
        rewrite <- Hvalid.
        destruct (rust_target_valid code_length rust_target) eqn:Htarget_valid.
        + apply CorrespondSuccess.
            unfold rust_state_corresponds, rust_state_with_pc,
                rocq_state_with_pc, rust_stacks_correspond,
                rust_status_corresponds.
            simpl.
            split; [exact Htarget |].
            split; [exact Hstack |].
            split; [exact Hmemory |].
            unfold rust_status_corresponds.
            rewrite Hrunning, Hrocqstatus.
            exact I.
        + apply CorrespondFailure.
            * constructor.
                        * unfold rust_state_corresponds, rust_stacks_correspond.
                            split; [exact Hpc |].
                            split; [exact Hstack |].
                            split; [exact Hmemory |].
                                        rewrite Hrunning, Hrocqstatus.
                            exact Hstatus.
    - simpl in Hstatus.
        contradiction.
Qed.

Theorem rust_const_instruction_corresponds :
    forall code_length rust_state rocq_state rust_value rocq_value,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustRunning ->
        rust_word_value rust_value = rocq_value ->
        rust_result_corresponds
            (rust_execute_instruction code_length (RustCONST rust_value) rust_state)
            (rocq_execute_instruction code_length (RocqCONST rocq_value) rocq_state).
Proof.
    intros code_length rust_state rocq_state rust_value rocq_value
        Hstate Hrunning Hvalue.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hrunning in Hstatus.
    unfold rust_execute_instruction, rocq_execute_instruction.
    rewrite Hrunning.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - pose proof (rust_stack_push_corresponds
            rust_value rocq_value (rust_stack rust_state) (rocq_stack rocq_state)
            Hvalue Hstack) as Hpush.
                destruct Hpush as
                        [rust_after rocq_after Hstack_after |
                         rust_error rocq_error rust_after rocq_after Herr Hstack_after].
                + apply CorrespondSuccess.
                    apply rust_advance_pc_corresponds.
                    apply rust_state_with_stack_corresponds.
                    * unfold rust_state_corresponds, rust_stacks_correspond.
                        split; [exact Hpc |].
                        split; [exact Hstack |].
                        split; [exact Hmemory |].
                        rewrite Hrunning, Hrocqstatus.
                        exact Hstatus.
                    * exact Hstack_after.
                + apply CorrespondFailure.
                    * exact Herr.
                    * unfold rust_state_corresponds, rust_stacks_correspond.
                        split; [exact Hpc |].
                        split; [exact Hstack |].
                        split; [exact Hmemory |].
                        rewrite Hrunning, Hrocqstatus.
                        exact Hstatus.
        - unfold rust_status_corresponds in Hstatus.
                    destruct Hstatus.
Qed.

Theorem rust_drop_instruction_corresponds :
    forall code_length rust_state rocq_state,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustRunning ->
        rust_result_corresponds
            (rust_execute_instruction code_length RustDROP rust_state)
            (rocq_execute_instruction code_length RocqDROP rocq_state).
Proof.
    intros code_length rust_state rocq_state Hstate Hrunning.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hrunning in Hstatus.
    unfold rust_execute_instruction, rocq_execute_instruction.
    rewrite Hrunning.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - pose proof (rust_stack_pop_corresponds
            (rust_stack rust_state) (rocq_stack rocq_state) Hstack) as Hpop.
        destruct Hpop as
            [rust_value rocq_value rust_after rocq_after Hvalue Hafter |
             rust_error rocq_error rust_after rocq_after Herror Hafter].
        + apply CorrespondSuccess.
            apply rust_advance_pc_corresponds.
            apply rust_state_with_stack_corresponds.
            * unfold rust_state_corresponds, rust_stacks_correspond.
                split; [exact Hpc |].
                split; [exact Hstack |].
                split; [exact Hmemory |].
                rewrite Hrunning, Hrocqstatus.
                exact Hstatus.
            * exact Hafter.
        + apply CorrespondFailure.
            * exact Herror.
            * unfold rust_state_corresponds, rust_stacks_correspond.
                split; [exact Hpc |].
                split; [exact Hstack |].
                split; [exact Hmemory |].
                rewrite Hrunning, Hrocqstatus.
                exact Hstatus.
    - unfold rust_status_corresponds in Hstatus.
        destruct Hstatus.
Qed.

Theorem rust_add_instruction_corresponds :
    forall code_length rust_state rocq_state,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustRunning ->
        rust_result_corresponds
            (rust_execute_instruction code_length RustADD rust_state)
            (rocq_execute_instruction code_length RocqADD rocq_state).
Proof.
    intros code_length rust_state rocq_state Hstate Hrunning.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hrunning in Hstatus.
    unfold rust_execute_instruction, rocq_execute_instruction.
    rewrite Hrunning.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - pose proof (rust_stack_pop_corresponds
            (rust_stack rust_state) (rocq_stack rocq_state) Hstack) as Hfirst.
        assert (Hstate_corr : rust_state_corresponds rust_state rocq_state).
        {
            unfold rust_state_corresponds, rust_stacks_correspond.
            split; [exact Hpc |].
            split; [exact Hstack |].
            split; [exact Hmemory |].
            rewrite Hrunning, Hrocqstatus.
            exact Hstatus.
        }
        destruct Hfirst as
            [right_r right_q after_right_r after_right_q Hright Hafter_right |
             first_error_r first_error_q stack_error_r stack_error_q Herr Hfailed_stack].
        + pose proof (rust_stack_pop_corresponds
                after_right_r after_right_q Hafter_right) as Hsecond.
            destruct Hsecond as
                [left_r left_q after_left_r after_left_q Hleft Hafter_left |
                 second_error_r second_error_q failed_r failed_q Hsecond_error Hfailed_stack].
            * assert (Hsum : rust_word_value (rust_wrapping_add left_r right_r) =
                        N.modulo (left_q + right_q) RUST_WORD_MODULUS).
                {
                    rewrite rust_wrapping_add_corresponds_to_modulo.
                    now rewrite Hleft, Hright.
                }
                pose proof (rust_stack_push_corresponds
                    (rust_wrapping_add left_r right_r)
                    (N.modulo (left_q + right_q) RUST_WORD_MODULUS)
                    after_left_r after_left_q Hsum Hafter_left) as Hpush.
                destruct Hpush as
                    [after_push_r after_push_q Hafter_push |
                     push_error_r push_error_q failed_push_r failed_push_q Hpush_error Hfailed_push].
                -- apply CorrespondSuccess.
                      apply rust_advance_pc_corresponds.
                      apply rust_state_with_stack_corresponds with
                         (rust_state := rust_state) (rocq_state := rocq_state).
                      ++ exact Hstate_corr.
                      ++ exact Hafter_push.
                -- apply CorrespondFailure.
                     ++ exact Hpush_error.
                      ++ apply rust_state_with_stack_corresponds with
                             (rust_state := rust_state) (rocq_state := rocq_state).
                          ** exact Hstate_corr.
                          ** exact Hafter_left.
            * apply CorrespondFailure.
                -- exact Hsecond_error.
                -- apply rust_state_with_stack_corresponds.
                      ++ exact Hstate_corr.
                     ++ exact Hafter_right.
        + apply CorrespondFailure.
            * exact Herr.
            * exact Hstate_corr.
    - unfold rust_status_corresponds in Hstatus.
        destruct Hstatus.
Qed.

Theorem rust_sub_instruction_corresponds :
    forall code_length rust_state rocq_state,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustRunning ->
        rust_result_corresponds
            (rust_execute_instruction code_length RustSUB rust_state)
            (rocq_execute_instruction code_length RocqSUB rocq_state).
Proof.
    intros code_length rust_state rocq_state Hstate Hrunning.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hrunning in Hstatus.
    unfold rust_execute_instruction, rocq_execute_instruction.
    rewrite Hrunning.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - pose proof (rust_stack_pop_corresponds
            (rust_stack rust_state) (rocq_stack rocq_state) Hstack) as Hfirst.
        assert (Hstate_corr : rust_state_corresponds rust_state rocq_state).
        {
            unfold rust_state_corresponds, rust_stacks_correspond.
            split; [exact Hpc |].
            split; [exact Hstack |].
            split; [exact Hmemory |].
            rewrite Hrunning, Hrocqstatus.
            exact Hstatus.
        }
        destruct Hfirst as
            [right_r right_q after_right_r after_right_q Hright Hafter_right |
             first_error_r first_error_q stack_error_r stack_error_q Herr Hfailed_stack].
        + pose proof (rust_stack_pop_corresponds
                after_right_r after_right_q Hafter_right) as Hsecond.
            destruct Hsecond as
                [left_r left_q after_left_r after_left_q Hleft Hafter_left |
                 second_error_r second_error_q failed_r failed_q Hsecond_error Hfailed_stack].
            * assert (Hdiff : rust_word_value (rust_wrapping_sub left_r right_r) =
                        N.modulo (left_q + RUST_WORD_MODULUS - right_q)
                            RUST_WORD_MODULUS).
                {
                    rewrite rust_wrapping_sub_corresponds_to_modulo.
                    now rewrite Hleft, Hright.
                }
                pose proof (rust_stack_push_corresponds
                    (rust_wrapping_sub left_r right_r)
                    (N.modulo (left_q + RUST_WORD_MODULUS - right_q)
                        RUST_WORD_MODULUS)
                    after_left_r after_left_q Hdiff Hafter_left) as Hpush.
                destruct Hpush as
                    [after_push_r after_push_q Hafter_push |
                     push_error_r push_error_q failed_push_r failed_push_q Hpush_error Hfailed_push].
                -- apply CorrespondSuccess.
                     apply rust_advance_pc_corresponds.
                     apply rust_state_with_stack_corresponds with
                         (rust_state := rust_state) (rocq_state := rocq_state).
                     ++ exact Hstate_corr.
                     ++ exact Hafter_push.
                -- apply CorrespondFailure.
                     ++ exact Hpush_error.
                     ++ apply rust_state_with_stack_corresponds with
                                (rust_state := rust_state) (rocq_state := rocq_state).
                            ** exact Hstate_corr.
                            ** exact Hafter_left.
            * apply CorrespondFailure.
                -- exact Hsecond_error.
                -- apply rust_state_with_stack_corresponds.
                     ++ exact Hstate_corr.
                     ++ exact Hafter_right.
        + apply CorrespondFailure.
            * exact Herr.
            * exact Hstate_corr.
    - unfold rust_status_corresponds in Hstatus.
        destruct Hstatus.
Qed.

Theorem rust_dup_instruction_corresponds :
    forall code_length rust_state rocq_state,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustRunning ->
        rust_result_corresponds
            (rust_execute_instruction code_length RustDUP rust_state)
            (rocq_execute_instruction code_length RocqDUP rocq_state).
Proof.
    intros code_length rust_state rocq_state Hstate Hrunning.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hrunning in Hstatus.
    unfold rust_execute_instruction, rocq_execute_instruction.
    rewrite Hrunning.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - destruct (rust_stack_values (rust_stack rust_state))
            as [|rust_top rust_rest] eqn:Hrust_values.
        + assert (Hrocq_empty : rocq_stack rocq_state = []).
            {
                unfold rust_stacks_correspond in Hstack.
                simpl in Hstack.
                symmetry.
                exact Hstack.
            }
            rewrite Hrocq_empty.
            simpl.
            apply CorrespondFailure.
            * constructor.
            * unfold rust_state_corresponds, rust_stacks_correspond.
                split; [exact Hpc |].
                     split.
                     -- rewrite Hrust_values.
                         simpl.
                         exact Hstack.
                     -- split; [exact Hmemory |].
                         rewrite Hrunning, Hrocqstatus.
                         exact Hstatus.
        + destruct (rocq_stack rocq_state) as [|rocq_top rocq_rest]
                eqn:Hrocq_values.
            * unfold rust_stacks_correspond in Hstack.
                simpl in Hstack.
                discriminate.
                                                * simpl.
                                                    assert (Htop : rust_word_value rust_top = rocq_top).
                {
                    unfold rust_stacks_correspond in Hstack.
                      simpl in Hstack.
                    inversion Hstack.
                    reflexivity.
                }
                assert (Hstack_tails :
                    rust_stacks_correspond
                        {| rust_stack_values := rust_rest;
                             rust_stack_bounded :=
                                                                 ltac:(pose proof
                                                                     (rust_stack_bounded (rust_stack rust_state))
                                                                     as Hbound;
                                                                     rewrite Hrust_values in Hbound;
                                                                     simpl in Hbound; lia) |}
                        rocq_rest).
                {
                    unfold rust_stacks_correspond.
                    unfold rust_stacks_correspond in Hstack.
                      simpl in Hstack.
                    inversion Hstack.
                    reflexivity.
                }
                assert (Hwhole_stack :
                    rust_stacks_correspond (rust_stack rust_state) (rocq_stack rocq_state)).
                {
                    unfold rust_stacks_correspond.
                    rewrite Hrust_values, Hrocq_values.
                    exact Hstack.
                }
                pose proof (rust_stack_push_corresponds
                    rust_top rocq_top (rust_stack rust_state) (rocq_stack rocq_state)
                    Htop Hwhole_stack) as Hpush.
                dependent destruction Hpush.
                                        -- rewrite Hrocq_values in x.
                                            rewrite <- x0, <- x.
                        simpl.
                        apply CorrespondSuccess.
                        apply rust_advance_pc_corresponds.
                        apply rust_state_with_stack_corresponds.
                        ++ unfold rust_state_corresponds, rust_stacks_correspond.
                           split; [exact Hpc |].
                                     split; [exact Hwhole_stack |].
                           split; [exact Hmemory |].
                           rewrite Hrunning, Hrocqstatus.
                           exact Hstatus.
                        ++ match goal with
                           | Hcorr : rust_stacks_correspond _ _ |- _ => exact Hcorr
                           end.
                     -- rewrite Hrocq_values in x.
                         rewrite <- x0, <- x.
                         simpl.
                         apply CorrespondFailure.
                         ++ exact H.
                         ++ unfold rust_state_corresponds, rust_stacks_correspond.
                             split; [exact Hpc |].
                             split; [exact Hwhole_stack |].
                             split; [exact Hmemory |].
                             rewrite Hrunning, Hrocqstatus.
                             exact Hstatus.
    - unfold rust_status_corresponds in Hstatus.
        destruct Hstatus.
Qed.

Theorem rust_jz_instruction_corresponds :
    forall code_length rust_state rocq_state rust_target rocq_target,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustRunning ->
        rust_word_value rust_target = rocq_target ->
        rust_result_corresponds
            (rust_execute_instruction code_length (RustJZ rust_target) rust_state)
            (rocq_execute_instruction code_length (RocqJZ rocq_target) rocq_state).
Proof.
    intros code_length rust_state rocq_state rust_target rocq_target
        Hstate Hrunning Htarget.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hrunning in Hstatus.
    unfold rust_execute_instruction, rocq_execute_instruction.
    rewrite Hrunning.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - pose proof (rust_stack_pop_corresponds
            (rust_stack rust_state) (rocq_stack rocq_state) Hstack) as Hpop.
        assert (Hstate_corr : rust_state_corresponds rust_state rocq_state).
        {
            unfold rust_state_corresponds, rust_stacks_correspond.
            split; [exact Hpc |].
            split; [exact Hstack |].
            split; [exact Hmemory |].
            rewrite Hrunning, Hrocqstatus.
            exact Hstatus.
        }
        dependent destruction Hpop.
        + rewrite <- x0, <- x.
            simpl.
            destruct (N.eqb rocq_value 0) eqn:Hzero.
            * rewrite H.
                rewrite Hzero.
                simpl.
                pose proof (rust_jmp_target_valid_corresponds
                    code_length rust_target rocq_target Htarget) as Hvalid.
                rewrite Hvalid.
                destruct (rocq_target_valid code_length rocq_target) eqn:Htarget_valid.
                -- apply CorrespondSuccess.
                     apply rust_state_with_pc_corresponds.
                     ++ apply rust_state_with_stack_corresponds.
                            ** exact Hstate_corr.
                            ** match goal with
                                 | Hcorr : rust_stacks_correspond _ _ |- _ => exact Hcorr
                                 end.
                     ++ exact Htarget.
                -- apply CorrespondFailure.
                     ++ constructor.
                     ++ apply rust_state_with_stack_corresponds.
                            ** exact Hstate_corr.
                            ** match goal with
                                 | Hcorr : rust_stacks_correspond _ _ |- _ => exact Hcorr
                                 end.
                        * rewrite H, Hzero.
                            simpl.
                            apply CorrespondSuccess.
                apply rust_advance_pc_corresponds.
                apply rust_state_with_stack_corresponds.
                -- exact Hstate_corr.
                -- match goal with
                     | Hcorr : rust_stacks_correspond _ _ |- _ => exact Hcorr
                     end.
        + rewrite <- x0, <- x.
            apply CorrespondFailure.
            * exact H.
            * exact Hstate_corr.
    - unfold rust_status_corresponds in Hstatus.
        destruct Hstatus.
Qed.

Theorem rust_load_instruction_corresponds :
    forall code_length rust_state rocq_state rust_address rocq_address,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustRunning ->
        rust_word_value rust_address = rocq_address ->
        rust_result_corresponds
            (rust_execute_instruction code_length (RustLOAD rust_address) rust_state)
            (rocq_execute_instruction code_length (RocqLOAD rocq_address) rocq_state).
Proof.
    intros code_length rust_state rocq_state rust_address rocq_address
        Hstate Hrunning Haddress.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hrunning in Hstatus.
    unfold rust_execute_instruction, rocq_execute_instruction.
    rewrite Hrunning.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - pose proof (rust_rocq_memory_load_corresponds
            (rust_memory rust_state) (rocq_memory rocq_state)
            rust_address rocq_address Hmemory Haddress) as Hread.
        destruct (rust_memory_load_word (rust_memory rust_state) rust_address)
            as [rust_value |] eqn:Hrust_read.
        + simpl in Hread.
            destruct (rocq_memory_load_word (rocq_memory rocq_state) rocq_address)
                as [rocq_value |] eqn:Hrocq_read.
            * inversion Hread; subst rocq_value.
                pose proof (rust_stack_push_corresponds rust_value
                    (rust_word_value rust_value) (rust_stack rust_state)
                    (rocq_stack rocq_state) eq_refl Hstack) as Hpush.
                dependent destruction Hpush.
                     -- rewrite <- x0, <- x.
                         simpl.
                     apply CorrespondSuccess.
                     apply rust_advance_pc_corresponds.
                     apply rust_state_with_stack_corresponds.
                     ++ unfold rust_state_corresponds, rust_stacks_correspond.
                            split; [exact Hpc |].
                            split; [exact Hstack |].
                            split; [exact Hmemory |].
                            rewrite Hrunning, Hrocqstatus.
                            exact Hstatus.
                     ++ match goal with
                            | Hcorr : rust_stacks_correspond _ _ |- _ => exact Hcorr
                            end.
                 -- rewrite <- x0, <- x.
                    simpl.
                    apply CorrespondFailure.
                     ++ eauto using rust_error_corresponds.
                     ++ unfold rust_state_corresponds, rust_stacks_correspond.
                            split; [exact Hpc |].
                            split; [exact Hstack |].
                            split; [exact Hmemory |].
                            rewrite Hrunning, Hrocqstatus.
                            exact Hstatus.
            * discriminate Hread.
        + destruct (rocq_memory_load_word (rocq_memory rocq_state) rocq_address)
                as [rocq_value |] eqn:Hrocq_read;
                simpl in Hread; try discriminate.
            apply CorrespondFailure.
            * constructor.
            * unfold rust_state_corresponds, rust_stacks_correspond.
                split; [exact Hpc |].
                split; [exact Hstack |].
                split; [exact Hmemory |].
                rewrite Hrunning, Hrocqstatus.
                exact Hstatus.
    - unfold rust_status_corresponds in Hstatus.
        destruct Hstatus.
Qed.

Theorem rust_store_instruction_corresponds :
    forall code_length rust_state rocq_state rust_address rocq_address,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustRunning ->
        rust_word_value rust_address = rocq_address ->
        rust_result_corresponds
            (rust_execute_instruction code_length (RustSTORE rust_address) rust_state)
            (rocq_execute_instruction code_length (RocqSTORE rocq_address) rocq_state).
Proof.
    intros code_length rust_state rocq_state rust_address rocq_address
        Hstate Hrunning Haddress.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hrunning in Hstatus.
    unfold rust_execute_instruction, rocq_execute_instruction.
    rewrite Hrunning.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - assert (Hstate_corr : rust_state_corresponds rust_state rocq_state).
        {
            unfold rust_state_corresponds, rust_stacks_correspond.
            split; [exact Hpc |].
            split; [exact Hstack |].
            split; [exact Hmemory |].
            rewrite Hrunning, Hrocqstatus.
            exact Hstatus.
        }
        assert (Hnat : N.to_nat rust_address = N.to_nat rocq_address).
        { now rewrite Haddress. }
        destruct (Compare_dec.lt_dec (N.to_nat rust_address) RUST_MEMORY_SIZE)
            as [Hrust_valid | Hrust_invalid].
        + destruct (Compare_dec.lt_dec (N.to_nat rocq_address) RUST_MEMORY_SIZE)
                as [Hrocq_valid | Hrocq_invalid].
            * pose proof (rust_stack_pop_corresponds
                    (rust_stack rust_state) (rocq_stack rocq_state) Hstack) as Hpop.
                dependent destruction Hpop.
                -- rewrite <- x0, <- x.
                     simpl.
                                            assert (Hindex : Fin.of_nat_lt Hrust_valid =
                                                    Fin.of_nat_lt Hrocq_valid).
                                            {
                                                    apply Fin.to_nat_inj.
                                                    rewrite !Fin.to_nat_of_nat.
                                                    simpl.
                                                    exact Hnat.
                                            }
                                            assert (Hmemory_after : forall index,
                                                    rust_word_value
                                                        (Vector.nth
                                                            (Vector.replace (rust_memory rust_state)
                                                                (Fin.of_nat_lt Hrust_valid) rust_value)
                                                            index) =
                                                    (if Fin.eq_dec index (Fin.of_nat_lt Hrocq_valid)
                                                     then rocq_value else rocq_memory rocq_state index)).
                                            {
                                                    intro index.
                                                    destruct (Fin.eq_dec index (Fin.of_nat_lt Hrust_valid))
                                                        as [Heq | Hneq].
                                                    - subst index.
                                                        rewrite VectorSpec.nth_replace_eq.
                                                        rewrite Hindex.
                                                        destruct (Fin.eq_dec (Fin.of_nat_lt Hrocq_valid)
                                                            (Fin.of_nat_lt Hrocq_valid)); simpl; congruence.
                                                    - rewrite VectorSpec.nth_replace_neq by exact Hneq.
                                                        destruct (Fin.eq_dec index (Fin.of_nat_lt Hrocq_valid))
                                                            as [Heq | Hneq_rocq].
                                                        + subst index.
                                                            exfalso.
                                                            apply Hneq.
                                                            rewrite Hindex.
                                                            reflexivity.
                                                        + apply Hmemory.
                                            }
                     apply CorrespondSuccess.
                     apply rust_advance_pc_corresponds.
                     apply rust_state_with_memory_corresponds.
                     ++ apply rust_state_with_stack_corresponds with
                                (rust_state := rust_state) (rocq_state := rocq_state).
                            ** exact Hstate_corr.
                            ** match goal with
                                 | Hcorr : rust_stacks_correspond _ _ |- _ => exact Hcorr
                                 end.
                      ++ exact Hmemory_after.
                -- rewrite <- x0, <- x.
                     apply CorrespondFailure.
                     ++ eauto using rust_error_corresponds.
                     ++ exact Hstate_corr.
            * exfalso.
                apply Hrocq_invalid.
                now rewrite <- Hnat.
        + destruct (Compare_dec.lt_dec (N.to_nat rocq_address) RUST_MEMORY_SIZE)
                as [Hrocq_valid | Hrocq_invalid].
            * exfalso.
                apply Hrust_invalid.
                now rewrite Hnat.
            * apply CorrespondFailure.
                -- constructor.
                -- exact Hstate_corr.
    - unfold rust_status_corresponds in Hstatus.
        destruct Hstatus.
Qed.

Lemma rust_failure_correspondence_preserves_post_state :
    forall rust_error rocq_error rust_state rocq_state,
        rust_result_corresponds
            (Failure rust_error rust_state)
            (RocqFailure rocq_error rocq_state) ->
        rust_error_corresponds rust_error rocq_error /\
        rust_state_corresponds rust_state rocq_state.
Proof.
    intros rust_error rocq_error rust_state rocq_state Hfailure.
    inversion Hfailure; subst.
    auto.
Qed.

Theorem rust_halted_instruction_noop_corresponds :
    forall code_length rust_state rocq_state rust_instruction rocq_instruction,
        rust_state_corresponds rust_state rocq_state ->
        rust_status rust_state = RustHalted ->
        rust_instruction_corresponds rust_instruction rocq_instruction ->
        rust_result_corresponds
            (rust_execute_instruction code_length rust_instruction rust_state)
            (rocq_execute_instruction code_length rocq_instruction rocq_state).
Proof.
    intros code_length rust_state rocq_state rust_instruction rocq_instruction
        Hstate Hhalt _.
    destruct Hstate as [Hpc [Hstack [Hmemory Hstatus]]].
    rewrite Hhalt in Hstatus.
    destruct (rocq_status rocq_state) eqn:Hrocqstatus.
    - simpl in Hstatus.
        destruct Hstatus.
    - unfold rust_execute_instruction, rocq_execute_instruction.
        rewrite Hhalt, Hrocqstatus.
        apply CorrespondSuccess.
        unfold rust_state_corresponds, rust_stacks_correspond,
            rust_status_corresponds.
        simpl.
        split; [exact Hpc |].
        split; [exact Hstack |].
        split; [exact Hmemory |].
        rewrite Hhalt, Hrocqstatus.
        exact I.
Qed.
