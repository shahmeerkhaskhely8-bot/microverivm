(* Finite program execution and trace properties for the RV32I subset. *)

From Stdlib Require Import List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import RiscV.Word.
From MicroVeriVM Require Import RiscV.RegisterFile.
From MicroVeriVM Require Import RiscV.Machine.
From MicroVeriVM Require Import RiscV.Instruction.
From MicroVeriVM Require Import RiscV.Decoder.
From MicroVeriVM Require Import RiscV.Semantics.
From MicroVeriVM Require Import RiscV.MemorySafety.

Import ListNotations.
Open Scope N_scope.

Definition rv32_program := list N.

Definition rv32_program_fetch
    (program : rv32_program) (state : rv32_execution_state) :
    option N :=
  nth_error program
    (N.to_nat
      (N.div
        (rv32_word_value
          (rv32_pc_word
            (rv321_pc (rv32_core_state state))))
        4)).

Definition rv32_program_step
    (program : rv32_program)
    (before after : rv32_execution_state) : Prop :=
  rv321_status (rv32_core_state before) = MachineRunning /\
  exists encoding,
    rv32_program_fetch program before = Some encoding /\
    rv32_step_encoded_rel encoding before after.

Inductive rv32_program_steps (program : rv32_program) :
    rv32_execution_state -> rv32_execution_state -> Prop :=
| RV32ProgramStepsRefl :
    forall state,
      rv32_program_steps program state state
| RV32ProgramStepsCons :
    forall first middle last,
      rv32_program_step program first middle ->
      rv32_program_steps program middle last ->
      rv32_program_steps program first last.

Inductive rv32_program_steps_n (program : rv32_program) :
    nat -> rv32_execution_state -> rv32_execution_state -> Prop :=
| RV32ProgramStepsZero :
    forall state,
      rv32_program_steps_n program 0 state state
| RV32ProgramStepsNext :
    forall count first middle last,
      rv32_program_step program first middle ->
      rv32_program_steps_n program count middle last ->
      rv32_program_steps_n program (S count) first last.

Definition rv32_initial_execution_state
    (memory : rv32_memory) : rv32_execution_state :=
  {| rv32_core_state := rv321_initial_state;
     rv32_data_memory := memory |}.

Definition rv32_memory_well_formed (memory : rv32_memory) : Prop :=
  Forall (fun word => rv32_word_value word < rv32_modulus) memory.

Theorem rv32_every_memory_is_well_formed :
  forall memory, rv32_memory_well_formed memory.
Proof.
  induction memory as [|word memory IH].
  - constructor.
  - constructor.
    + apply rv32_word_range.
    + exact IH.
Qed.

Definition rv32_execution_invariant
    (state : rv32_execution_state) : Prop :=
  rv32_pc_aligned
    (rv32_pc_word (rv321_pc (rv32_core_state state))) /\
  rv32_read_register
    (rv321_registers (rv32_core_state state)) RV32X0 = rv32_word_zero /\
  rv32_memory_well_formed (rv32_data_memory state).

Theorem rv32_program_step_deterministic :
  forall program before after1 after2,
    rv32_program_step program before after1 ->
    rv32_program_step program before after2 ->
    after1 = after2.
Proof.
  intros program before after1 after2
    [Hstatus1 [encoding1 [Hfetch1 Hstep1]]]
    [Hstatus2 [encoding2 [Hfetch2 Hstep2]]].
  assert (encoding1 = encoding2) as Hencoding.
  {
    unfold rv32_program_fetch in Hfetch1, Hfetch2.
    rewrite Hfetch1 in Hfetch2.
    inversion Hfetch2.
    reflexivity.
  }
  subst encoding2.
  eapply rv32_step_encoded_rel_deterministic.
  - exact Hstep1.
  - exact Hstep2.
Qed.

Theorem rv32_program_step_has_progress :
  forall program state encoding,
    rv321_status (rv32_core_state state) = MachineRunning ->
    rv32_program_fetch program state = Some encoding ->
    exists next_state, rv32_program_step program state next_state.
Proof.
  intros program state encoding Hrunning Hfetch.
  exists (rv32_step_encoded encoding state).
  split.
  - exact Hrunning.
  - exists encoding.
    split.
    + exact Hfetch.
    + reflexivity.
Qed.

Theorem rv32_initial_nonempty_program_has_progress :
  forall encoding program memory,
    exists next_state,
      rv32_program_step (encoding :: program)
        (rv32_initial_execution_state memory) next_state.
Proof.
  intros encoding program memory.
  exists
    (rv32_step_encoded encoding (rv32_initial_execution_state memory)).
  split.
  - reflexivity.
  - exists encoding.
    split.
    + unfold rv32_program_fetch, rv32_initial_execution_state.
      simpl.
      vm_compute.
      reflexivity.
    + reflexivity.
Qed.

Theorem rv32_program_step_preserves_execution_invariant :
  forall program before after,
    rv32_program_step program before after ->
    rv32_execution_invariant before ->
    rv32_execution_invariant after.
Proof.
  intros program before after
    [_ [encoding [_ Hstep]]] [_ [_ Hmemory]].
  unfold rv32_execution_invariant.
  split.
  - rewrite <- Hstep.
    apply rv32_step_encoded_preserves_pc_alignment.
  - split.
    + rewrite <- Hstep.
      apply rv32_step_encoded_preserves_x0.
    + apply rv32_every_memory_is_well_formed.
Qed.

Theorem rv32_program_step_preserves_memory_length :
  forall program before after,
    rv32_program_step program before after ->
    length (rv32_data_memory after) = length (rv32_data_memory before).
Proof.
  intros program before after
    [_ [encoding [_ Hstep]]].
  unfold rv32_step_encoded_rel in Hstep.
  rewrite <- Hstep.
  apply rv32_step_encoded_preserves_memory_length.
Qed.

Theorem rv32_program_steps_reflexive :
  forall program state,
    rv32_program_steps program state state.
Proof.
  intros program state.
  apply RV32ProgramStepsRefl.
Qed.

Theorem rv32_program_steps_n_is_reflexive_transitive :
  forall program count initial final,
    rv32_program_steps_n program count initial final ->
    rv32_program_steps program initial final.
Proof.
  intros program count initial final Htrace.
  induction Htrace.
  - apply RV32ProgramStepsRefl.
  - econstructor.
    + exact H.
    + exact IHHtrace.
Qed.

Theorem rv32_program_steps_n_deterministic :
  forall program count initial final1 final2,
    rv32_program_steps_n program count initial final1 ->
    rv32_program_steps_n program count initial final2 ->
    final1 = final2.
Proof.
  intros program count initial final1 final2 Htrace1.
  revert final2.
  induction Htrace1; intros final2 Htrace2.
  - inversion Htrace2.
    reflexivity.
  - inversion Htrace2; subst.
    assert (middle = middle0) as Hmiddle.
    {
      eapply rv32_program_step_deterministic.
      - exact H.
      - exact H1.
    }
    subst middle0.
    eapply IHHtrace1.
    exact H2.
Qed.

Theorem rv32_program_steps_transitive :
  forall program first middle last,
    rv32_program_steps program first middle ->
    rv32_program_steps program middle last ->
    rv32_program_steps program first last.
Proof.
  intros program first middle last Hfirst Hsecond.
  revert last Hsecond.
  induction Hfirst; intros ? Hsecond.
  - exact Hsecond.
  - econstructor.
    + exact H.
    + eapply IHHfirst.
      exact Hsecond.
Qed.

Theorem rv32_program_steps_preserves_execution_invariant :
  forall program initial final,
    rv32_program_steps program initial final ->
    rv32_execution_invariant initial ->
    rv32_execution_invariant final.
Proof.
  intros program initial final Htrace.
  induction Htrace; intros Hinvariant.
  - exact Hinvariant.
  - apply IHHtrace.
    eapply rv32_program_step_preserves_execution_invariant.
    + exact H.
    + exact Hinvariant.
Qed.

Theorem rv32_program_steps_preserves_memory_length :
  forall program initial final,
    rv32_program_steps program initial final ->
    length (rv32_data_memory final) = length (rv32_data_memory initial).
Proof.
  intros program initial final Htrace.
  induction Htrace.
  - reflexivity.
  - rewrite IHHtrace.
    eapply rv32_program_step_preserves_memory_length.
    exact H.
Qed.

Theorem rv32_initial_execution_state_satisfies_invariant :
  forall memory,
    rv32_memory_well_formed memory ->
    rv32_execution_invariant
      (rv32_initial_execution_state memory).
Proof.
  intros memory Hmemory.
  unfold rv32_execution_invariant, rv32_initial_execution_state.
  simpl.
  split.
  - unfold rv32_pc_aligned, rv32_instruction_alignment.
    vm_compute.
    reflexivity.
  - split.
    + apply rv32_x0_reads_zero with
        (registers := rv32_zero_register_file).
    + exact Hmemory.
Qed.

Theorem rv32_initial_execution_state_has_well_formed_memory :
  forall memory,
    rv32_memory_well_formed memory ->
    rv32_memory_well_formed
      (rv32_data_memory (rv32_initial_execution_state memory)).
Proof.
  intros memory Hmemory.
  exact Hmemory.
Qed.

Fixpoint rv32_execute_n
    (program : rv32_program)
    (steps : nat)
    (state : rv32_execution_state) : rv32_execution_state :=
  match steps with
  | O => state
  | S remaining =>
      match rv321_status (rv32_core_state state) with
      | MachineRunning =>
          match rv32_program_fetch program state with
          | Some encoding =>
              rv32_execute_n program remaining
                (rv32_step_encoded encoding state)
          | None => state
          end
      | MachineHalted | MachineTrapped => state
      end
  end.

Theorem rv32_execute_n_preserves_execution_invariant :
  forall program steps state,
    rv32_execution_invariant state ->
    rv32_execution_invariant (rv32_execute_n program steps state).
Proof.
  intros program steps.
  induction steps as [|steps IH]; intros state Hinvariant.
  - exact Hinvariant.
  - simpl.
    destruct (rv321_status (rv32_core_state state)) eqn:Hstatus.
    + destruct (rv32_program_fetch program state) as [encoding|]
        eqn:Hfetch.
      * apply IH.
        unfold rv32_execution_invariant in *.
        destruct Hinvariant as [Hpc [Hx0 Hmemory]].
        split.
        -- apply rv32_step_encoded_preserves_pc_alignment.
        -- split.
           ++            apply rv32_step_encoded_preserves_x0.
           ++ apply rv32_every_memory_is_well_formed.
      * exact Hinvariant.
    + exact Hinvariant.
    + exact Hinvariant.
Qed.

Theorem rv32_execute_n_preserves_memory_length :
  forall program steps state,
    length (rv32_data_memory (rv32_execute_n program steps state)) =
    length (rv32_data_memory state).
Proof.
  intros program steps.
  induction steps as [|steps IH]; intros state.
  - reflexivity.
  - simpl.
    destruct (rv321_status (rv32_core_state state));
      try reflexivity.
    destruct (rv32_program_fetch program state) as [encoding|];
      try reflexivity.
    rewrite IH.
    apply rv32_step_encoded_preserves_memory_length.
Qed.

Theorem rv32_execute_n_takes_step_when_instruction_is_fetched :
  forall program remaining state encoding,
    rv321_status (rv32_core_state state) = MachineRunning ->
    rv32_program_fetch program state = Some encoding ->
    rv32_execute_n program (S remaining) state =
      rv32_execute_n program remaining
        (rv32_step_encoded encoding state).
Proof.
  intros program remaining state encoding Hstatus Hfetch.
  simpl.
  rewrite Hstatus, Hfetch.
  reflexivity.
Qed.

Theorem rv32_execute_n_functional :
  forall program steps state final1 final2,
    rv32_execute_n program steps state = final1 ->
    rv32_execute_n program steps state = final2 ->
    final1 = final2.
Proof.
  intros program steps state final1 final2 Hrun1 Hrun2.
  congruence.
Qed.

Theorem rv32_execute_n_is_a_program_trace :
  forall program steps state,
    rv32_program_steps program state
      (rv32_execute_n program steps state).
Proof.
  intros program steps.
  induction steps as [|steps IH]; intros state.
  - apply RV32ProgramStepsRefl.
  - simpl.
    destruct (rv321_status (rv32_core_state state)) eqn:Hstatus.
    + destruct (rv32_program_fetch program state) as [encoding|]
        eqn:Hfetch.
      * eapply RV32ProgramStepsCons.
        -- split.
           ++ exact Hstatus.
           ++ exists encoding.
              split.
              ** exact Hfetch.
              ** reflexivity.
        -- apply IH.
      * apply RV32ProgramStepsRefl.
    + apply RV32ProgramStepsRefl.
    + apply RV32ProgramStepsRefl.
Qed.

Theorem rv32_execute_n_has_bounded_exact_trace :
  forall program steps state,
    exists executed,
      (executed <= steps)%nat /\
      rv32_program_steps_n program executed state
        (rv32_execute_n program steps state).
Proof.
  intros program steps.
  induction steps as [|steps IH]; intros state.
  - exists 0%nat.
    split.
    + lia.
    + simpl.
      constructor.
  - simpl.
    destruct (rv321_status (rv32_core_state state)) eqn:Hstatus.
    + destruct (rv32_program_fetch program state) as [encoding|]
        eqn:Hfetch.
      * destruct (IH (rv32_step_encoded encoding state))
          as [executed [Hbound Htrace]].
        exists (S executed).
        split.
        -- lia.
        -- econstructor.
           ++ split.
              ** exact Hstatus.
              ** exists encoding.
                 split.
                 --- exact Hfetch.
                 --- reflexivity.
           ++ exact Htrace.
      * exists 0%nat.
        split.
        -- lia.
        -- constructor.
    + exists 0%nat.
      split.
      * lia.
      * constructor.
    + exists 0%nat.
      split.
      * lia.
      * constructor.
Qed.

Theorem rv32_bounded_execution_is_safe :
  forall program steps memory,
    rv32_memory_well_formed memory ->
    rv32_execution_invariant
      (rv32_execute_n program steps
        (rv32_initial_execution_state memory)).
Proof.
  intros program steps memory Hmemory.
  apply rv32_execute_n_preserves_execution_invariant.
  apply rv32_initial_execution_state_satisfies_invariant.
  exact Hmemory.
Qed.
