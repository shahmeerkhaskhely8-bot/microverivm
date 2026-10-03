(* Precise retirement/event records with explicit before/after PCs. *)

From Stdlib Require Import List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import RiscV.Word.
From MicroVeriVM Require Import RiscV.Machine.
From MicroVeriVM Require Import RiscV.Semantics.
From MicroVeriVM Require Import RiscV.Execution.
From MicroVeriVM Require Import RiscV.TrapHandling.
From MicroVeriVM Require Import RiscV.SystemIntegration.
From MicroVeriVM Require Import RiscV.PrivilegedCSR.
From MicroVeriVM Require Import RiscV.Interrupts.

Import ListNotations.
Open Scope N_scope.

Inductive rv32_pc_event_kind : Type :=
| RV32RetiredInstruction (encoding : N)
| RV32TakenInterrupt (source : rv32_interrupt_source)
| RV32SynchronousException (cause : rv32_trap_cause)
| RV32ReturnedFromTrap.

Record rv32_pc_event : Type := {
  rv32_event_pc_before : rv32_pc;
  rv32_event_pc_after : rv32_pc;
  rv32_event_kind : rv32_pc_event_kind
}.

Record rv32_pc_tracked_machine : Type := {
  rv32_pc_trace_origin : rv32_pc;
  rv32_pc_tracked_core : rv32_interrupt_machine;
  rv32_pc_event_trace : list rv32_pc_event
}.

Definition rv32_pc_tracked_initial
    (memory : rv32_memory)
    (trap_vector : rv32_pc) : rv32_pc_tracked_machine :=
  {| rv32_pc_trace_origin := rv32_pc_zero;
     rv32_pc_tracked_core :=
       rv32_interrupt_machine_initial memory trap_vector;
     rv32_pc_event_trace := [] |}.

Definition rv32_tracked_current_pc
    (state : rv32_pc_tracked_machine) : rv32_pc :=
  rv32_interrupt_pc (rv32_pc_tracked_core state).

Definition rv32_make_pc_event
    (before after : rv32_interrupt_machine)
    (kind : rv32_pc_event_kind) : rv32_pc_event :=
  {| rv32_event_pc_before := rv32_interrupt_pc before;
     rv32_event_pc_after := rv32_interrupt_pc after;
     rv32_event_kind := kind |}.

Definition rv32_classify_interrupt_step
    (program : rv32_program)
    (before after : rv32_interrupt_machine) :
    option rv32_pc_event_kind :=
  let privileged := rv32_interrupt_privileged before in
  let core := rv32_system_core (rv32_privileged_system privileged) in
  match rv32_program_fetch program core with
  | None => None
  | Some encoding =>
      match rv32_select_pending_interrupt
        (rv32_interrupt_control before) with
      | Some source => Some (RV32TakenInterrupt source)
      | None =>
          if encoding =? rv32_machine_return_encoding then
            match rv32_interrupt_mret before with
            | Some _ => Some RV32ReturnedFromTrap
            | None => Some (RV32SynchronousException RV32IllegalInstruction)
            end
          else
            match rv32_detect_exception encoding core with
            | Some event =>
                Some (RV32SynchronousException (rv32_event_cause event))
            | None => Some (RV32RetiredInstruction encoding)
            end
      end
  end.

Definition rv32_pc_tracked_step_result
    (program : rv32_program)
    (state : rv32_pc_tracked_machine) :
    option rv32_pc_tracked_machine :=
  match rv32_interrupt_step_result program (rv32_pc_tracked_core state) with
  | None => None
  | Some next =>
      match rv32_classify_interrupt_step
        program (rv32_pc_tracked_core state) next with
      | None => None
      | Some kind =>
          Some
            {| rv32_pc_trace_origin := rv32_pc_trace_origin state;
               rv32_pc_tracked_core := next;
               rv32_pc_event_trace :=
                 rv32_pc_event_trace state ++
                   [rv32_make_pc_event
                     (rv32_pc_tracked_core state) next kind] |}
      end
  end.

Definition rv32_pc_tracked_step
    (program : rv32_program)
    (before after : rv32_pc_tracked_machine) : Prop :=
  rv32_pc_tracked_step_result program before = Some after.

Fixpoint rv32_pc_tracked_execute_n
    (program : rv32_program)
    (fuel : nat)
    (state : rv32_pc_tracked_machine) : rv32_pc_tracked_machine :=
  match fuel with
  | O => state
  | S remaining =>
      match rv32_pc_tracked_step_result program state with
      | Some next => rv32_pc_tracked_execute_n program remaining next
      | None => state
      end
  end.

Inductive rv32_pc_tracked_steps_n
    (program : rv32_program) :
    nat -> rv32_pc_tracked_machine -> rv32_pc_tracked_machine -> Prop :=
| RV32PCTrackedStepsZero :
    forall state,
      rv32_pc_tracked_steps_n program 0 state state
| RV32PCTrackedStepsNext :
    forall count first middle last,
      rv32_pc_tracked_step program first middle ->
      rv32_pc_tracked_steps_n program count middle last ->
      rv32_pc_tracked_steps_n program (S count) first last.

Inductive rv32_pc_trace_consistent :
    rv32_pc -> list rv32_pc_event -> rv32_pc -> Prop :=
| RV32PCTraceEmpty :
    forall pc,
      rv32_pc_trace_consistent pc [] pc
| RV32PCTraceSnoc :
    forall origin trace current next event,
      rv32_pc_trace_consistent origin trace current ->
      rv32_event_pc_before event = current ->
      rv32_event_pc_after event = next ->
      rv32_pc_trace_consistent origin (trace ++ [event]) next.

Theorem rv32_pc_trace_consistent_append :
  forall origin trace current event next,
    rv32_pc_trace_consistent origin trace current ->
    rv32_event_pc_before event = current ->
    rv32_event_pc_after event = next ->
    rv32_pc_trace_consistent origin (trace ++ [event]) next.
Proof.
  intros.
  econstructor; eassumption.
Qed.

Definition rv32_pc_tracking_invariant
    (state : rv32_pc_tracked_machine) : Prop :=
  rv32_interrupt_system_invariant (rv32_pc_tracked_core state) /\
  rv32_pc_trace_consistent
    (rv32_pc_trace_origin state)
    (rv32_pc_event_trace state)
    (rv32_tracked_current_pc state).

Theorem rv32_pc_event_endpoints_are_aligned :
  forall event,
    rv32_pc_aligned (rv32_pc_word (rv32_event_pc_before event)) /\
    rv32_pc_aligned (rv32_pc_word (rv32_event_pc_after event)).
Proof.
  intros event.
  split; apply rv32_pc_alignment_holds.
Qed.

Theorem rv32_classify_successful_interrupt_step :
  forall program before after,
    rv32_interrupt_step_result program before = Some after ->
    exists kind,
      rv32_classify_interrupt_step program before after = Some kind.
Proof.
  intros program before after Hstep.
  unfold rv32_interrupt_step_result in Hstep.
  destruct
    (rv321_status
      (rv32_core_state
        (rv32_system_core
          (rv32_privileged_system (rv32_interrupt_privileged before)))));
    try discriminate.
  destruct
    (rv32_program_fetch program
      (rv32_system_core
        (rv32_privileged_system (rv32_interrupt_privileged before))))
    as [encoding|] eqn:Hfetch; try discriminate.
  unfold rv32_classify_interrupt_step.
  rewrite Hfetch.
  destruct (rv32_select_pending_interrupt
    (rv32_interrupt_control before)) as [source|].
  - eexists. reflexivity.
  - destruct (encoding =? rv32_machine_return_encoding).
    + destruct (rv32_interrupt_mret before); eexists; reflexivity.
    + destruct (rv32_detect_exception encoding
        (rv32_system_core
          (rv32_privileged_system (rv32_interrupt_privileged before))));
        eexists; reflexivity.
Qed.

Theorem rv32_pc_tracked_step_result_deterministic :
  forall program state after1 after2,
    rv32_pc_tracked_step_result program state = Some after1 ->
    rv32_pc_tracked_step_result program state = Some after2 ->
    after1 = after2.
Proof.
  intros program state after1 after2 H1 H2.
  congruence.
Qed.

Theorem rv32_pc_tracked_step_appends_precise_event :
  forall program before after,
    rv32_pc_tracked_step_result program before = Some after ->
    exists event,
      rv32_pc_event_trace after = rv32_pc_event_trace before ++ [event] /\
      rv32_event_pc_before event = rv32_tracked_current_pc before /\
      rv32_event_pc_after event = rv32_tracked_current_pc after /\
      exists kind,
        rv32_classify_interrupt_step program
          (rv32_pc_tracked_core before)
          (rv32_pc_tracked_core after) = Some kind /\
        rv32_event_kind event = kind.
Proof.
  intros program before after Hstep.
  unfold rv32_pc_tracked_step_result in Hstep.
  destruct
    (rv32_interrupt_step_result program (rv32_pc_tracked_core before))
    as [next|] eqn:Hcore; try discriminate.
  destruct (rv32_classify_interrupt_step program
    (rv32_pc_tracked_core before) next) as [kind|] eqn:Hkind;
    try discriminate.
  inversion Hstep; subst after.
  exists (rv32_make_pc_event (rv32_pc_tracked_core before) next kind).
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * exists kind.
        split.
        -- exact Hkind.
        -- reflexivity.
Qed.

Theorem rv32_pc_tracked_step_preserves_invariant :
  forall program before after,
    rv32_pc_tracked_step program before after ->
    rv32_pc_tracking_invariant before ->
    rv32_pc_tracking_invariant after.
Proof.
  intros program before after Hstep [Hsystem Htrace].
  unfold rv32_pc_tracked_step in Hstep.
  unfold rv32_pc_tracked_step_result in Hstep.
  destruct
    (rv32_interrupt_step_result program (rv32_pc_tracked_core before))
    as [next|] eqn:Hinterrupt; try discriminate.
  destruct (rv32_classify_interrupt_step program
    (rv32_pc_tracked_core before) next) as [kind|] eqn:Hkind;
    try discriminate.
  inversion Hstep; subst after.
  split.
  - eapply rv32_interrupt_step_preserves_invariant; eassumption.
  - eapply RV32PCTraceSnoc.
    + exact Htrace.
    + reflexivity.
    + reflexivity.
Qed.

Theorem rv32_pc_tracked_step_deterministic :
  forall program before after1 after2,
    rv32_pc_tracked_step program before after1 ->
    rv32_pc_tracked_step program before after2 ->
    after1 = after2.
Proof.
  intros program before after1 after2 H1 H2.
  unfold rv32_pc_tracked_step in *.
  eapply rv32_pc_tracked_step_result_deterministic; eassumption.
Qed.

Theorem rv32_pc_tracked_initial_satisfies_invariant :
  forall memory trap_vector,
    rv32_pc_tracking_invariant
      (rv32_pc_tracked_initial memory trap_vector).
Proof.
  intros memory trap_vector.
  unfold rv32_pc_tracking_invariant, rv32_pc_tracked_initial,
    rv32_tracked_current_pc.
  simpl.
  split.
  - apply rv32_interrupt_system_initial_state_is_safe.
  - constructor.
Qed.

Theorem rv32_pc_tracked_step_advances_event_count :
  forall program before after,
    rv32_pc_tracked_step program before after ->
    length (rv32_pc_event_trace after) =
      S (length (rv32_pc_event_trace before)).
Proof.
  intros program before after Hstep.
  unfold rv32_pc_tracked_step, rv32_pc_tracked_step_result in Hstep.
  destruct
    (rv32_interrupt_step_result program (rv32_pc_tracked_core before))
    as [next|] eqn:Hinterrupt; try discriminate.
  destruct (rv32_classify_interrupt_step program
    (rv32_pc_tracked_core before) next) as [kind|] eqn:Hkind;
    try discriminate.
  inversion Hstep; subst after.
  simpl.
  rewrite length_app.
  simpl.
  lia.
Qed.

Theorem rv32_pc_tracked_steps_n_preserves_invariant :
  forall program count initial final,
    rv32_pc_tracked_steps_n program count initial final ->
    rv32_pc_tracking_invariant initial ->
    rv32_pc_tracking_invariant final.
Proof.
  intros program count initial final Htrace.
  induction Htrace; intros Hinvariant.
  - exact Hinvariant.
  - apply IHHtrace.
    eapply rv32_pc_tracked_step_preserves_invariant; eassumption.
Qed.

Theorem rv32_pc_tracked_steps_n_deterministic :
  forall program count initial final1 final2,
    rv32_pc_tracked_steps_n program count initial final1 ->
    rv32_pc_tracked_steps_n program count initial final2 ->
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
      eapply rv32_pc_tracked_step_deterministic; eassumption.
    }
    subst middle0.
    eapply IHHtrace1.
    exact H2.
Qed.

Theorem rv32_pc_tracked_execute_n_preserves_invariant :
  forall program fuel state,
    rv32_pc_tracking_invariant state ->
    rv32_pc_tracking_invariant
      (rv32_pc_tracked_execute_n program fuel state).
Proof.
  intros program fuel.
  induction fuel as [|fuel IH]; intros state Hinvariant.
  - exact Hinvariant.
  - simpl.
    destruct (rv32_pc_tracked_step_result program state)
      as [next|] eqn:Hstep.
    + apply IH.
      eapply rv32_pc_tracked_step_preserves_invariant.
      * exact Hstep.
      * exact Hinvariant.
    + exact Hinvariant.
Qed.

Theorem rv32_pc_tracked_execute_n_has_bounded_trace :
  forall program fuel state,
    exists executed,
      (executed <= fuel)%nat /\
      rv32_pc_tracked_steps_n program executed state
        (rv32_pc_tracked_execute_n program fuel state).
Proof.
  intros program fuel.
  induction fuel as [|fuel IH]; intros state.
  - exists 0%nat.
    split; [lia|].
    simpl.
    constructor.
  - simpl.
    destruct (rv32_pc_tracked_step_result program state)
      as [next|] eqn:Hstep.
    + destruct (IH next) as [executed [Hbound Htrace]].
      exists (S executed).
      split; [lia|].
      econstructor.
      * exact Hstep.
      * exact Htrace.
    + exists 0%nat.
      split; [lia|].
      constructor.
Qed.

Theorem rv32_pc_tracked_execute_n_event_count_bound :
  forall program fuel state,
    (length (rv32_pc_event_trace
      (rv32_pc_tracked_execute_n program fuel state)) <=
     length (rv32_pc_event_trace state) + fuel)%nat.
Proof.
  intros program fuel.
  induction fuel as [|fuel IH]; intros state.
  - simpl.
    lia.
  - simpl.
    destruct (rv32_pc_tracked_step_result program state)
      as [next|] eqn:Hstep.
    + assert (Happend :
        length (rv32_pc_event_trace next) =
          S (length (rv32_pc_event_trace state))).
      {
        eapply rv32_pc_tracked_step_advances_event_count.
        exact Hstep.
      }
      specialize (IH next).
      lia.
    + lia.
Qed.

Theorem rv32_pc_tracked_run_preserves_pc_chain :
  forall program fuel state,
    rv32_pc_tracking_invariant state ->
    rv32_pc_trace_consistent
      (rv32_pc_trace_origin
        (rv32_pc_tracked_execute_n program fuel state))
      (rv32_pc_event_trace
        (rv32_pc_tracked_execute_n program fuel state))
      (rv32_tracked_current_pc
        (rv32_pc_tracked_execute_n program fuel state)).
Proof.
  intros program fuel state Hinvariant.
  pose proof
    (rv32_pc_tracked_execute_n_preserves_invariant
      program fuel state Hinvariant) as Hfinal.
  exact (proj2 Hfinal).
Qed.

Definition rv32_pc_tracked_application_initial
    (image : rv32_binary_image)
    (trap_vector : rv32_pc) : rv32_pc_tracked_machine :=
  rv32_pc_tracked_initial
    (rv32_binary_data_words image) trap_vector.

Definition rv32_run_application_with_pc_trace
    (image : rv32_binary_image)
    (trap_vector : rv32_pc)
    (fuel : nat) : rv32_pc_tracked_machine :=
  rv32_pc_tracked_execute_n
    (rv32_load_binary_text image) fuel
    (rv32_pc_tracked_application_initial image trap_vector).

Theorem rv32_run_application_with_pc_trace_is_safe :
  forall image trap_vector fuel,
    rv32_pc_tracking_invariant
      (rv32_run_application_with_pc_trace image trap_vector fuel).
Proof.
  intros image trap_vector fuel.
  unfold rv32_run_application_with_pc_trace.
  apply rv32_pc_tracked_execute_n_preserves_invariant.
  apply rv32_pc_tracked_initial_satisfies_invariant.
Qed.

Theorem rv32_run_application_with_pc_trace_has_bounded_steps :
  forall image trap_vector fuel,
    exists executed,
      (executed <= fuel)%nat /\
      rv32_pc_tracked_steps_n
        (rv32_load_binary_text image) executed
        (rv32_pc_tracked_application_initial image trap_vector)
        (rv32_run_application_with_pc_trace image trap_vector fuel).
Proof.
  intros image trap_vector fuel.
  unfold rv32_run_application_with_pc_trace.
  apply rv32_pc_tracked_execute_n_has_bounded_trace.
Qed.

Theorem rv32_run_application_with_pc_trace_event_bound :
  forall image trap_vector fuel,
    (length (rv32_pc_event_trace
      (rv32_run_application_with_pc_trace image trap_vector fuel)) <= fuel)%nat.
Proof.
  intros image trap_vector fuel.
  unfold rv32_run_application_with_pc_trace,
    rv32_pc_tracked_application_initial,
    rv32_pc_tracked_initial.
  simpl.
  apply rv32_pc_tracked_execute_n_event_count_bound.
Qed.

Theorem rv32_run_application_with_pc_trace_deterministic :
  forall image trap_vector fuel initial final1 final2,
    initial = rv32_pc_tracked_application_initial image trap_vector ->
    rv32_pc_tracked_steps_n (rv32_load_binary_text image) fuel
      initial final1 ->
    rv32_pc_tracked_steps_n (rv32_load_binary_text image) fuel
      initial final2 ->
    final1 = final2.
Proof.
  intros image trap_vector fuel initial final1 final2 Hinitial
    Htrace1 Htrace2.
  subst initial.
  eapply rv32_pc_tracked_steps_n_deterministic; eassumption.
Qed.
