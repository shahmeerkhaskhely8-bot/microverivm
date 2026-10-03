(* Machine interrupt arbitration and architectural event traces for RV32I. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import RiscV.Word.
From MicroVeriVM Require Import RiscV.Machine.
From MicroVeriVM Require Import RiscV.Semantics.
From MicroVeriVM Require Import RiscV.Execution.
From MicroVeriVM Require Import RiscV.TrapHandling.
From MicroVeriVM Require Import RiscV.SystemIntegration.
From MicroVeriVM Require Import RiscV.PrivilegedCSR.

Import ListNotations.
Open Scope N_scope.

Inductive rv32_interrupt_source : Type :=
| RV32SoftwareInterrupt
| RV32TimerInterrupt
| RV32ExternalInterrupt.

Record rv32_interrupt_controller : Type := {
  rv32_global_interrupt_enable : bool;
  rv32_software_pending : bool;
  rv32_timer_pending : bool;
  rv32_external_pending : bool;
  rv32_software_enable : bool;
  rv32_timer_enable : bool;
  rv32_external_enable : bool
}.

Inductive rv32_architectural_event : Type :=
| RV32InstructionRetired (pc : rv32_pc) (encoding : N)
| RV32SynchronousTrap (pc : rv32_pc) (cause : rv32_trap_cause)
    (value : rv32_word)
| RV32InterruptAccepted (pc : rv32_pc) (source : rv32_interrupt_source)
| RV32MachineReturn (pc : rv32_pc).

Record rv32_interrupt_machine : Type := {
  rv32_interrupt_privileged : rv32_privileged_state;
  rv32_interrupt_control : rv32_interrupt_controller;
  rv32_saved_global_enable : list bool;
  rv32_architectural_trace : list rv32_architectural_event
}.

Definition rv32_interrupt_controller_initial : rv32_interrupt_controller :=
  {| rv32_global_interrupt_enable := false;
     rv32_software_pending := false;
     rv32_timer_pending := false;
     rv32_external_pending := false;
     rv32_software_enable := false;
     rv32_timer_enable := false;
     rv32_external_enable := false |}.

Definition rv32_interrupt_machine_initial
    (memory : rv32_memory)
    (trap_vector : rv32_pc) : rv32_interrupt_machine :=
  {| rv32_interrupt_privileged :=
       rv32_privileged_initial_state memory trap_vector;
     rv32_interrupt_control := rv32_interrupt_controller_initial;
     rv32_saved_global_enable := [];
     rv32_architectural_trace := [] |}.

Definition rv32_interrupt_eligible
    (control : rv32_interrupt_controller)
    (pending enabled : bool) : bool :=
  rv32_global_interrupt_enable control && pending && enabled.

Definition rv32_select_pending_interrupt
    (control : rv32_interrupt_controller) :
    option rv32_interrupt_source :=
  if rv32_interrupt_eligible control
       (rv32_external_pending control) (rv32_external_enable control)
  then Some RV32ExternalInterrupt
  else if rv32_interrupt_eligible control
       (rv32_software_pending control) (rv32_software_enable control)
  then Some RV32SoftwareInterrupt
  else if rv32_interrupt_eligible control
       (rv32_timer_pending control) (rv32_timer_enable control)
  then Some RV32TimerInterrupt
  else None.

Definition rv32_source_trap_cause
    (source : rv32_interrupt_source) : rv32_trap_cause :=
  match source with
  | RV32SoftwareInterrupt => RV32MachineSoftwareInterrupt
  | RV32TimerInterrupt => RV32MachineTimerInterrupt
  | RV32ExternalInterrupt => RV32MachineExternalInterrupt
  end.

Definition rv32_interrupt_event_value
    (source : rv32_interrupt_source) : rv32_word := rv32_word_zero.

Definition rv32_interrupt_trap_event
    (source : rv32_interrupt_source) : rv32_trap_event :=
  {| rv32_event_cause := rv32_source_trap_cause source;
     rv32_event_value := rv32_interrupt_event_value source |}.

Definition rv32_interrupt_pc
    (state : rv32_interrupt_machine) : rv32_pc :=
  rv321_pc
    (rv32_core_state
      (rv32_system_core
        (rv32_privileged_system (rv32_interrupt_privileged state)))).

Definition rv32_interrupt_raise
    (control : rv32_interrupt_controller)
    (source : rv32_interrupt_source) : rv32_interrupt_controller :=
  match source with
  | RV32SoftwareInterrupt =>
      {| rv32_global_interrupt_enable := rv32_global_interrupt_enable control;
         rv32_software_pending := true;
         rv32_timer_pending := rv32_timer_pending control;
         rv32_external_pending := rv32_external_pending control;
         rv32_software_enable := rv32_software_enable control;
         rv32_timer_enable := rv32_timer_enable control;
         rv32_external_enable := rv32_external_enable control |}
  | RV32TimerInterrupt =>
      {| rv32_global_interrupt_enable := rv32_global_interrupt_enable control;
         rv32_software_pending := rv32_software_pending control;
         rv32_timer_pending := true;
         rv32_external_pending := rv32_external_pending control;
         rv32_software_enable := rv32_software_enable control;
         rv32_timer_enable := rv32_timer_enable control;
         rv32_external_enable := rv32_external_enable control |}
  | RV32ExternalInterrupt =>
      {| rv32_global_interrupt_enable := rv32_global_interrupt_enable control;
         rv32_software_pending := rv32_software_pending control;
         rv32_timer_pending := rv32_timer_pending control;
         rv32_external_pending := true;
         rv32_software_enable := rv32_software_enable control;
         rv32_timer_enable := rv32_timer_enable control;
         rv32_external_enable := rv32_external_enable control |}
  end.

Definition rv32_interrupt_clear
    (control : rv32_interrupt_controller)
    (source : rv32_interrupt_source) : rv32_interrupt_controller :=
  match source with
  | RV32SoftwareInterrupt =>
      {| rv32_global_interrupt_enable := rv32_global_interrupt_enable control;
         rv32_software_pending := false;
         rv32_timer_pending := rv32_timer_pending control;
         rv32_external_pending := rv32_external_pending control;
         rv32_software_enable := rv32_software_enable control;
         rv32_timer_enable := rv32_timer_enable control;
         rv32_external_enable := rv32_external_enable control |}
  | RV32TimerInterrupt =>
      {| rv32_global_interrupt_enable := rv32_global_interrupt_enable control;
         rv32_software_pending := rv32_software_pending control;
         rv32_timer_pending := false;
         rv32_external_pending := rv32_external_pending control;
         rv32_software_enable := rv32_software_enable control;
         rv32_timer_enable := rv32_timer_enable control;
         rv32_external_enable := rv32_external_enable control |}
  | RV32ExternalInterrupt =>
      {| rv32_global_interrupt_enable := rv32_global_interrupt_enable control;
         rv32_software_pending := rv32_software_pending control;
         rv32_timer_pending := rv32_timer_pending control;
         rv32_external_pending := false;
         rv32_software_enable := rv32_software_enable control;
         rv32_timer_enable := rv32_timer_enable control;
         rv32_external_enable := rv32_external_enable control |}
  end.

Definition rv32_interrupt_set_global_enable
    (control : rv32_interrupt_controller)
    (enabled : bool) : rv32_interrupt_controller :=
  {| rv32_global_interrupt_enable := enabled;
     rv32_software_pending := rv32_software_pending control;
     rv32_timer_pending := rv32_timer_pending control;
     rv32_external_pending := rv32_external_pending control;
     rv32_software_enable := rv32_software_enable control;
     rv32_timer_enable := rv32_timer_enable control;
     rv32_external_enable := rv32_external_enable control |}.

Definition rv32_interrupt_set_source_enable
    (control : rv32_interrupt_controller)
    (source : rv32_interrupt_source)
    (enabled : bool) : rv32_interrupt_controller :=
  match source with
  | RV32SoftwareInterrupt =>
      {| rv32_global_interrupt_enable := rv32_global_interrupt_enable control;
         rv32_software_pending := rv32_software_pending control;
         rv32_timer_pending := rv32_timer_pending control;
         rv32_external_pending := rv32_external_pending control;
         rv32_software_enable := enabled;
         rv32_timer_enable := rv32_timer_enable control;
         rv32_external_enable := rv32_external_enable control |}
  | RV32TimerInterrupt =>
      {| rv32_global_interrupt_enable := rv32_global_interrupt_enable control;
         rv32_software_pending := rv32_software_pending control;
         rv32_timer_pending := rv32_timer_pending control;
         rv32_external_pending := rv32_external_pending control;
         rv32_software_enable := rv32_software_enable control;
         rv32_timer_enable := enabled;
         rv32_external_enable := rv32_external_enable control |}
  | RV32ExternalInterrupt =>
      {| rv32_global_interrupt_enable := rv32_global_interrupt_enable control;
         rv32_software_pending := rv32_software_pending control;
         rv32_timer_pending := rv32_timer_pending control;
         rv32_external_pending := rv32_external_pending control;
         rv32_software_enable := rv32_software_enable control;
         rv32_timer_enable := rv32_timer_enable control;
         rv32_external_enable := enabled |}
  end.

Definition rv32_interrupt_system_invariant
    (state : rv32_interrupt_machine) : Prop :=
  rv32_privileged_invariant (rv32_interrupt_privileged state) /\
  length
    (rv32_system_trap_stack
      (rv32_privileged_system (rv32_interrupt_privileged state))) =
    length (rv32_saved_global_enable state).

Definition rv32_interrupt_trap_entry
    (state : rv32_interrupt_machine)
    (source : rv32_interrupt_source) : rv32_interrupt_machine :=
  let privileged := rv32_interrupt_privileged state in
  let control := rv32_interrupt_control state in
  {| rv32_interrupt_privileged :=
       rv32_privileged_trap_entry privileged
         (rv32_interrupt_trap_event source);
     rv32_interrupt_control :=
       rv32_interrupt_set_global_enable control false;
     rv32_saved_global_enable :=
       rv32_global_interrupt_enable control :: rv32_saved_global_enable state;
     rv32_architectural_trace :=
       rv32_architectural_trace state ++
         [RV32InterruptAccepted (rv32_interrupt_pc state) source] |}.

Definition rv32_sync_trap_entry
    (state : rv32_interrupt_machine)
    (event : rv32_trap_event) : rv32_interrupt_machine :=
  let privileged := rv32_interrupt_privileged state in
  let control := rv32_interrupt_control state in
  {| rv32_interrupt_privileged :=
       rv32_privileged_trap_entry privileged event;
     rv32_interrupt_control :=
       rv32_interrupt_set_global_enable control false;
     rv32_saved_global_enable :=
       rv32_global_interrupt_enable control :: rv32_saved_global_enable state;
     rv32_architectural_trace :=
       rv32_architectural_trace state ++
         [RV32SynchronousTrap (rv32_interrupt_pc state)
           (rv32_event_cause event) (rv32_event_value event)] |}.

Definition rv32_interrupt_mret
    (state : rv32_interrupt_machine) : option rv32_interrupt_machine :=
  match rv32_privileged_mret (rv32_interrupt_privileged state) with
  | None => None
  | Some privileged =>
      match rv32_saved_global_enable state with
      | [] => None
      | saved_enable :: saved =>
          Some
            {| rv32_interrupt_privileged := privileged;
               rv32_interrupt_control :=
                 rv32_interrupt_set_global_enable
                   (rv32_interrupt_control state) saved_enable;
               rv32_saved_global_enable := saved;
               rv32_architectural_trace :=
                 rv32_architectural_trace state ++
                   [RV32MachineReturn (rv32_interrupt_pc state)] |}
      end
  end.

Definition rv32_interrupt_step_result
    (program : rv32_program)
    (state : rv32_interrupt_machine) : option rv32_interrupt_machine :=
  let privileged := rv32_interrupt_privileged state in
  let system := rv32_privileged_system privileged in
  let core := rv32_system_core system in
  match rv321_status (rv32_core_state core) with
  | MachineRunning =>
      match rv32_program_fetch program core with
      | None => None
      | Some encoding =>
          match rv32_select_pending_interrupt
            (rv32_interrupt_control state) with
          | Some source => Some (rv32_interrupt_trap_entry state source)
          | None =>
              if encoding =? rv32_machine_return_encoding then
                match rv32_interrupt_mret state with
                | Some returned => Some returned
                | None =>
                    Some
                      (rv32_sync_trap_entry state
                        {| rv32_event_cause := RV32IllegalInstruction;
                           rv32_event_value := rv32_word_wrap encoding |})
                end
              else
                match rv32_detect_exception encoding core with
                | Some event => Some (rv32_sync_trap_entry state event)
                | None =>
                    Some
                      {| rv32_interrupt_privileged :=
                           {| rv32_privileged_system :=
                                {| rv32_system_core :=
                                     rv32_step_encoded encoding core;
                                   rv32_system_trap_stack :=
                                     rv32_system_trap_stack system |};
                              rv32_privileged_csrs :=
                                rv32_privileged_csrs privileged |};
                         rv32_interrupt_control :=
                           rv32_interrupt_control state;
                         rv32_saved_global_enable :=
                           rv32_saved_global_enable state;
                         rv32_architectural_trace :=
                           rv32_architectural_trace state ++
                             [RV32InstructionRetired
                               (rv32_interrupt_pc state) encoding] |}
                end
          end
      end
  | MachineHalted | MachineTrapped => None
  end.

Definition rv32_interrupt_step
    (program : rv32_program)
    (before after : rv32_interrupt_machine) : Prop :=
  rv32_interrupt_step_result program before = Some after.

Fixpoint rv32_interrupt_execute_n
    (program : rv32_program)
    (fuel : nat)
    (state : rv32_interrupt_machine) : rv32_interrupt_machine :=
  match fuel with
  | O => state
  | S remaining =>
      match rv32_interrupt_step_result program state with
      | Some next => rv32_interrupt_execute_n program remaining next
      | None => state
      end
  end.

Inductive rv32_interrupt_steps_n
    (program : rv32_program) :
    nat -> rv32_interrupt_machine -> rv32_interrupt_machine -> Prop :=
| RV32InterruptStepsZero :
    forall state,
      rv32_interrupt_steps_n program 0 state state
| RV32InterruptStepsNext :
    forall count first middle last,
      rv32_interrupt_step program first middle ->
      rv32_interrupt_steps_n program count middle last ->
      rv32_interrupt_steps_n program (S count) first last.

Theorem rv32_external_interrupt_has_highest_priority :
  forall control,
    rv32_global_interrupt_enable control = true ->
    rv32_external_pending control = true ->
    rv32_external_enable control = true ->
    rv32_select_pending_interrupt control = Some RV32ExternalInterrupt.
Proof.
  intros control Hglobal Hpending Henabled.
  unfold rv32_select_pending_interrupt, rv32_interrupt_eligible.
  rewrite Hglobal, Hpending, Henabled.
  reflexivity.
Qed.

Theorem rv32_software_interrupt_precedes_timer :
  forall control,
    rv32_global_interrupt_enable control = true ->
    rv32_external_pending control = false ->
    rv32_software_pending control = true ->
    rv32_software_enable control = true ->
    rv32_select_pending_interrupt control = Some RV32SoftwareInterrupt.
Proof.
  intros control Hglobal Hexternal Hsoftware Henabled.
  unfold rv32_select_pending_interrupt, rv32_interrupt_eligible.
  rewrite Hglobal, Hexternal, Hsoftware, Henabled.
  reflexivity.
Qed.

Theorem rv32_timer_interrupt_is_selected_when_alone :
  forall control,
    rv32_global_interrupt_enable control = true ->
    rv32_external_pending control = false ->
    rv32_software_pending control = false ->
    rv32_timer_pending control = true ->
    rv32_timer_enable control = true ->
    rv32_select_pending_interrupt control = Some RV32TimerInterrupt.
Proof.
  intros control Hglobal Hexternal Hsoftware Htimer Henabled.
  unfold rv32_select_pending_interrupt, rv32_interrupt_eligible.
  rewrite Hglobal, Hexternal, Hsoftware, Htimer, Henabled.
  reflexivity.
Qed.

Theorem rv32_interrupts_masked_when_global_disabled :
  forall control,
    rv32_global_interrupt_enable control = false ->
    rv32_select_pending_interrupt control = None.
Proof.
  intros control Hglobal.
  unfold rv32_select_pending_interrupt, rv32_interrupt_eligible.
  rewrite Hglobal.
  reflexivity.
Qed.

Theorem rv32_interrupt_source_enable_does_not_change_pending :
  forall control source enabled,
    rv32_software_pending
      (rv32_interrupt_set_source_enable control source enabled) =
        rv32_software_pending control /\
    rv32_timer_pending
      (rv32_interrupt_set_source_enable control source enabled) =
        rv32_timer_pending control /\
    rv32_external_pending
      (rv32_interrupt_set_source_enable control source enabled) =
        rv32_external_pending control.
Proof.
  intros control source enabled.
  destruct source; simpl; auto.
Qed.

Theorem rv32_interrupt_raise_sets_selected_pending :
  forall control source,
    match source with
    | RV32SoftwareInterrupt =>
        rv32_software_pending
          (rv32_interrupt_raise control source) = true
    | RV32TimerInterrupt =>
        rv32_timer_pending
          (rv32_interrupt_raise control source) = true
    | RV32ExternalInterrupt =>
        rv32_external_pending
          (rv32_interrupt_raise control source) = true
    end.
Proof.
  intros control source.
  destruct source; reflexivity.
Qed.

Theorem rv32_interrupt_clear_clears_selected_pending :
  forall control source,
    match source with
    | RV32SoftwareInterrupt =>
        rv32_software_pending
          (rv32_interrupt_clear control source) = false
    | RV32TimerInterrupt =>
        rv32_timer_pending
          (rv32_interrupt_clear control source) = false
    | RV32ExternalInterrupt =>
        rv32_external_pending
          (rv32_interrupt_clear control source) = false
    end.
Proof.
  intros control source.
  destruct source; reflexivity.
Qed.

Theorem rv32_interrupt_trap_cause_codes :
  rv32_trap_cause_code RV32MachineSoftwareInterrupt = 3 /\
  rv32_trap_cause_code RV32MachineTimerInterrupt = 7 /\
  rv32_trap_cause_code RV32MachineExternalInterrupt = 11.
Proof.
  repeat split; reflexivity.
Qed.

Theorem rv32_interrupt_trap_mcause_sets_interrupt_bit :
  forall state source,
    rv32_word_value
      (rv32_mcause
        (rv32_privileged_csrs
          (rv32_interrupt_privileged
            (rv32_interrupt_trap_entry state source)))) =
      2147483648 +
        rv32_trap_cause_code (rv32_source_trap_cause source).
Proof.
  intros state source.
  destruct source; reflexivity.
Qed.

Theorem rv32_interrupt_trap_entry_preserves_invariant :
  forall state source,
    rv32_interrupt_system_invariant state ->
    rv32_interrupt_system_invariant
      (rv32_interrupt_trap_entry state source).
Proof.
  intros state source [Hsafe Hdepth].
  unfold rv32_interrupt_system_invariant,
    rv32_interrupt_trap_entry.
  simpl.
  split.
  - unfold rv32_privileged_invariant.
    apply rv32_trap_entry_preserves_safety.
    exact Hsafe.
  - simpl.
    rewrite Hdepth.
    lia.
Qed.

Theorem rv32_sync_trap_entry_preserves_invariant :
  forall state event,
    rv32_interrupt_system_invariant state ->
    rv32_interrupt_system_invariant
      (rv32_sync_trap_entry state event).
Proof.
  intros state event [Hsafe Hdepth].
  unfold rv32_interrupt_system_invariant, rv32_sync_trap_entry.
  simpl.
  split.
  - unfold rv32_privileged_invariant.
    apply rv32_trap_entry_preserves_safety.
    exact Hsafe.
  - simpl.
    rewrite Hdepth.
    lia.
Qed.

Theorem rv32_interrupt_mret_preserves_invariant :
  forall state next,
    rv32_interrupt_mret state = Some next ->
    rv32_interrupt_system_invariant state ->
    rv32_interrupt_system_invariant next.
Proof.
  intros state next Hmret [Hsafe Hdepth].
  unfold rv32_interrupt_mret in Hmret.
  destruct
    (rv32_privileged_mret (rv32_interrupt_privileged state))
    as [privileged|] eqn:Hpriv; try discriminate.
  destruct (rv32_saved_global_enable state) as [|saved tail]
    eqn:Hsaved; try discriminate.
  inversion Hmret; subst next.
  unfold rv32_interrupt_system_invariant.
  simpl.
  split.
  - eapply rv32_privileged_mret_preserves_safety; eassumption.
  - simpl in Hdepth.
    pose proof
      (rv32_privileged_mret_decreases_trap_depth
        (rv32_interrupt_privileged state) privileged Hpriv) as Hframes.
    lia.
Qed.

Theorem rv32_interrupt_step_result_deterministic :
  forall program state next1 next2,
    rv32_interrupt_step_result program state = Some next1 ->
    rv32_interrupt_step_result program state = Some next2 ->
    next1 = next2.
Proof.
  intros program state next1 next2 H1 H2.
  congruence.
Qed.

Theorem rv32_interrupt_step_preserves_invariant :
  forall program before after,
    rv32_interrupt_step program before after ->
    rv32_interrupt_system_invariant before ->
    rv32_interrupt_system_invariant after.
Proof.
  intros program before after Hstep [Hsafe Hdepth].
  unfold rv32_interrupt_step in Hstep.
  unfold rv32_interrupt_step_result in Hstep.
  destruct
    (rv321_status
      (rv32_core_state
        (rv32_system_core
          (rv32_privileged_system (rv32_interrupt_privileged before)))))
    eqn:Hstatus; try discriminate.
  destruct
    (rv32_program_fetch program
      (rv32_system_core
        (rv32_privileged_system (rv32_interrupt_privileged before))))
    as [encoding|] eqn:Hfetch; try discriminate.
  destruct (rv32_select_pending_interrupt
    (rv32_interrupt_control before)) as [source|] eqn:Hselected.
  - inversion Hstep; subst after.
    apply rv32_interrupt_trap_entry_preserves_invariant.
    split; assumption.
  - destruct (encoding =? rv32_machine_return_encoding) eqn:Hmret.
    + destruct (rv32_interrupt_mret before) as [returned|]
        eqn:Hreturn.
      * inversion Hstep; subst after.
        eapply rv32_interrupt_mret_preserves_invariant.
        -- exact Hreturn.
        -- split; assumption.
      * inversion Hstep; subst after.
        apply rv32_sync_trap_entry_preserves_invariant.
        split; assumption.
    + destruct (rv32_detect_exception encoding
        (rv32_system_core
          (rv32_privileged_system (rv32_interrupt_privileged before))))
        as [event|] eqn:Hexception.
      * inversion Hstep; subst after.
        apply rv32_sync_trap_entry_preserves_invariant.
        split; assumption.
      * inversion Hstep; subst after.
        unfold rv32_interrupt_system_invariant.
        simpl.
        split.
        -- unfold rv32_privileged_invariant, rv32_system_invariant,
             rv32_execution_invariant in *.
           destruct Hsafe as [Hpc [Hx0 Hmemory]].
           split.
           ++ apply rv32_step_encoded_preserves_pc_alignment.
           ++ split.
              ** apply rv32_step_encoded_preserves_x0.
              ** apply rv32_every_memory_is_well_formed.
        -- exact Hdepth.
Qed.

Theorem rv32_interrupt_execute_n_preserves_invariant :
  forall program fuel state,
    rv32_interrupt_system_invariant state ->
    rv32_interrupt_system_invariant
      (rv32_interrupt_execute_n program fuel state).
Proof.
  intros program fuel.
  induction fuel as [|fuel IH]; intros state Hinvariant.
  - exact Hinvariant.
  - simpl.
    destruct (rv32_interrupt_step_result program state)
      as [next|] eqn:Hstep.
    + apply IH.
      eapply rv32_interrupt_step_preserves_invariant.
      * exact Hstep.
      * exact Hinvariant.
    + exact Hinvariant.
Qed.

Theorem rv32_interrupt_steps_n_preserves_invariant :
  forall program count initial final,
    rv32_interrupt_steps_n program count initial final ->
    rv32_interrupt_system_invariant initial ->
    rv32_interrupt_system_invariant final.
Proof.
  intros program count initial final Htrace.
  induction Htrace; intros Hinvariant.
  - exact Hinvariant.
  - apply IHHtrace.
    eapply rv32_interrupt_step_preserves_invariant; eassumption.
Qed.

Theorem rv32_interrupt_steps_n_deterministic :
  forall program count initial final1 final2,
    rv32_interrupt_steps_n program count initial final1 ->
    rv32_interrupt_steps_n program count initial final2 ->
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
      apply
        (rv32_interrupt_step_result_deterministic
          program first middle middle0).
      - exact H.
      - exact H1.
    }
    subst middle0.
    eapply IHHtrace1.
    exact H2.
Qed.

Theorem rv32_interrupt_execute_n_has_bounded_trace :
  forall program fuel state,
    exists executed,
      (executed <= fuel)%nat /\
      rv32_interrupt_steps_n program executed state
        (rv32_interrupt_execute_n program fuel state).
Proof.
  intros program fuel.
  induction fuel as [|fuel IH]; intros state.
  - exists 0%nat.
    split; [lia|].
    simpl.
    constructor.
  - simpl.
    destruct (rv32_interrupt_step_result program state)
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

Theorem rv32_interrupt_execute_n_is_functional :
  forall program fuel state result1 result2,
    rv32_interrupt_execute_n program fuel state = result1 ->
    rv32_interrupt_execute_n program fuel state = result2 ->
    result1 = result2.
Proof.
  intros program fuel state result1 result2 H1 H2.
  congruence.
Qed.

Theorem rv32_interrupt_system_initial_state_is_safe :
  forall memory trap_vector,
    rv32_interrupt_system_invariant
      (rv32_interrupt_machine_initial memory trap_vector).
Proof.
  intros memory trap_vector.
  unfold rv32_interrupt_system_invariant,
    rv32_interrupt_machine_initial,
    rv32_interrupt_controller_initial.
  simpl.
  split.
  - unfold rv32_privileged_invariant, rv32_system_invariant,
      rv32_privileged_initial_state.
    apply rv32_initial_execution_state_satisfies_invariant.
    apply rv32_every_memory_is_well_formed.
  - reflexivity.
Qed.

Theorem rv32_interrupt_step_result_appends_one_event :
  forall program state next,
    rv32_interrupt_step_result program state = Some next ->
    length (rv32_architectural_trace next) =
      S (length (rv32_architectural_trace state)).
Proof.
  intros program state next Hstep.
  unfold rv32_interrupt_step_result in Hstep.
  destruct
    (rv321_status
      (rv32_core_state
        (rv32_system_core
          (rv32_privileged_system (rv32_interrupt_privileged state)))));
    try discriminate.
  destruct
    (rv32_program_fetch program
      (rv32_system_core
        (rv32_privileged_system (rv32_interrupt_privileged state))))
    as [encoding|] eqn:Hfetch; try discriminate.
  destruct (rv32_select_pending_interrupt
    (rv32_interrupt_control state)) as [source|] eqn:Hsource.
  - inversion Hstep; subst next.
    simpl.
    rewrite length_app.
    simpl.
    lia.
  - destruct (encoding =? rv32_machine_return_encoding) eqn:Hmret.
    + destruct (rv32_interrupt_mret state) as [returned|]
        eqn:Hreturn.
      * inversion Hstep; subst next.
        unfold rv32_interrupt_mret in Hreturn.
        destruct (rv32_privileged_mret (rv32_interrupt_privileged state))
          as [privileged|]; try discriminate.
        destruct (rv32_saved_global_enable state) as [|saved tail];
          try discriminate.
        inversion Hreturn; subst returned.
        simpl.
        rewrite length_app.
        simpl.
        lia.
      * inversion Hstep; subst next.
        simpl.
        rewrite length_app.
        simpl.
        lia.
    + destruct (rv32_detect_exception encoding
        (rv32_system_core
          (rv32_privileged_system (rv32_interrupt_privileged state))))
        as [event|] eqn:Hevent.
      * inversion Hstep; subst next.
        simpl.
        rewrite length_app.
        simpl.
        lia.
      * inversion Hstep; subst next.
        simpl.
        rewrite length_app.
        simpl.
        lia.
Qed.

Theorem rv32_interrupt_execute_n_trace_length_bound :
  forall program fuel state,
    (length
      (rv32_architectural_trace
        (rv32_interrupt_execute_n program fuel state)) <=
    length (rv32_architectural_trace state) + fuel)%nat.
Proof.
  intros program fuel.
  induction fuel as [|fuel IH]; intros state.
  - simpl.
    lia.
  - simpl.
    destruct (rv32_interrupt_step_result program state)
      as [next|] eqn:Hstep.
    + pose proof
        (rv32_interrupt_step_result_appends_one_event
          program state next Hstep) as Hevents.
      specialize (IH next).
      lia.
    + lia.
Qed.

Definition rv32_interrupt_application_initial
    (image : rv32_binary_image)
    (trap_vector : rv32_pc) : rv32_interrupt_machine :=
  rv32_interrupt_machine_initial
    (rv32_binary_data_words image) trap_vector.

Definition rv32_run_application_with_interrupts
    (image : rv32_binary_image)
    (trap_vector : rv32_pc)
    (fuel : nat) : rv32_interrupt_machine :=
  rv32_interrupt_execute_n
    (rv32_load_binary_text image) fuel
    (rv32_interrupt_application_initial image trap_vector).

Theorem rv32_run_application_with_interrupts_is_safe :
  forall image trap_vector fuel,
    rv32_interrupt_system_invariant
      (rv32_run_application_with_interrupts image trap_vector fuel).
Proof.
  intros image trap_vector fuel.
  unfold rv32_run_application_with_interrupts.
  apply rv32_interrupt_execute_n_preserves_invariant.
  apply rv32_interrupt_system_initial_state_is_safe.
Qed.

Theorem rv32_run_application_with_interrupts_has_bounded_trace :
  forall image trap_vector fuel,
    exists executed,
      (executed <= fuel)%nat /\
      rv32_interrupt_steps_n
        (rv32_load_binary_text image) executed
        (rv32_interrupt_application_initial image trap_vector)
        (rv32_run_application_with_interrupts image trap_vector fuel).
Proof.
  intros image trap_vector fuel.
  unfold rv32_run_application_with_interrupts.
  apply rv32_interrupt_execute_n_has_bounded_trace.
Qed.

Theorem rv32_run_application_with_interrupts_event_bound :
  forall image trap_vector fuel,
    (length
      (rv32_architectural_trace
        (rv32_run_application_with_interrupts image trap_vector fuel)) <=
    fuel)%nat.
Proof.
  intros image trap_vector fuel.
  unfold rv32_run_application_with_interrupts,
    rv32_interrupt_application_initial,
    rv32_interrupt_machine_initial.
  simpl.
  apply rv32_interrupt_execute_n_trace_length_bound.
Qed.
