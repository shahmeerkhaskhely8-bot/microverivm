(* Direct-mode machine CSRs and CSR-driven exception execution. *)

From Stdlib Require Import List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import RiscV.Word.
From MicroVeriVM Require Import RiscV.RegisterFile.
From MicroVeriVM Require Import RiscV.Machine.
From MicroVeriVM Require Import RiscV.Semantics.
From MicroVeriVM Require Import RiscV.Execution.
From MicroVeriVM Require Import RiscV.TrapHandling.
From MicroVeriVM Require Import RiscV.SystemIntegration.

Import ListNotations.
Open Scope N_scope.

Definition rv32_csr_mtvec : N := 773.
Definition rv32_csr_mepc : N := 833.
Definition rv32_csr_mcause : N := 834.
Definition rv32_csr_mtval : N := 835.

Record rv32_machine_csrs : Type := {
  rv32_mtvec : rv32_pc;
  rv32_mepc : rv32_pc;
  rv32_mcause : rv32_word;
  rv32_mtval : rv32_word
}.

Record rv32_privileged_state : Type := {
  rv32_privileged_system : rv32_system_state;
  rv32_privileged_csrs : rv32_machine_csrs
}.

Definition rv32_csr_read
    (csrs : rv32_machine_csrs) (address : N) : option rv32_word :=
  if address =? rv32_csr_mtvec then Some (rv32_pc_word (rv32_mtvec csrs))
  else if address =? rv32_csr_mepc then Some (rv32_pc_word (rv32_mepc csrs))
  else if address =? rv32_csr_mcause then Some (rv32_mcause csrs)
  else if address =? rv32_csr_mtval then Some (rv32_mtval csrs)
  else None.

Definition rv32_csr_write
    (csrs : rv32_machine_csrs)
    (address : N)
    (value : rv32_word) : option rv32_machine_csrs :=
  if address =? rv32_csr_mtvec then
    match rv32_pc_from_word value with
    | Some vector =>
        Some
          {| rv32_mtvec := vector;
             rv32_mepc := rv32_mepc csrs;
             rv32_mcause := rv32_mcause csrs;
             rv32_mtval := rv32_mtval csrs |}
    | None => None
    end
  else if address =? rv32_csr_mepc then
    match rv32_pc_from_word value with
    | Some pc =>
        Some
          {| rv32_mtvec := rv32_mtvec csrs;
             rv32_mepc := pc;
             rv32_mcause := rv32_mcause csrs;
             rv32_mtval := rv32_mtval csrs |}
    | None => None
    end
  else if address =? rv32_csr_mcause then
    Some
      {| rv32_mtvec := rv32_mtvec csrs;
         rv32_mepc := rv32_mepc csrs;
         rv32_mcause := value;
         rv32_mtval := rv32_mtval csrs |}
  else if address =? rv32_csr_mtval then
    Some
      {| rv32_mtvec := rv32_mtvec csrs;
         rv32_mepc := rv32_mepc csrs;
         rv32_mcause := rv32_mcause csrs;
         rv32_mtval := value |}
  else None.

Definition rv32_trap_cause_code (cause : rv32_trap_cause) : N :=
  match cause with
  | RV32InstructionAddressMisaligned => 0
  | RV32IllegalInstruction => 2
  | RV32LoadAddressMisaligned => 4
  | RV32LoadAccessFault => 5
  | RV32StoreAddressMisaligned => 6
  | RV32StoreAccessFault => 7
  | RV32EnvironmentCall => 11
  | RV32MachineSoftwareInterrupt => 3
  | RV32MachineTimerInterrupt => 7
  | RV32MachineExternalInterrupt => 11
  end.

Definition rv32_trap_is_interrupt (cause : rv32_trap_cause) : bool :=
  match cause with
  | RV32MachineSoftwareInterrupt
  | RV32MachineTimerInterrupt
  | RV32MachineExternalInterrupt => true
  | RV32InstructionAddressMisaligned
  | RV32IllegalInstruction
  | RV32LoadAddressMisaligned
  | RV32StoreAddressMisaligned
  | RV32LoadAccessFault
  | RV32StoreAccessFault
  | RV32EnvironmentCall => false
  end.

Definition rv32_trap_mcause_value (cause : rv32_trap_cause) : N :=
  rv32_trap_cause_code cause +
    if rv32_trap_is_interrupt cause then 2147483648 else 0.

Definition rv32_privileged_initial_state
    (memory : rv32_memory)
    (trap_vector : rv32_pc) : rv32_privileged_state :=
  {| rv32_privileged_system :=
       rv32_system_initial_state memory;
     rv32_privileged_csrs :=
       {| rv32_mtvec := trap_vector;
          rv32_mepc := rv32_pc_zero;
          rv32_mcause := rv32_word_zero;
          rv32_mtval := rv32_word_zero |} |}.

Definition rv32_privileged_trap_entry
    (state : rv32_privileged_state)
    (event : rv32_trap_event) : rv32_privileged_state :=
  let system := rv32_privileged_system state in
  let machine := rv32_core_state (rv32_system_core system) in
  let csrs := rv32_privileged_csrs state in
  {| rv32_privileged_system :=
       rv32_trap_entry (rv32_mtvec csrs) system event;
     rv32_privileged_csrs :=
       {| rv32_mtvec := rv32_mtvec csrs;
          rv32_mepc := rv321_pc machine;
          rv32_mcause :=
            rv32_word_wrap
              (rv32_trap_mcause_value (rv32_event_cause event));
          rv32_mtval := rv32_event_value event |} |}.

Definition rv32_privileged_mret
    (state : rv32_privileged_state) : option rv32_privileged_state :=
  match rv32_system_trap_stack (rv32_privileged_system state) with
  | [] => None
  | _ :: frames =>
      let system := rv32_privileged_system state in
      let core := rv32_system_core system in
      let machine := rv32_core_state core in
      let csrs := rv32_privileged_csrs state in
      Some
        {| rv32_privileged_system :=
             {| rv32_system_core :=
                  rv32_state_with core (rv32_mepc csrs)
                    (rv321_registers machine) MachineRunning
                    (rv32_data_memory core);
                rv32_system_trap_stack := frames |};
           rv32_privileged_csrs := csrs |}
  end.

Definition rv32_privileged_step_result
    (program : rv32_program)
    (state : rv32_privileged_state) : option rv32_privileged_state :=
  let system := rv32_privileged_system state in
  let core := rv32_system_core system in
  match rv321_status (rv32_core_state core) with
  | MachineRunning =>
      match rv32_program_fetch program core with
      | None => None
      | Some encoding =>
          if encoding =? rv32_machine_return_encoding then
            match rv32_privileged_mret state with
            | Some returned => Some returned
            | None =>
                Some
                  (rv32_privileged_trap_entry state
                    {| rv32_event_cause := RV32IllegalInstruction;
                       rv32_event_value := rv32_word_wrap encoding |})
            end
          else
            match rv32_detect_exception encoding core with
            | Some event =>
                Some (rv32_privileged_trap_entry state event)
            | None =>
                Some
                  {| rv32_privileged_system :=
                       {| rv32_system_core :=
                            rv32_step_encoded encoding core;
                          rv32_system_trap_stack :=
                            rv32_system_trap_stack system |};
                     rv32_privileged_csrs :=
                       rv32_privileged_csrs state |}
            end
      end
  | MachineHalted | MachineTrapped => None
  end.

Definition rv32_privileged_step
    (program : rv32_program)
    (before after : rv32_privileged_state) : Prop :=
  rv32_privileged_step_result program before = Some after.

Fixpoint rv32_privileged_execute_n
    (program : rv32_program)
    (fuel : nat)
    (state : rv32_privileged_state) : rv32_privileged_state :=
  match fuel with
  | O => state
  | S remaining =>
      match rv32_privileged_step_result program state with
      | Some next => rv32_privileged_execute_n program remaining next
      | None => state
      end
  end.

Inductive rv32_privileged_steps_n
    (program : rv32_program) :
    nat -> rv32_privileged_state -> rv32_privileged_state -> Prop :=
| RV32PrivilegedStepsZero :
    forall state,
      rv32_privileged_steps_n program 0 state state
| RV32PrivilegedStepsNext :
    forall count first middle last,
      rv32_privileged_step program first middle ->
      rv32_privileged_steps_n program count middle last ->
      rv32_privileged_steps_n program (S count) first last.

Definition rv32_privileged_invariant
    (state : rv32_privileged_state) : Prop :=
  rv32_system_invariant (rv32_privileged_system state).

Definition rv32_run_application_with_csrs
    (image : rv32_binary_image)
    (trap_vector : rv32_pc)
    (fuel : nat) : rv32_privileged_state :=
  rv32_privileged_execute_n
    (rv32_load_binary_text image) fuel
    (rv32_privileged_initial_state
      (rv32_binary_data_words image) trap_vector).

Theorem rv32_csr_write_mtvec_accepts_aligned_value :
  forall csrs value,
    rv32_pc_aligned value ->
    exists updated,
      rv32_csr_write csrs rv32_csr_mtvec value = Some updated.
Proof.
  intros csrs value Haligned.
  unfold rv32_csr_write, rv32_csr_mtvec.
  assert (N.eqb 773 773 = true) as Haddress.
  { apply N.eqb_eq. reflexivity. }
  rewrite Haddress.
  unfold rv32_pc_from_word.
  destruct (N.eq_dec
    (N.modulo (rv32_word_value value) rv32_instruction_alignment) 0)
    as [Hvalid|Hinvalid].
  - eexists.
    reflexivity.
  - contradiction.
Qed.

Theorem rv32_csr_write_mepc_accepts_aligned_value :
  forall csrs value,
    rv32_pc_aligned value ->
    exists updated,
      rv32_csr_write csrs rv32_csr_mepc value = Some updated.
Proof.
  intros csrs value Haligned.
  unfold rv32_csr_write, rv32_csr_mepc.
  cbn [rv32_csr_mtvec].
  unfold rv32_pc_from_word.
  destruct (N.eq_dec
    (N.modulo (rv32_word_value value) rv32_instruction_alignment) 0)
    as [Hvalid|Hinvalid].
  - eexists.
    reflexivity.
  - contradiction.
Qed.

Theorem rv32_csr_write_mtvec_rejects_misaligned_value :
  forall csrs value,
    rv32_pc_from_word value = None ->
    rv32_csr_write csrs rv32_csr_mtvec value = None.
Proof.
  intros csrs value Hmisaligned.
  unfold rv32_csr_write, rv32_csr_mtvec.
  assert (N.eqb 773 773 = true) as Haddress.
  { apply N.eqb_eq. reflexivity. }
  rewrite Haddress, Hmisaligned.
  reflexivity.
Qed.

Theorem rv32_csr_write_mepc_rejects_misaligned_value :
  forall csrs value,
    rv32_pc_from_word value = None ->
    rv32_csr_write csrs rv32_csr_mepc value = None.
Proof.
  intros csrs value Hmisaligned.
  unfold rv32_csr_write, rv32_csr_mepc.
  cbn [rv32_csr_mtvec].
  rewrite Hmisaligned.
  reflexivity.
Qed.

Theorem rv32_csr_write_mcause_sets_value :
  forall csrs value,
    exists updated,
      rv32_csr_write csrs rv32_csr_mcause value = Some updated /\
      rv32_mcause updated = value.
Proof.
  intros csrs value.
  unfold rv32_csr_write, rv32_csr_mcause.
  cbn [rv32_csr_mtvec rv32_csr_mepc].
  eexists.
  split; reflexivity.
Qed.

Theorem rv32_csr_write_mtval_sets_value :
  forall csrs value,
    exists updated,
      rv32_csr_write csrs rv32_csr_mtval value = Some updated /\
      rv32_mtval updated = value.
Proof.
  intros csrs value.
  unfold rv32_csr_write, rv32_csr_mtval.
  cbn [rv32_csr_mtvec rv32_csr_mepc rv32_csr_mcause].
  eexists.
  split; reflexivity.
Qed.

Theorem rv32_machine_csr_pc_fields_are_aligned :
  forall csrs,
    rv32_pc_aligned (rv32_pc_word (rv32_mtvec csrs)) /\
    rv32_pc_aligned (rv32_pc_word (rv32_mepc csrs)).
Proof.
  intros csrs.
  split; apply rv32_pc_alignment_holds.
Qed.

Theorem rv32_privileged_trap_entry_uses_mtvec :
  forall state event,
    rv321_pc
      (rv32_core_state
        (rv32_system_core
          (rv32_privileged_system
            (rv32_privileged_trap_entry state event)))) =
      rv32_mtvec (rv32_privileged_csrs state).
Proof.
  reflexivity.
Qed.

Theorem rv32_privileged_trap_entry_saves_mepc :
  forall state event,
    rv32_mepc (rv32_privileged_csrs
      (rv32_privileged_trap_entry state event)) =
    rv321_pc (rv32_core_state
      (rv32_system_core (rv32_privileged_system state))).
Proof.
  reflexivity.
Qed.

Theorem rv32_privileged_trap_entry_sets_mcause :
  forall state event,
    rv32_word_value
      (rv32_mcause (rv32_privileged_csrs
        (rv32_privileged_trap_entry state event))) =
    rv32_trap_mcause_value (rv32_event_cause event).
Proof.
  intros.
  unfold rv32_privileged_trap_entry.
  simpl.
  apply rv32_word_wrap_small.
  destruct (rv32_event_cause event);
    cbv [rv32_trap_mcause_value rv32_trap_cause_code
      rv32_trap_is_interrupt rv32_modulus];
    lia.
Qed.

Theorem rv32_privileged_mret_without_frame_is_undefined :
  forall state,
    rv32_system_trap_stack (rv32_privileged_system state) = [] ->
    rv32_privileged_mret state = None.
Proof.
  intros [system csrs] Hframes.
  unfold rv32_privileged_mret.
  simpl in Hframes |- *.
  rewrite Hframes.
  reflexivity.
Qed.

Theorem rv32_privileged_mret_preserves_safety :
  forall state next,
    rv32_privileged_mret state = Some next ->
    rv32_privileged_invariant state ->
    rv32_privileged_invariant next.
Proof.
  intros [[core frames] csrs] next Hmret Hsafe.
  unfold rv32_privileged_mret in Hmret.
  simpl in Hmret.
  destruct frames as [|frame frames]; simpl in Hmret.
  - 
    discriminate.
  -
    inversion Hmret; subst next.
    unfold rv32_privileged_invariant, rv32_system_invariant,
      rv32_execution_invariant in *.
    destruct Hsafe as [_ [Hx0 Hmemory]].
    simpl.
    split.
    + apply rv32_pc_alignment_holds.
    + split.
      * apply rv32_x0_reads_zero with
          (registers := rv321_registers
            (rv32_core_state core)).
      * exact Hmemory.
Qed.

Theorem rv32_privileged_mret_decreases_trap_depth :
  forall state next,
    rv32_privileged_mret state = Some next ->
    S (length
      (rv32_system_trap_stack
        (rv32_privileged_system next))) =
    length
      (rv32_system_trap_stack
        (rv32_privileged_system state)).
Proof.
  intros [[core frames] csrs] next Hmret.
  unfold rv32_privileged_mret in Hmret.
  simpl in Hmret.
  destruct frames as [|frame frames]; simpl in Hmret.
  - discriminate.
  - inversion Hmret; subst next.
    simpl.
    reflexivity.
Qed.

Theorem rv32_privileged_step_deterministic :
  forall program before after1 after2,
    rv32_privileged_step program before after1 ->
    rv32_privileged_step program before after2 ->
    after1 = after2.
Proof.
  intros program before after1 after2 H1 H2.
  unfold rv32_privileged_step in *.
  congruence.
Qed.

Theorem rv32_privileged_step_preserves_safety :
  forall program before after,
    rv32_privileged_step program before after ->
    rv32_privileged_invariant before ->
    rv32_privileged_invariant after.
Proof.
  intros program before after Hstep Hsafe.
  unfold rv32_privileged_step in Hstep.
  unfold rv32_privileged_step_result in Hstep.
  destruct
    (rv321_status
      (rv32_core_state
        (rv32_system_core (rv32_privileged_system before))));
    try discriminate.
  destruct
    (rv32_program_fetch program
      (rv32_system_core (rv32_privileged_system before)))
    as [encoding|] eqn:Hfetch; try discriminate.
  destruct (encoding =? rv32_machine_return_encoding) eqn:Hreturn.
  - destruct (rv32_privileged_mret before) as [returned|] eqn:Hmret.
    + inversion Hstep; subst after.
      unfold rv32_privileged_mret in Hmret.
      destruct
        (rv32_system_trap_stack (rv32_privileged_system before))
        as [|frame frames] eqn:Hframes; simpl in Hmret.
      * discriminate.
      * inversion Hmret; subst returned.
        unfold rv32_privileged_invariant, rv32_system_invariant,
          rv32_execution_invariant in *.
        destruct Hsafe as [Hpc [Hx0 Hmemory]].
        split.
        -- apply rv32_pc_alignment_holds.
        -- split.
           ++ apply rv32_x0_reads_zero with
                (registers := rv321_registers
                  (rv32_core_state
                    (rv32_system_core (rv32_privileged_system before)))).
           ++ exact Hmemory.
    + inversion Hstep; subst after.
      unfold rv32_privileged_invariant.
      apply rv32_trap_entry_preserves_safety.
      exact Hsafe.
  - destruct (rv32_detect_exception encoding
      (rv32_system_core (rv32_privileged_system before)))
      as [event|] eqn:Hevent.
    + inversion Hstep; subst after.
      unfold rv32_privileged_invariant.
      apply rv32_trap_entry_preserves_safety.
      exact Hsafe.
    + inversion Hstep; subst after.
      unfold rv32_privileged_invariant, rv32_system_invariant,
        rv32_execution_invariant in *.
      destruct Hsafe as [Hpc [Hx0 Hmemory]].
      split.
      * apply rv32_step_encoded_preserves_pc_alignment.
      * split.
        -- apply rv32_step_encoded_preserves_x0.
        -- apply rv32_every_memory_is_well_formed.
Qed.

Theorem rv32_privileged_execute_n_preserves_safety :
  forall program fuel state,
    rv32_privileged_invariant state ->
    rv32_privileged_invariant
      (rv32_privileged_execute_n program fuel state).
Proof.
  intros program fuel.
  induction fuel as [|fuel IH]; intros state Hsafe.
  - exact Hsafe.
  - simpl.
    destruct (rv32_privileged_step_result program state)
      as [next|] eqn:Hstep.
    + apply IH.
      eapply rv32_privileged_step_preserves_safety; eassumption.
    + exact Hsafe.
Qed.

Theorem rv32_privileged_steps_n_deterministic :
  forall program count initial final1 final2,
    rv32_privileged_steps_n program count initial final1 ->
    rv32_privileged_steps_n program count initial final2 ->
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
      eapply rv32_privileged_step_deterministic; eassumption.
    }
    subst middle0.
    eapply IHHtrace1.
    exact H2.
Qed.

Theorem rv32_privileged_execute_n_has_bounded_trace :
  forall program fuel state,
    exists executed,
      (executed <= fuel)%nat /\
      rv32_privileged_steps_n program executed state
        (rv32_privileged_execute_n program fuel state).
Proof.
  intros program fuel.
  induction fuel as [|fuel IH]; intros state.
  - exists 0%nat.
    split; [lia|].
    simpl.
    constructor.
  - simpl.
    destruct (rv32_privileged_step_result program state)
      as [next|] eqn:Hstep.
    + destruct (IH next) as [executed [Hbound Htrace]].
      exists (S executed).
      split; [lia|].
      econstructor; eassumption.
    + exists 0%nat.
      split; [lia|].
      constructor.
Qed.

Theorem rv32_run_application_with_csrs_is_safe :
  forall image trap_vector fuel,
    rv32_privileged_invariant
      (rv32_run_application_with_csrs image trap_vector fuel).
Proof.
  intros image trap_vector fuel.
  unfold rv32_run_application_with_csrs.
  apply rv32_privileged_execute_n_preserves_safety.
  unfold rv32_privileged_invariant, rv32_system_invariant.
  apply rv32_initial_execution_state_satisfies_invariant.
  apply rv32_every_memory_is_well_formed.
Qed.

Theorem rv32_run_application_with_csrs_has_bounded_trace :
  forall image trap_vector fuel,
    exists executed,
      (executed <= fuel)%nat /\
      rv32_privileged_steps_n
        (rv32_load_binary_text image) executed
        (rv32_privileged_initial_state
          (rv32_binary_data_words image) trap_vector)
        (rv32_run_application_with_csrs image trap_vector fuel).
Proof.
  intros image trap_vector fuel.
  unfold rv32_run_application_with_csrs.
  apply rv32_privileged_execute_n_has_bounded_trace.
Qed.
