(* Trap entry, handler return, and exception-aware execution for RV32I. *)

From Stdlib Require Import List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia.
From MicroVeriVM Require Import RiscV.Word.
From MicroVeriVM Require Import RiscV.RegisterFile.
From MicroVeriVM Require Import RiscV.Machine.
From MicroVeriVM Require Import RiscV.Instruction.
From MicroVeriVM Require Import RiscV.Decoder.
From MicroVeriVM Require Import RiscV.Semantics.
From MicroVeriVM Require Import RiscV.Execution.

Import ListNotations.
Open Scope N_scope.

Inductive rv32_trap_cause : Type :=
| RV32EnvironmentCall
| RV32IllegalInstruction
| RV32LoadAddressMisaligned
| RV32StoreAddressMisaligned
| RV32InstructionAddressMisaligned
| RV32LoadAccessFault
| RV32StoreAccessFault
| RV32MachineSoftwareInterrupt
| RV32MachineTimerInterrupt
| RV32MachineExternalInterrupt.

Record rv32_trap_event : Type := {
  rv32_event_cause : rv32_trap_cause;
  rv32_event_value : rv32_word
}.

Record rv32_trap_frame : Type := {
  rv32_frame_pc : rv32_pc;
  rv32_frame_cause : rv32_trap_cause;
  rv32_frame_value : rv32_word
}.

Record rv32_system_state : Type := {
  rv32_system_core : rv32_execution_state;
  rv32_system_trap_stack : list rv32_trap_frame
}.

Definition rv32_environment_call_encoding : N := 115.
Definition rv32_machine_return_encoding : N := 807403635.

Definition rv32_system_initial_state
    (memory : rv32_memory) : rv32_system_state :=
  {| rv32_system_core := rv32_initial_execution_state memory;
     rv32_system_trap_stack := [] |}.

Definition rv32_address_event
    (memory : rv32_memory)
    (address : rv32_word)
    (misaligned_cause access_cause : rv32_trap_cause) :
    option rv32_trap_event :=
  if N.eqb (N.modulo (rv32_word_value address) 4) 0 then
    match rv32_memory_load memory address with
    | Some _ => None
    | None => Some {| rv32_event_cause := access_cause;
                      rv32_event_value := address |}
    end
  else
    Some {| rv32_event_cause := misaligned_cause;
            rv32_event_value := address |}.

Definition rv32_control_target_event
    (target : rv32_word) : option rv32_trap_event :=
  match rv32_pc_from_word target with
  | Some _ => None
  | None =>
      Some {| rv32_event_cause := RV32InstructionAddressMisaligned;
              rv32_event_value := target |}
  end.

Definition rv32_instruction_trap_event
    (instruction : rv32_instruction)
    (state : rv32_execution_state) : option rv32_trap_event :=
  let core := rv32_core_state state in
  let registers := rv321_registers core in
  let pc := rv321_pc core in
  let memory := rv32_data_memory state in
  match instruction with
  | RV32_LW _ rs1 immediate =>
      rv32_address_event memory
        (rv32_effective_address (rv32_read_register registers rs1) immediate)
        RV32LoadAddressMisaligned RV32LoadAccessFault
  | RV32_SW rs1 _ immediate =>
      rv32_address_event memory
        (rv32_effective_address (rv32_read_register registers rs1) immediate)
        RV32StoreAddressMisaligned RV32StoreAccessFault
  | RV32_BEQ rs1 rs2 immediate =>
      if rv32_word_value (rv32_read_register registers rs1) =?
         rv32_word_value (rv32_read_register registers rs2) then
        rv32_control_target_event
          (rv32_add (rv32_pc_word pc)
            (rv32_sign_extend_13 immediate))
      else None
  | RV32_JAL _ immediate =>
      rv32_control_target_event
        (rv32_add (rv32_pc_word pc)
          (rv32_sign_extend_21 immediate))
  | RV32_JALR _ rs1 immediate =>
      rv32_control_target_event
        (rv32_jalr_target
          (rv32_read_register registers rs1)
          (rv32_sign_extend_12 immediate))
  | RV32_ADD _ _ _ | RV32_SUB _ _ _ | RV32_ADDI _ _ _ | RV32_LUI _ _ =>
      None
  end.

Definition rv32_detect_exception
    (encoding : N)
    (state : rv32_execution_state) : option rv32_trap_event :=
  if encoding =? rv32_environment_call_encoding then
    Some {| rv32_event_cause := RV32EnvironmentCall;
            rv32_event_value := rv32_word_zero |}
  else
    match rv32_decode encoding with
    | RV32IllegalEncoding | RV32UnsupportedEncoding =>
        Some {| rv32_event_cause := RV32IllegalInstruction;
                rv32_event_value := rv32_word_wrap encoding |}
    | RV32Decoded instruction _ _ =>
        rv32_instruction_trap_event instruction state
    end.

Definition rv32_trap_entry
    (handler_pc : rv32_pc)
    (state : rv32_system_state)
    (event : rv32_trap_event) : rv32_system_state :=
  let core := rv32_system_core state in
  let machine := rv32_core_state core in
  {| rv32_system_core :=
       rv32_state_with core handler_pc
         (rv321_registers machine) MachineRunning
         (rv32_data_memory core);
     rv32_system_trap_stack :=
       {| rv32_frame_pc := rv321_pc machine;
          rv32_frame_cause := rv32_event_cause event;
          rv32_frame_value := rv32_event_value event |}
       :: rv32_system_trap_stack state |}.

Definition rv32_trap_return
    (state : rv32_system_state) : option rv32_system_state :=
  match rv32_system_trap_stack state with
  | [] => None
  | frame :: frames =>
      let core := rv32_system_core state in
      let machine := rv32_core_state core in
      Some
        {| rv32_system_core :=
             rv32_state_with core (rv32_frame_pc frame)
               (rv321_registers machine) MachineRunning
               (rv32_data_memory core);
           rv32_system_trap_stack := frames |}
  end.

Definition rv32_update_saved_pc
    (state : rv32_system_state)
    (new_pc : rv32_pc) : option rv32_system_state :=
  match rv32_system_trap_stack state with
  | [] => None
  | frame :: frames =>
      Some
        {| rv32_system_core := rv32_system_core state;
           rv32_system_trap_stack :=
             {| rv32_frame_pc := new_pc;
                rv32_frame_cause := rv32_frame_cause frame;
                rv32_frame_value := rv32_frame_value frame |} :: frames |}
  end.

Definition rv32_system_step_result
    (program : rv32_program)
    (handler_pc : rv32_pc)
    (state : rv32_system_state) : option rv32_system_state :=
  let core := rv32_system_core state in
  match rv321_status (rv32_core_state core) with
  | MachineRunning =>
      match rv32_program_fetch program core with
      | None => None
      | Some encoding =>
          if encoding =? rv32_machine_return_encoding then
            match rv32_trap_return state with
            | Some returned => Some returned
            | None =>
                Some
                  (rv32_trap_entry handler_pc state
                    {| rv32_event_cause := RV32IllegalInstruction;
                       rv32_event_value := rv32_word_wrap encoding |})
            end
          else
            match rv32_detect_exception encoding core with
            | Some event => Some (rv32_trap_entry handler_pc state event)
            | None =>
                Some
                  {| rv32_system_core :=
                       rv32_step_encoded encoding core;
                     rv32_system_trap_stack :=
                       rv32_system_trap_stack state |}
            end
      end
  | MachineHalted | MachineTrapped => None
  end.

Definition rv32_system_step
    (program : rv32_program)
    (handler_pc : rv32_pc)
    (before after : rv32_system_state) : Prop :=
  rv32_system_step_result program handler_pc before = Some after.

Fixpoint rv32_system_execute_n
    (program : rv32_program)
    (handler_pc : rv32_pc)
    (fuel : nat)
    (state : rv32_system_state) : rv32_system_state :=
  match fuel with
  | O => state
  | S remaining =>
      match rv32_system_step_result program handler_pc state with
      | Some next => rv32_system_execute_n program handler_pc remaining next
      | None => state
      end
  end.

Inductive rv32_system_steps_n
    (program : rv32_program)
    (handler_pc : rv32_pc) :
    nat -> rv32_system_state -> rv32_system_state -> Prop :=
| RV32SystemStepsZero :
    forall state,
      rv32_system_steps_n program handler_pc 0 state state
| RV32SystemStepsNext :
    forall count first middle last,
      rv32_system_step program handler_pc first middle ->
      rv32_system_steps_n program handler_pc count middle last ->
      rv32_system_steps_n program handler_pc (S count) first last.

Definition rv32_system_invariant (state : rv32_system_state) : Prop :=
  rv32_execution_invariant (rv32_system_core state).

Theorem rv32_environment_call_is_detected :
  forall state,
    rv32_detect_exception rv32_environment_call_encoding state =
    Some {| rv32_event_cause := RV32EnvironmentCall;
            rv32_event_value := rv32_word_zero |}.
Proof.
  intros state.
  unfold rv32_detect_exception, rv32_environment_call_encoding.
  vm_compute.
  reflexivity.
Qed.

Theorem rv32_illegal_decode_is_illegal_instruction_trap :
  forall encoding state,
    encoding <> rv32_environment_call_encoding ->
    (rv32_decode encoding = RV32IllegalEncoding \/
     rv32_decode encoding = RV32UnsupportedEncoding) ->
    rv32_detect_exception encoding state =
      Some {| rv32_event_cause := RV32IllegalInstruction;
              rv32_event_value := rv32_word_wrap encoding |}.
Proof.
  intros encoding state Hnot_ecall Hdecode.
  unfold rv32_detect_exception.
  assert (N.eqb encoding rv32_environment_call_encoding = false) as Htest.
  { apply N.eqb_neq. exact Hnot_ecall. }
  rewrite Htest.
  destruct (rv32_decode encoding); try contradiction.
  - destruct Hdecode as [Hdecode|Hdecode]; discriminate.
  - reflexivity.
  - reflexivity.
Qed.

Theorem rv32_misaligned_memory_address_is_classified :
  forall memory address misaligned_cause access_cause,
    N.modulo (rv32_word_value address) 4 <> 0 ->
    rv32_address_event memory address misaligned_cause access_cause =
      Some {| rv32_event_cause := misaligned_cause;
              rv32_event_value := address |}.
Proof.
  intros memory address misaligned_cause access_cause Hmisaligned.
  unfold rv32_address_event.
  assert (N.eqb (N.modulo (rv32_word_value address) 4) 0 = false)
    as Htest.
  { apply N.eqb_neq. exact Hmisaligned. }
  rewrite Htest.
  reflexivity.
Qed.

Theorem rv32_aligned_memory_access_failure_is_classified :
  forall memory address misaligned_cause access_cause,
    N.modulo (rv32_word_value address) 4 = 0 ->
    rv32_memory_load memory address = None ->
    rv32_address_event memory address misaligned_cause access_cause =
      Some {| rv32_event_cause := access_cause;
              rv32_event_value := address |}.
Proof.
  intros memory address misaligned_cause access_cause Haligned Hload.
  unfold rv32_address_event.
  assert (N.eqb (N.modulo (rv32_word_value address) 4) 0 = true)
    as Htest.
  { apply N.eqb_eq. exact Haligned. }
  rewrite Htest, Hload.
  reflexivity.
Qed.

Theorem rv32_misaligned_control_target_is_classified :
  forall target,
    rv32_pc_from_word target = None ->
    rv32_control_target_event target =
      Some {| rv32_event_cause := RV32InstructionAddressMisaligned;
              rv32_event_value := target |}.
Proof.
  intros target Htarget.
  unfold rv32_control_target_event.
  rewrite Htarget.
  reflexivity.
Qed.

Theorem rv32_system_step_result_routes_detected_exception :
  forall program handler state encoding event,
    rv321_status (rv32_core_state (rv32_system_core state)) =
      MachineRunning ->
    rv32_program_fetch program (rv32_system_core state) = Some encoding ->
    encoding <> rv32_machine_return_encoding ->
    rv32_detect_exception encoding (rv32_system_core state) = Some event ->
    rv32_system_step_result program handler state =
      Some (rv32_trap_entry handler state event).
Proof.
  intros program handler state encoding event Hrunning Hfetch
    Hnot_mret Hevent.
  unfold rv32_system_step_result.
  rewrite Hrunning, Hfetch.
  assert (N.eqb encoding rv32_machine_return_encoding = false) as Htest.
  { apply N.eqb_neq. exact Hnot_mret. }
  rewrite Htest, Hevent.
  reflexivity.
Qed.

Theorem rv32_environment_call_redirects_to_handler :
  forall program handler state,
    rv321_status (rv32_core_state (rv32_system_core state)) =
      MachineRunning ->
    rv32_program_fetch program (rv32_system_core state) =
      Some rv32_environment_call_encoding ->
    rv32_system_step_result program handler state =
      Some
        (rv32_trap_entry handler state
          {| rv32_event_cause := RV32EnvironmentCall;
             rv32_event_value := rv32_word_zero |}).
Proof.
  intros program handler state Hrunning Hfetch.
  eapply rv32_system_step_result_routes_detected_exception.
  - exact Hrunning.
  - exact Hfetch.
  - unfold rv32_machine_return_encoding, rv32_environment_call_encoding.
    discriminate.
  - apply rv32_environment_call_is_detected.
Qed.

Theorem rv32_system_step_deterministic :
  forall program handler_pc before after1 after2,
    rv32_system_step program handler_pc before after1 ->
    rv32_system_step program handler_pc before after2 ->
    after1 = after2.
Proof.
  intros program handler_pc before after1 after2 H1 H2.
  unfold rv32_system_step in *.
  congruence.
Qed.

Theorem rv32_mret_without_active_trap_is_illegal :
  forall program handler state,
    rv321_status (rv32_core_state (rv32_system_core state)) =
      MachineRunning ->
    rv32_program_fetch program (rv32_system_core state) =
      Some rv32_machine_return_encoding ->
    rv32_system_trap_stack state = [] ->
    exists event,
      rv32_system_step_result program handler state =
        Some (rv32_trap_entry handler state event) /\
      rv32_event_cause event = RV32IllegalInstruction.
Proof.
  intros program handler state Hrunning Hfetch Hframes.
  exists
    {| rv32_event_cause := RV32IllegalInstruction;
       rv32_event_value := rv32_word_wrap rv32_machine_return_encoding |}.
  unfold rv32_system_step_result.
  rewrite Hrunning, Hfetch.
  assert (N.eqb rv32_machine_return_encoding
    rv32_machine_return_encoding = true) as Hreturn.
  { apply N.eqb_eq. reflexivity. }
  rewrite Hreturn.
  split; [|reflexivity].
  unfold rv32_trap_return.
  rewrite Hframes.
  reflexivity.
Qed.

Theorem rv32_trap_return_without_frame_is_undefined :
  forall state,
    rv32_system_trap_stack state = [] ->
    rv32_trap_return state = None.
Proof.
  intros [core frames] Hframes.
  simpl in *.
  subst frames.
  reflexivity.
Qed.

Theorem rv32_trap_return_restores_saved_pc :
  forall core frame frames next,
    rv32_trap_return
      {| rv32_system_core := core;
         rv32_system_trap_stack := frame :: frames |} = Some next ->
    rv321_pc (rv32_core_state (rv32_system_core next)) =
      rv32_frame_pc frame.
Proof.
  intros core frame frames next Hreturn.
  simpl in Hreturn.
  inversion Hreturn.
  reflexivity.
Qed.

Theorem rv32_trap_entry_records_faulting_pc :
  forall handler state event,
    hd_error (rv32_system_trap_stack (rv32_trap_entry handler state event)) =
      Some
        {| rv32_frame_pc :=
             rv321_pc
               (rv32_core_state (rv32_system_core state));
           rv32_frame_cause := rv32_event_cause event;
           rv32_frame_value := rv32_event_value event |}.
Proof.
  reflexivity.
Qed.

Theorem rv32_trap_entry_redirects_to_handler :
  forall handler state event,
    rv321_pc
      (rv32_core_state (rv32_system_core
        (rv32_trap_entry handler state event))) = handler.
Proof.
  reflexivity.
Qed.

Theorem rv32_trap_entry_preserves_safety :
  forall handler state event,
    rv32_system_invariant state ->
    rv32_system_invariant (rv32_trap_entry handler state event).
Proof.
  intros handler [core frames] event [_ [_ Hmemory]].
  unfold rv32_system_invariant, rv32_execution_invariant.
  simpl.
  split.
  - apply rv32_pc_alignment_holds.
  - split.
    + apply rv32_x0_reads_zero with
        (registers := rv321_registers (rv32_core_state core)).
    + exact Hmemory.
Qed.

Theorem rv32_trap_return_preserves_safety :
  forall state next,
    rv32_trap_return state = Some next ->
    rv32_system_invariant state ->
    rv32_system_invariant next.
Proof.
  intros [core frames] next Hreturn Hsafe.
  destruct frames as [|frame frames]; simpl in Hreturn.
  - discriminate.
  - destruct Hsafe as [_ [_ Hmemory]].
    inversion Hreturn; subst next.
    unfold rv32_system_invariant, rv32_execution_invariant.
    simpl.
    split.
    + apply rv32_pc_alignment_holds.
    + split.
      * apply rv32_x0_reads_zero with
          (registers := rv321_registers (rv32_core_state core)).
      * exact Hmemory.
Qed.

Theorem rv32_system_step_preserves_safety :
  forall program handler state next,
    rv32_system_step program handler state next ->
    rv32_system_invariant state ->
    rv32_system_invariant next.
Proof.
  intros program handler state next Hstep Hsafe.
  unfold rv32_system_step in Hstep.
  unfold rv32_system_step_result in Hstep.
  destruct (rv321_status (rv32_core_state (rv32_system_core state)));
    try discriminate.
  destruct (rv32_program_fetch program (rv32_system_core state))
    as [encoding|] eqn:Hfetch; try discriminate.
  destruct (encoding =? rv32_machine_return_encoding) eqn:Hreturn.
  - destruct (rv32_trap_return state) as [returned|] eqn:Hret.
    + inversion Hstep; subst next.
      eapply rv32_trap_return_preserves_safety; eauto.
    + inversion Hstep; subst next.
      apply rv32_trap_entry_preserves_safety.
      exact Hsafe.
  - destruct (rv32_detect_exception encoding (rv32_system_core state))
      as [event|] eqn:Hevent.
    + inversion Hstep; subst next.
      apply rv32_trap_entry_preserves_safety.
      exact Hsafe.
    + inversion Hstep; subst next.
      unfold rv32_system_invariant, rv32_execution_invariant in *.
      destruct Hsafe as [Hpc [Hx0 Hmemory]].
      split.
      * apply rv32_step_encoded_preserves_pc_alignment.
      * split.
        -- apply rv32_step_encoded_preserves_x0.
        -- apply rv32_every_memory_is_well_formed.
Qed.

Theorem rv32_system_execute_n_preserves_safety :
  forall program handler fuel state,
    rv32_system_invariant state ->
    rv32_system_invariant
      (rv32_system_execute_n program handler fuel state).
Proof.
  intros program handler fuel.
  induction fuel as [|fuel IH]; intros state Hsafe.
  - exact Hsafe.
  - simpl.
    destruct (rv32_system_step_result program handler state)
      as [next|] eqn:Hstep.
    + apply IH.
      eapply rv32_system_step_preserves_safety.
      * exact Hstep.
      * exact Hsafe.
    + exact Hsafe.
Qed.

Theorem rv32_system_steps_n_preserves_safety :
  forall program handler count initial final,
    rv32_system_steps_n program handler count initial final ->
    rv32_system_invariant initial ->
    rv32_system_invariant final.
Proof.
  intros program handler count initial final Htrace.
  induction Htrace; intros Hsafe.
  - exact Hsafe.
  - apply IHHtrace.
    eapply rv32_system_step_preserves_safety; eassumption.
Qed.

Theorem rv32_system_steps_n_deterministic :
  forall program handler count initial final1 final2,
    rv32_system_steps_n program handler count initial final1 ->
    rv32_system_steps_n program handler count initial final2 ->
    final1 = final2.
Proof.
  intros program handler count initial final1 final2 Htrace1.
  revert final2.
  induction Htrace1; intros final2 Htrace2.
  - inversion Htrace2.
    reflexivity.
  - inversion Htrace2; subst.
    assert (middle = middle0) as Hmiddle.
    {
      eapply rv32_system_step_deterministic; eassumption.
    }
    subst middle0.
    eapply IHHtrace1.
    exact H2.
Qed.

Theorem rv32_system_execute_n_functional :
  forall program handler fuel state result1 result2,
    rv32_system_execute_n program handler fuel state = result1 ->
    rv32_system_execute_n program handler fuel state = result2 ->
    result1 = result2.
Proof.
  intros program handler fuel state result1 result2 H1 H2.
  congruence.
Qed.

Theorem rv32_system_execute_n_next :
  forall program handler fuel state next,
    rv32_system_step_result program handler state = Some next ->
    rv32_system_execute_n program handler (S fuel) state =
      rv32_system_execute_n program handler fuel next.
Proof.
  intros program handler fuel state next Hstep.
  simpl.
  rewrite Hstep.
  reflexivity.
Qed.

Theorem rv32_system_execute_n_has_exact_trace :
  forall program handler fuel state,
    exists executed,
      (executed <= fuel)%nat /\
      rv32_system_steps_n program handler executed state
        (rv32_system_execute_n program handler fuel state).
Proof.
  intros program handler fuel.
  induction fuel as [|fuel IH]; intros state.
  - exists 0%nat.
    split; [lia|].
    simpl.
    constructor.
  - simpl.
    destruct (rv32_system_step_result program handler state)
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

Theorem rv32_system_execute_n_is_a_trace :
  forall program handler fuel state,
    exists executed,
      (executed <= fuel)%nat /\
      rv32_system_steps_n program handler executed state
        (rv32_system_execute_n program handler fuel state).
Proof.
  apply rv32_system_execute_n_has_exact_trace.
Qed.
