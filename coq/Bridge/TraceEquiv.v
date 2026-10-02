(* Forward simulation of successful target traces into RustLite executions. *)

Set Warnings "-warn-library-file-stdlib-vector".

From MicroVeriVM Require Import RustModel.
From MicroVeriVM Require Import TargetAST.
From MicroVeriVM Require Import Bridge.RustLite.
From MicroVeriVM Require Import Bridge.Simulation.

Inductive lower_success_trace
    (program : list TargetInstruction) :
    RustState -> environment -> RustState -> environment -> Prop :=
| LowerTraceRefl : forall state env,
    st_rel state env ->
    lower_success_trace program state env state env
| LowerTraceStep : forall state env next next_env finish finish_env fuel,
    target_step program state = Success next ->
    exec fuel (lower_target_program_step program) env =
      ROk next_env CNormal ->
    st_rel next next_env ->
    lower_success_trace program next next_env finish finish_env ->
    lower_success_trace program state env finish finish_env.

Theorem run_sim_from_step_simulation :
  forall program start start_env finish,
    target_success_trace program start finish ->
    st_rel start start_env ->
    exists finish_env,
      lower_success_trace program start start_env finish finish_env.
Proof.
  intros program start start_env finish Htrace.
  revert start_env.
  induction Htrace as
    [state
    |state next finish Hstep Htail IH].
  - intros start_env Hrel.
    exists start_env.
    constructor.
    exact Hrel.
  - intros start_env Hrel.
    destruct (target_step_simulation program state start_env next Hrel Hstep)
      as [fuel [next_env [Hexec Hnext_rel]]].
    destruct (IH next_env Hnext_rel)
      as [finish_env Hlower_tail].
    exists finish_env.
    eapply LowerTraceStep; eauto.
Qed.
