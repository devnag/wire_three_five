import Proof.CaseAnalysis.FinalWorkerEmitLoader

/-! # W2 -- the estimator body, closed to ONE loader

Paper C.10.1 (paper.tex 4130):

> In addition to validity, the machine estimates `mu = E_{i,u} F_i(u)` **by
> expanding it into AND-four supplier calls**, and accepts a branch only if
> `mu~ >= theta_acc := (c_p + s_p)/2`.

`RepairCloseoutFinalC10WorkerDockBody.body_runs` closes the body to TWO loader
hypotheses.  The second (`hemit`) is refuted as written
(`CloseoutFinalC10WorkerEmitShape.emit_over_arbitrary_exit_refuted`) and
discharged in its corrected form by an actual machine
(`CloseoutFinalC10WorkerEmitLoader.emit_loader_step`).  This module joins the
two: `body_runs_of_loader` produces `BodyRuns` -- hence `EstimatorBody` --
from ONE hypothesis, the prologue that turns P4's gate exit into the ready
bank.

`dock_exit` is `RepairCloseoutFinalC10WorkerDock.dock_step` with the two
projections the emit loader needs and which the existential of `dock_step`
hides: the exit heads are zero away from the fold's source tape `76` and its
unread driver tape `186`, and the twenty-nine answer slots `187 .. 215` come
through the docked multiply stage and the docked fold untouched.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitBody

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The dock's exit, with the two projections the emitter needs -/

/-! ## §2 The body, closed to one loader -/

/-! ## §3 The junction -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitBody
