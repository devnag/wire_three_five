import Proof.CaseAnalysis.FinalStageSeamBlock
import Proof.CaseAnalysis.FinalWordsStage

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (DockReady joinScalarWidth flag
  result inputTape)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape (EmitEntry)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold (foldWidth)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other
  install_existing)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The words stage's tapes sit at the bottom of the stage bank -/

/-! ## §3 The stage, its fuel, and its state count -/

/-! ## §4 The run -/

/-! ## §5 The block, from the prologue obligation alone -/


-- scan (L.md §7.6) is only safe when no `does not depend on any axioms` line is
-- followed by a `depends on axioms` line.

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage
