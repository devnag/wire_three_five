import Proof.CaseAnalysis.CloseoutRowsEstimatorWarmRetained
import Proof.CaseAnalysis.FinalSiteBodyUniform
import Proof.CaseAnalysis.RowsEstimatorPrepareWords

namespace NearCubicWires.RepairSource.CloseoutFinal.C10RoundEmitter

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 Two facts about the primitives, neither of which is new mathematics -/

/-! ## §2 The side condition `Emits` carries, and the refutation it implies -/

/-! ## §2a The length gate: `length_mono` does NOT refute `Emits` -/

/-! ## §3 The emptiness is not a phantom -/

/-! ## §4 The side condition, named, and the fact that discharges it -/

/-! ## §5 The k-free residual -/

section ClassicalNext
open scoped Classical

end ClassicalNext

/-! ## §6 The consumer, reached from the k-free obligation -/


end NearCubicWires.RepairSource.CloseoutFinal.C10RoundEmitter
