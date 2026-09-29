import Proof.CaseAnalysis.FinalExactStagePackage
import Proof.CaseAnalysis.FinalExactRecordLoop
import Proof.CaseAnalysis.FinalRecordPadding
import Proof.CaseAnalysis.FinalClauseBitsUniform

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10StageJoin

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (CoefficientsFit siteCalls)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (joinScalarWidth)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters constantsOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## §1 The one width identity the join needs -/

/-! ## §2 `StageReady'` at the exact-fraction stage data, from `CallsReady` -/

/-! ## §3 `StageBlock'` at A.13.9's own fraction, open in `CallsReady` alone -/


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10StageJoin
