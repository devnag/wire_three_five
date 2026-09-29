import Proof.CaseAnalysis.FinalStageContracts
import Proof.CaseAnalysis.FinalSupplierStage

namespace NearCubicWires.RepairSource.CloseoutFinal.C10StageSeamBridge

open LocalBitMultitape ExtDecompositionBatch ComponentwisePolynomial
open RepairOrdinary RepairOrdinary.CloseoutWitness RepairRepresentation SourceInterfaces
open SupplierPipeline
open CompetitorRationalGap CloseoutRowsOriginalSchedule
open RepairOrdinary.CloseoutFinalC10WorkerChain RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10WorkerDockSeam RepairOrdinary.CloseoutFinalC10WorkerFold
open RepairOrdinary.CloseoutFinalC10WorkerEmitLoader RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open RepairOrdinary.CloseoutFinalC10StageSeam
open C10LengthGate C10TailCompose C10BodyWidths C10TailComposeUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The two retained width words, on one physical pair of tapes -/

-- `StageData`'s own guard: `Proof/CaseAnalysis/FinalStageContracts.lean` makes the two
-- PCPP abbreviations opaque while the carrier structure is elaborated, and restores them
-- at `:77`.  `Parts` carries the same fields, so it needs the same guard.
attribute [local irreducible] pcppOf Atoms

attribute [local semireducible] pcppOf Atoms

/-! ## Section 3  The seam -/

end
end NearCubicWires.RepairSource.CloseoutFinal.C10StageSeamBridge
