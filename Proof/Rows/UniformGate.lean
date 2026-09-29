import Proof.Rows.FullGateRun

/-! The unchanged reusable gate evaluator accepts one uniform paid reserve R.
Only the run theorem is generalized; the same core, fanout and cleanup execute. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_UniformGate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.P1Closure
open OffsetSourceGate CloseoutRowsPoolWeight
open PCJ45bee56da9f34d5a_CellGatePalette
noncomputable section
attribute [local irreducible] OffsetSourceGate.machine

end
end PCJ45bee56da9f34d5a_UniformGate
