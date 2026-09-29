import Proof.Rows.UniformGate

/-! Consume the same resident-master fanout/evaluator/erase program with a
single uniform reserve, so consecutive original gates share exactly one bank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_UniformGateCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.P1Closure
open PCJ45bee56da9f34d5a_CellGatePalette PCJ45bee56da9f34d5a_CellGate
noncomputable section
attribute [local irreducible] OffsetSourceGate.machine

end
end PCJ45bee56da9f34d5a_UniformGateCell
