import Proof.Rows.FullGateBounds

/-! Consume the existing paid reusable gate on an arbitrary full assignment.
False backing is added only to retained source/mask masters after the run proof,
so it does not enlarge the logical evaluator capacity or create a size cycle. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FullGateRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open PCJ45bee56da9f34d5a_FullGateBounds PCJ45bee56da9f34d5a_CellGatePalette
open scoped BigOperators
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CellGate.machine


end
end PCJ45bee56da9f34d5a_FullGateRun
