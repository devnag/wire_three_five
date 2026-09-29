import Proof.Rows.RowReady

/-! The paid Header scratch eraser used at the end of completion. All 430
mutable Header ports are swept in parallel. The eight metadata inputs, raw
source and packet driver are excluded; so are every Frame and other work port.
The current heads, true cap driver and zero log are explicit input obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ45bee56da9f34d5a_HeaderErase
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJd4d1d9d7d1fa4313_Production PCJ45bee56da9f34d5a_RowState
open PCJ9eff70d512234a4c_Fixed
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section





end
end PCJ45bee56da9f34d5a_HeaderErase
