import Proof.Rows.FramedGateBank

/-! Copy and load a real original gate while retaining the native stream cursor. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FramedGateLoad
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation
open PCJ45bee56da9f34d5a_FramedGateBank
noncomputable section
attribute [local irreducible] PoolEntryCursor.copy PCJ45bee56da9f34d5a_NativeGateLoadReady.machine


end
end PCJ45bee56da9f34d5a_FramedGateLoad
