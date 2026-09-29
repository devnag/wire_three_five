import Proof.Rows.CircuitFlagBank

/-! Isolate and unwrap one actual circuit frame, preserving the advancing
outer source and using only the fixed local work reserve. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitFlagLoad
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds PCJ45bee56da9f34d5a_CircuitFlagBank
noncomputable section
attribute [local irreducible] PoolEntryCursor.copy
attribute [local irreducible] Streaming.machine


end
end PCJ45bee56da9f34d5a_CircuitFlagLoad
