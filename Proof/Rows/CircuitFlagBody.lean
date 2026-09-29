import Proof.Rows.CircuitFlagLoad

/-! Consume the loaded circuit, then rewind and erase exactly its raw payload,
count, and isolated frame. The original outer source remains resident. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitFlagBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds PCJ45bee56da9f34d5a_CircuitFlagBank
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload flags)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_HeaderRewind.clear


end
end PCJ45bee56da9f34d5a_CircuitFlagBody
