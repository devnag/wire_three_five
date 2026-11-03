import Proof.Rows.NativeCircuitCount

/-! Parse the actual native circuit count, skip its TOP frame, and return a
cold parser bank with the physical padded count ready for the bottom loop. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeCircuitPrepare
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_NativeCircuitCount
noncomputable section

def budget (n U t : Nat) :=2*PCPPQueryNatural.budget n+6*U+2*natBitLength n+2*t+21

end
end PCJ45bee56da9f34d5a_NativeCircuitPrepare
