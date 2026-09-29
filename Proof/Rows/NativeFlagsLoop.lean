import Proof.Rows.CircuitFlagCost

/-! The actual reusable circuit callback traverses the native framed circuit
list. Its invariant co-counts all produced gate and target flags. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeFlagsLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds PCJ45bee56da9f34d5a_CircuitFlagBank
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload flags)
noncomputable section

abbrev Circuit (q : Nat) :=List (NormalizedThresholdGate q)×List Bool
def word {q : Nat} (c : Circuit q) :=frame (payload c.1 c.2)
def stream {q : Nat} (cs : List (Circuit q)):=cs.flatMap word



end
end PCJ45bee56da9f34d5a_NativeFlagsLoop
