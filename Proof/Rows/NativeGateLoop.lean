import Proof.Rows.CountedGateCell

/-! Counted traversal of actual original native gate frames. Each iteration
consumes the checked reusable framed-gate/count cell, including zero arity. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeGateLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_FramedGateBank PCJ45bee56da9f34d5a_UniformMinimumBounds
noncomputable section

def word {q : Nat} (g : NormalizedThresholdGate q) := frame (PoolEntryLoad.word (strict g))
def stream {q : Nat} (gs : List (NormalizedThresholdGate q)) :=gs.flatMap word


end
end PCJ45bee56da9f34d5a_NativeGateLoop
