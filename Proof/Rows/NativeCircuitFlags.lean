import Proof.Rows.NativeCircuitCount

/-! Actual native circuit payload to its complete flag block: read the count,
skip TOP, evaluate every original bottom gate, then emit the true target flag.
The source bound includes the circuit's gate count, not merely one gate width. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeCircuitFlags
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_NativeCircuitCount PCJ45bee56da9f34d5a_UniformMinimumBounds
noncomputable section

def payload {q : Nat} (gs : List (NormalizedThresholdGate q)) (top : List Bool) :=
 natWord gs.length++frame top++PCJ45bee56da9f34d5a_NativeGateLoop.stream gs

def flags {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q) :=
 gs.map (fun g=>residualConstant g live x)++[true]

end
end PCJ45bee56da9f34d5a_NativeCircuitFlags
