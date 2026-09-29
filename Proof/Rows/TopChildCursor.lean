import Proof.Rows.Plan

/-! The actual topWord circuit payload has TWO native headers and unframed
children. This paid locator reads those headers and the preceding fixed-arity
children; it leaves the original source at the chosen child's first field. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_TopChildCursor
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def payload {n : Nat} (gs : List (ExactThresholdGate n)) :=natWord n++exactListWord gs

end
end PCJ45bee56da9f34d5a_TopChildCursor
