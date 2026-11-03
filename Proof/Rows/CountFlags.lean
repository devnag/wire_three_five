import Proof.Rows.NativeGateLoop
import Proof.Rows.FinalPrimeModularSum

/-! Count true flags in an actual counted prefix. The circuit's appended
true target flag remains outside that prefix. All increments are paid and
rewound on the same framed binary counter. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CountFlags
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution RadixSemantics SignedSortKey
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section


def budget (N w :Nat):=N*(4*w+11)+3

end
end PCJ45bee56da9f34d5a_CountFlags
