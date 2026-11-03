import Proof.Rows.FinalPrimeResidueWord
import Proof.Rows.FinalPrimeModularSum
import Proof.Rows.FinalPrimeCoefficientReduce
import Proof.Hierarchy.HierarchyAllocation
import Proof.MachineModel.Layout

/-! Paid reduction and signed selection on the actual installed tape states.
The raw MSB-first magnitude, physical sign, prime, zero words, repeat
template and reset capacities are supplied at this local input boundary. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeSignedResidue
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairSource.VerifierDecoding RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


def budget (w Q : ℕ) := 2*FinalPrimeResidue.fuel w Q+12*w+21



end NearCubicWires.RepairSource.CloseoutFinal.C10NativeSignedResidue
