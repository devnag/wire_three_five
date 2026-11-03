import Proof.Rows.NativeFamilyCount
import Proof.Rows.NativeFlagsMeaning

/-! Complete original native family traversal. Its loop driver is produced
from the fifth physical header; all size premises follow from the native byte cap. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeFamilyFlags
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_UniformMinimumBounds PCJ45bee56da9f34d5a_NativeFamilyCount
open PCJ45bee56da9f34d5a_NativeFlagsLoop (Circuit stream)
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload)
noncomputable section

def source {q : Nat} (tag L target : Nat) (cs : List (Circuit q)) :=
 PCJ45bee56da9f34d5a_CircuitCountCopy.source tag q L target cs.length (stream cs)
def budget (tag q L target N B : Nat):=
 PCJ45bee56da9f34d5a_CircuitCountAdvance.budget tag q L target N (U B q (B+1))+
 PCJ45bee56da9f34d5a_NativeFlagsLoop.budget N B q+3

end
end PCJ45bee56da9f34d5a_NativeFamilyFlags
