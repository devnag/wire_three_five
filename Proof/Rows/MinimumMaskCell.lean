import Proof.Rows.CircuitCountCopy
import Proof.Rows.MinimumAssignment

/-! One actual minimizing-mask cell reads the native coefficient sign and skips
its magnitude with the paid native field parser. Source and input bits survive. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_MinimumMaskCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey RecoveryExecution Streaming StablePartition.Workspace
noncomputable section


def emit : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q bits => if q.val = 0 then some ⟨1,
    ![none,none,none,none,some (if bits 2 then bits 0 else bits 3)],
    ![.right,.stay,.right,.right,.right]⟩ else none

def slots : Fin 3 → Fin 5 := ![0,1,4]
def skip := RecoveryFocus.machine slots (PCPPQueryField.machine false)
def machine := Composition.machine emit skip

end
end PCJ45bee56da9f34d5a_MinimumMaskCell
