import Proof.Rows.TopArity
import Proof.PCP.PCPPQueryField

/-! Skip exactly four native headers and physically copy only the fifth field.
The original target is never decoded as unary. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CircuitCountCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open StablePartition.Workspace
noncomputable section


def source (tag q L target N : Nat) (tail : List Bool):=
  natWord tag++natWord q++natWord L++natWord target++natWord N++tail
def budget (tag q L target N : Nat):=
  2*(natBitLength tag+natBitLength q+natBitLength L+natBitLength target+natBitLength N)+19

end
end PCJ45bee56da9f34d5a_CircuitCountCopy
