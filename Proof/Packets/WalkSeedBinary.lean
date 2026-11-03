import Proof.Packets.ToeplitzSeedBits
import Proof.MachineModel.OrdinaryBoundedCounter

/-! Exact little-endian words of the frozen Toeplitz encoding. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedBinary
open NearCubicWires NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open Completion.ToeplitzSeedBits

def vertexWord (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :=
  binary (toeplitzWalkSideBits rank) v.2.val++binary (toeplitzWalkSideBits rank) v.1.val

theorem vertexWord_length (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    (vertexWord rank v).length=2*toeplitzWalkSideBits rank := by
  simp only [vertexWord,List.length_append,binary_length]
  omega

end Theorem25Completion.WalkSeedBinary
