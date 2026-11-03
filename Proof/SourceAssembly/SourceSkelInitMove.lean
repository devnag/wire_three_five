import Proof.MachineModel.Layout
import Proof.Amplification.RecoveryReadyCalls

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceSkeleton.InitMove

/-- SI's tape `v` ↦ S's tape. -/
def piV (b X NR v : Nat) : Nat :=
  if v < b then v
  else if v < b + 3 then v + NR + X
  else if v < b + 3 + X then v + NR - 3
  else if v < b + 3 + X + NR then v - 3 - X
  else v

section vals
variable (b X NR : Nat)

theorem piV_lt (T v : Nat) (hv : v < T) (hT : b + 3 + X + NR ≤ T) : piV b X NR v < T := by
  unfold piV; split_ifs <;> omega

end vals

variable (b X NR T : Nat) (hT : b + 3 + X + NR ≤ T)

/-- The slot map of the relocation (SI's tape ↦ S's tape). -/
def piF : Fin T → Fin T := fun x => ⟨piV b X NR x.val, piV_lt b X NR T x.val x.isLt hT⟩


end NearCubicWires.SourceSkeleton.InitMove
end
