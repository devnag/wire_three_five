import Proof.Amplification.RecoveryBoundedNativeUnaryMeaning

/-! Specialize the actual forward loop to the original compiler's
description-row unary-equality expression, with the same literal order. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryBoundedNative BoundedOracleStructuralCircuit OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstIndex {n bound : ℕ} (row : Fin (bound+1)) (start : ℕ) := row.val*rowWidth n bound+start
theorem index_bound {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) :
    firstIndex (n:=n) row start+limit ≤ descriptionWidth n bound := by
  have hr:=Nat.mul_le_mul_right (rowWidth n bound) (Nat.succ_le_iff.mpr row.isLt)
  unfold firstIndex descriptionWidth boundedCircuitDescriptionWidth
  dsimp only [rowWidth] at hr hblock
  nlinarith

theorem items_unary {n bound : ℕ} (row : Fin (bound+1)) (start limit value : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) :
    items (firstIndex (n:=n) row start) 0 value limit (index_bound row start limit hblock)=
      unaryItems row start limit value hblock := by
  rw [items_ofFn]
  unfold unaryItems
  congr 1
  funext i
  apply Prod.ext
  · apply Fin.ext
    simp [firstIndex,descriptionIndex,Nat.add_assoc]
  · simp [RecoveryBoundedNativeUnaryFlag.negative]

def initial {n bound : ℕ} (row : Fin (bound+1)) (start base : ℕ) (out stack : List Bool) : State :=
  ⟨firstIndex (n:=n) row start,base,0,false,out,stack⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryLoop
