import Proof.CaseAnalysis.RecoveryGraphBudgetResources

/-! The explicit support sum can be funded by one ordinary polynomial in
an already paid coarse W, after the caller proves actual source dominance. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
open RepairSource ProjectionNormalization PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem support_bound (W R Q bound : ℕ) (source : List Bool)
    (hR : R ≤ W) (hQ : Q ≤ W) (hb : bound ≤ W)
    (hs : source.length ≤ W) (htwo : 2^R ≤ W) :
    support W R Q bound source ≤ 10000000000*(W+1)^6 := by
  have hcap : RecoveryProjectionRows.capacity R ≤ 1048576*(W+1)^4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hR 1) 4)
  have hp := Nat.mul_le_mul hQ (Nat.add_le_add_right
    (Nat.mul_le_mul hR (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hcap) 11)) 8)
  simp only [←Nat.mul_assoc] at hp
  have hqr := Nat.mul_le_mul hQ hR
  have hstack := Nat.mul_le_mul_right (2*W+1) (show bound+W ≤ 2*W by omega)
  have hsave := Nat.mul_le_mul_right (2*W+1) (show bound+2^R+1 ≤ 2*W+1 by omega)
  have hupper : support W R Q bound source ≤
      16384*(W+1)^2+1+8388608*(W+1)^3+268435600*(W+1)^4+(W+7)+
      W*(6*(W+W+5)+3)+W+W*W+
      (W*(W*(4*1048576*(W+1)^4+11)+8)+5)+
      (2*W)*(2*W+1)+(2*W+1)*(2*W+1) := by
    unfold support RecoveryProjectionRowsRewind.batchBudget RecoveryBoundedSelectorLoop.capacity
    omega
  apply hupper.trans
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4),
    Nat.zero_le (W^5),Nat.zero_le (W^6)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
