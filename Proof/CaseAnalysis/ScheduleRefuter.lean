import Proof.CaseAnalysis.ScheduleFramed

/-! The actual ordinary schedule feeds the same selected source refuter.
The existing compositor pays both word handoffs and resets. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Refuter
open RepairOrdinary SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem compose_bound (a d b e n N : Nat) (hN : N ≤ 2^n) :
    16*(a*(2^n+1)^d+b*(N+2)^e+1) ≤
      16*(a+b*2^e+1)*(2^n+1)^(d+e+1) := by
  let x : Nat := 2^n+1
  let P := x^(d+e+1)
  have hx : 1 ≤ x := Nat.succ_pos _
  have hP : 1 ≤ P := Nat.one_le_pow _ _ hx
  have hd : x^d ≤ P := Nat.pow_le_pow_right hx (by omega)
  have he : (N+2)^e ≤ 2^e*P := by
    calc
      _ ≤ (2*x)^e := Nat.pow_le_pow_left (by dsimp [x]; omega) _
      _ = 2^e*x^e := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (by omega))
  have ha := Nat.mul_le_mul_left a hd
  have hb := Nat.mul_le_mul_left b he
  change 16*(a*x^d+b*(N+2)^e+1) ≤ 16*(a+b*2^e+1)*P
  nlinarith

end
end NearCubicWires.RepairSource.CloseoutSchedule.Refuter
