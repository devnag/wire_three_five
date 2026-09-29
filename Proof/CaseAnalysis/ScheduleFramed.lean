import Proof.CaseAnalysis.ScheduleOutput

/-! The cold canonical schedule returns an ordinary framed unary request.
Its original input is retained for the final requested language bit. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Framed
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def selectedLength (width : Nat → Nat) (n : Nat) :=
  if CloseoutLanguage.selectedIndex width n = 0 then 0 else 2^(CloseoutLanguage.selectedIndex width n)

theorem selectedLength_bound (width : Nat → Nat) (n : Nat) : selectedLength width n ≤ 2^n := by
  unfold selectedLength
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.pow_le_pow_right (by decide) (CloseoutLanguage.selectedIndex_le width n)


end
end NearCubicWires.RepairSource.CloseoutSchedule.Framed
