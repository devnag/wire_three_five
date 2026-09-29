import Proof.CaseAnalysis.RecoveryRowPacketRefresh

/-! All original prototype printing, erasure and rewind fit in one linear
multiple of the already paid row backing. No sharper recovery estimate is used. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
open LocalBitMultitape RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_eq (C F R count Q clauses : ℕ) :
    budget C F R count Q clauses=24*C+8*F+4*R+4*count+4*Q+4*clauses+177 := by
  simp [budget,paddedBudget,fieldBudget,header,frame_length,CompareMachine.word]
  omega

theorem refresh_bound (C F R count Q clauses B : ℕ)
    (hC : C≤B) (hF : F≤B) (hR : R≤B) (hc : count≤B) (hQ : Q≤B) (hcl : clauses≤B) :
    refreshBudget C F R count Q clauses B≤512*(B+1) := by
  rw [refreshBudget,readyBudget,budget_eq]
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
