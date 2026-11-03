import Proof.CaseAnalysis.RowsEstimatorReuseRun
import Proof.CaseAnalysis.RowsEstimatorNativeReadOnly

/-! The same enclosing reusable program preserves both externally owned
native tapes through the original estimator, masked reset, append and sweep. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RepairSource.RecoveryTseitinReadOnly
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem after_readonly (p : Program) (i : Fin (tapes p))
    (hi : i=native p ∨ i=capacity p) : NoWrite (after p) i := by
  apply composition
  · apply unselected
    intro j he
    have hv:=congrArg (fun k : Fin (tapes p)=>k.val) he
    have ht : 70≤WholePrefix.tapes p:=by unfold WholePrefix.tapes;omega
    have hr:=record_private p
    rcases hi with rfl|rfl <;> fin_cases j
    all_goals simp [copySlots,native,capacity,old,output,log,Retained.capacity] at hv
    all_goals omega
  · exact unselected (eraseSlots p) _ i
      (erase_avoids p i (hi.elim Or.inl (fun h=>Or.inr (Or.inl h))))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
