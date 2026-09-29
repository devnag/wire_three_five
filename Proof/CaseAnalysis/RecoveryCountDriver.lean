import Proof.CaseAnalysis.RecoveryCountIncrement

/-! Reuse the same Compare(2^R) driver after the original row fold. One
paid move takes its returned head1 to the original scan's head2. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountDriver
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 116 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some
    ⟨1,fun _=>none,fun i=>if i=115 then .right else .stay⟩ else none

theorem run (H : Fin 116→ℕ) (A : Fin 116→List Bool) :
    ∃ r,runFrom machine 1 ⟨machine.start,H,A⟩=some r ∧ r.steps=1 ∧
      r.final.heads=Function.update H 115 (H 115+1) ∧ r.final.tapes=A := by
  have hs : step machine (⟨0,H,A⟩ : Configuration 116 2)=
      some ⟨1,Function.update H 115 (H 115+1),A⟩ := by
    change some (applyAction (⟨0,H,A⟩ : Configuration 116 2)
      ⟨1,fun _=>none,fun i=>if i=115 then .right else .stay⟩)=_
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=115
      · subst i;simp only [applyAction,↓reduceIte,HeadMove.apply,Function.update_self]
      · simp only [applyAction,if_neg hi,HeadMove.apply,Function.update_of_ne hi]
    · rfl
  obtain ⟨r,rr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,rr,rs,congrArg Configuration.heads rf,congrArg Configuration.tapes rf⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountDriver
