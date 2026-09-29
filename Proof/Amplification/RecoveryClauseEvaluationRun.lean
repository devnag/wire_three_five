import Proof.Amplification.RecoveryClauseEvaluationWhole

/-! Literal ordinary run receipt for the whole reusable clause checker.
The accepting endpoint is consumed directly by later certificate rows. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clause_run (s : State) (e : Extra) (word : List Bool) (hs : s.Valid) (he : e.Valid s word) :
    ∃ r,run machine (4194304*(s.bits.length+1)^2) (tapes s e)=some r ∧
      r.steps ≤ 4194304*(s.bits.length+1)^2 ∧ (∀ i,r.final.heads i=0) ∧
      r.final.tapes 27=[clauseWordCheck s e word] ∧
      (clauseWordCheck s e word=true → ∃ out : ClauseResult s e word,r.final.tapes=tapes out.state out.extra) := by
  obtain ⟨n,output,hn,hout,h,hreturn⟩ := clause_trace s e word hs he
  obtain ⟨r,hr,hf,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := run_moreFuel machine n (4194304*(s.bits.length+1)^2-n) (tapes s e) r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hsteps.trans_le hn,?_,?_,?_⟩
  · intro i; simp [hf,RecoveryCalls.stopped]
  · simpa [hf,RecoveryCalls.stopped] using hout
  · intro ht
    obtain ⟨out,heq⟩ := hreturn ht
    exact ⟨out,by simpa [hf,RecoveryCalls.stopped] using heq⟩

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
