import Proof.CaseAnalysis.RowsLoopBoundary

/-! The literal Q driver executes only the required degree transitions.
Exhaustion includes its physical rewind; no body call at degree Q is
assumed. The growing cut pre is retained throughout the loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeLoop
open LocalBitMultitape RecoveryExecution CloseoutRowsLoopLayout CloseoutRowsLoopBoundary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine {t s : ℕ} (body : Machine t s) := RepeatMachine.machine body (fun _ _=>true)

theorem remaining {t s : ℕ} (body : Machine t s)
    (source : ℕ→List Bool→ Configuration t s) (emit : ℕ→List Bool) (cost Q : ℕ)
    (hstart : ∀ j<Q,∀ out,(source j out).control=body.start)
    (supplier : ∀ j<Q,∀ out,∃ r,runFrom body cost (source j out)=some r ∧
      r.final.heads=(source (j+1) (out++emit j)).heads ∧
      r.final.tapes=(source (j+1) (out++emit j)).tapes ∧ r.steps≤cost)
    (j n : ℕ) (out : List Bool) (hn : j+n=Q) :
    ∃ time≤n*(cost+2)+Q+3,Timed (machine body) time
      (RepeatMachine.cfg 0 (source j out) Q (j+1))
      (RepeatMachine.cfg 3 (source (j+n) (out++(List.range' j n).flatMap emit)) Q 1) := by
  induction n generalizing j out with
  | zero=>
    have hj : j=Q := by omega
    subst j
    refine ⟨Q+3,by simp,?_⟩
    simpa only [machine,Nat.add_zero,List.range'_zero,List.flatMap_nil,List.append_nil] using
      RepeatMachine.exhaust body (fun _ _=>true) (source Q out) Q
  | succ n ih=>
    have hj : j<Q := by omega
    obtain ⟨r,hr,rh,rt,rs⟩ := supplier j hj out
    have hstep := RepeatMachine.iteration body (fun _ _=>true) (source j out) Q j r
      (hstart j hj out) hj hr
    simp only [↓reduceIte] at hstep
    rw [RowOccurrenceLoop.cfg_eq 0 r.final (source (j+1) (out++emit j)) Q (j+2) rh rt] at hstep
    obtain ⟨time,htime,htail⟩ := ih (j+1) (out++emit j) (by omega)
    rw [show j+1+1=j+2 by omega] at htail
    have whole := hstep.trans htail
    refine ⟨r.steps+2+time,by nlinarith,?_⟩
    have he : j+1+n=j+(n+1) := by omega
    simpa only [machine,List.range'_succ,List.flatMap_cons,List.append_assoc,he] using whole

theorem loop_run {t s : ℕ} (body : Machine t s)
    (source : ℕ→List Bool→ Configuration t s) (emit : ℕ→List Bool) (cost Q : ℕ)
    (hstart : ∀ j<Q,∀ out,(source j out).control=body.start)
    (supplier : ∀ j<Q,∀ out,∃ r,runFrom body cost (source j out)=some r ∧
      r.final.heads=(source (j+1) (out++emit j)).heads ∧
      r.final.tapes=(source (j+1) (out++emit j)).tapes ∧ r.steps≤cost)
    (out : List Bool) :
    ∃ r,runFrom (machine body) (Q*(cost+3)+3) (RepeatMachine.cfg 0 (source 0 out) Q 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (source Q (out++(List.range Q).flatMap emit)) Q 1 ∧
      r.steps≤Q*(cost+3)+3 := by
  obtain ⟨time,hb,ht⟩ := remaining body source emit cost Q hstart supplier 0 Q out (by omega)
  simp only [Nat.zero_add,←List.range_eq_range'] at ht
  have hbound : time≤Q*(cost+3)+3 := by nlinarith
  obtain ⟨r,hr,hf,hs⟩ := ht.run
    (by simp [machine,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more := runFrom_moreFuel (machine body) time (Q*(cost+3)+3-time) _ r hr
  rw [Nat.add_sub_of_le hbound] at more
  exact ⟨r,more,hf,hs.le.trans hbound⟩


end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeLoop
