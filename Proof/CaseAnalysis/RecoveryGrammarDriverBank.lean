import Proof.CaseAnalysis.RecoveryGrammarFinishScan
import Proof.CaseAnalysis.RecoveryGrammarDriverReady

/-! Physically print the two finite-driver words from the retained raw
bound/candidate scalars, using the existing log. No scalar copy is introduced. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriverBank
open LocalBitMultitape RecoveryRootRound RecoveryExecution RecoveryBoundedGrammarCold
open RepairSource.ProjectionNormalization
open private install_eq from Proof.Amplification.RecoveryRowLookupCell
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ports (isBound : Bool) : Fin 3→Fin 114:=if isBound then ![102,112,78] else ![101,113,78]
def destination (isBound : Bool) : Fin 114:=if isBound then 112 else 113
noncomputable def emit (isBound : Bool):=RecoveryFocus.machine (ports isBound) (DimensionTemplate.machine true)

theorem injective (isBound : Bool) : Function.Injective (ports isBound) := by cases isBound <;> decide

theorem emit_run (isBound : Bool) (B n : ℕ) (H : Fin 114→ℕ) (A : Fin 114→List Bool)
    (hB : n+3≤B) (hin : ∀ j,A (ports isBound j)=CloseoutRecoveryGrammarDriverReady.input B n j)
    (hh : ∀ j,H (ports isBound j)=0) :
    ∃ r,runFrom (emit isBound) (2*n+8) ⟨(emit isBound).start,H,A⟩=some r ∧
      r.steps≤2*n+8 ∧ r.final.heads=H ∧
      r.final.tapes=Function.update A (destination isBound)
        (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (n+1))) := by
  obtain ⟨r,rr,rh,rt,rs⟩:=(CloseoutRecoveryGrammarDriverReady.ready B n hB).focus_at
    (ports isBound) (injective isBound) H A hin hh
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt]
  apply install_eq (ports isBound) (injective isBound)
  · intro j
    have hd : destination isBound=ports isBound 1:=by cases isBound <;> rfl
    rw [hd]
    by_cases hj : j=1
    · subst j
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne ((injective isBound).ne hj)]
      have same : CloseoutRecoveryGrammarDriverReady.output B n j=CloseoutRecoveryGrammarDriverReady.input B n j := by
        fin_cases j <;> simp_all [CloseoutRecoveryGrammarDriverReady.output,CloseoutRecoveryGrammarDriverReady.input]
      exact same.trans (hin j).symm
  · intro i hi
    have hd : destination isBound=ports isBound 1:=by cases isBound <;> rfl
    rw [hd]
    exact (Function.update_of_ne (Ne.symm (hi 1)) _ _).symm


end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriverBank
