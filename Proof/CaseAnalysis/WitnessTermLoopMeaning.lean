import Proof.CaseAnalysis.WitnessTermLoopData
import Proof.CaseAnalysis.WitnessTermRoundAll

/-! The one physical loop result is exactly the conjunction of its
original term decisions. Successful exhaustion carries the exact final
mass and both logical retained-record cursors for the sum consumer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem iterate_flag {α : Type} (next : ℕ → α → Bool×α) (flag : ℕ → Bool)
    (hflag : ∀ j x,(next j x).1=flag j) (n pos : ℕ) (x : α) :
    (RepeatMachine.iterate (CountedReject.advance next) n (pos,x)).1=(List.range' pos n).all flag := by
  induction n generalizing pos x with
  | zero => rfl
  | succ n ih =>
    cases hp : flag pos <;>
      simp only [RepeatMachine.iterate,CountedReject.advance,hflag,hp,Bool.false_eq_true,↓reduceIte,
        List.range'_succ,List.all_cons,Bool.false_and,Bool.true_and,ih]

theorem range_all (words : List (List Bool)) (flag : List Bool → Bool) :
    (List.range' 0 words.length).all (fun j=>flag (words.getD j []))=words.all flag := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,List.mem_range',Nat.one_mul,Nat.zero_add]
  constructor
  · intro h bits hb
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hb
    subst bits
    simpa only [List.getD_eq_getElem words [] hi] using h i ⟨i,hi,rfl⟩
  · intro h j hj
    obtain ⟨i,hi,rfl⟩ := hj
    rw [List.getD_eq_getElem words [] hi]
    exact h _ (List.getElem_mem hi)

def passed (C : ℕ) (words : List (List Bool)) (circuitPass : List Bool → Bool) :=
  words.all (fun bits=>TermRoundAll.accepted C bits (circuitPass bits))

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermLoop
