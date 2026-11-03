import W3.Aliases
import Proof.CaseAnalysis.WitnessBudgetFast
import Proof.CaseAnalysis.WitnessDescriptionPolicy
import Proof.CaseAnalysis.WitnessFamilyCount
import Proof.CaseAnalysis.WitnessMass
import Proof.CaseAnalysis.WitnessModeDivide
import Proof.CaseAnalysis.WitnessTermPolicy
import W3.Proof.CaseAnalysis.Language
import W3.Proof.CaseAnalysis.ScheduleClauseWidth
import W3.Proof.CaseAnalysis.WitnessLegalTemplate

w3_alias_base

namespace W3


/-! One finite maximum of actual legal-policy costs is fixed before k.
Its maximizing short parameters satisfy the same polynomial bounds, so the
literal budget theorem proves this uniform envelope polynomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalBudget
open PaddedRunnerBudgetClosure BudgetTools
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev Parameters:=ℕ×ℕ×ℕ×ℕ
def box (S : ℕ) : Finset Parameters :=
  ((Finset.range (S+2)).product ((Finset.range (S+2)).product
    ((Finset.range (S+2)).product (Finset.range (S+2))))).filter (fun p=>2^p.2.2.1≤S+1)

theorem box_nonempty (S : ℕ) : (box S).Nonempty := by
  refine ⟨(0,0,0,0),?_⟩
  simp [box]

theorem box_bounds {S : ℕ} {p : Parameters} (hp:p∈box S) :
    p.1≤S+1 ∧ p.2.1≤S+1 ∧ p.2.2.1≤S+1 ∧ p.2.2.2≤S+1 ∧ 2^p.2.2.1≤S+1 := by
  simp only [box,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] at hp
  omega

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalBudget

end W3
