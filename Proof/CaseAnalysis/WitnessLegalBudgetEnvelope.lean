import Proof.CaseAnalysis.WitnessBudgetFast

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
def cost (e den copies : ℕ) (delta : ℚ) (sym : Bool) (p : Parameters) :=
  LegalTemplate.budget e den delta copies sym p.1 p.2.1 p.2.2.1 p.2.2.2
def envelope (e den copies : ℕ) (delta : ℚ) (sym : Bool) (S : ℕ) :=
  (box S).sup (cost e den copies delta sym)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalBudget
