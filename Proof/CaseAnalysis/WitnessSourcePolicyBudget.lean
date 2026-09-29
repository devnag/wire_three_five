import Proof.CaseAnalysis.WitnessNativeCacheBudget

/-! The real metadata and coefficient policy costs allow a fixed envelope
over their short input fields. The finite maximum is only a runtime bound. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy
open PaddedRunnerBudgetClosure BudgetTools RepairSource ProjectionNormalization CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def cost (D copies : ℕ) (delta : ℚ) (p : LegalBudget.Parameters):=
  budget D copies p.1 p.2.1 p.2.2.2 p.2.2.1 delta
def envelope (D copies : ℕ) (delta : ℚ) (S : ℕ):=(LegalBudget.box S).sup (cost D copies delta)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy
