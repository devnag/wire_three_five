import Proof.CaseAnalysis.WitnessFamilyResourcesLocal
import Proof.Circuits.PaddedRunnerBudgetClosure

/-! Coarse costs of the actual term, sum and outer-family loops, including
their already-checked loads, mask returns, clears and reinitialization. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def termCost (S P : ℕ) := 10000*(S+2)*(P+1)
def sumCost (S P : ℕ) := 1000*(S+2)*(termCost S P+P+1)
def totalCost (S P : ℕ) := 100*(S+2)*(sumCost S P+P+1)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
