import Proof.CaseAnalysis.WitnessHierarchyBudget
import Proof.CaseAnalysis.CloseoutWitnessOracleBudget

/-! Uniform source and oracle-prefix accounting includes the inactive and
oversized-width branches. All hierarchy dependence is in a linear scale. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdOracle
open SourceInterfaces RepairSource ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open CloseoutSchedule LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def parserBound (N R : ℕ):=2*R+12*N+40+40000000000000000000000*(N+2)^25

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def sourceBound (cutoff T : ℕ):=8*T+2*max 2 cutoff+30+1+HierarchyBudget.sourceBound source T+1
def bound (cutoff T : ℕ):=sourceBound source cutoff T+1+parserBound T (HierarchyBudget.sizeBound source T)+1

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdOracle
