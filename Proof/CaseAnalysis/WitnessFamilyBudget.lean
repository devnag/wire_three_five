import Proof.CaseAnalysis.WitnessFamilyMeaning

/-! The actual family continuation, including physical P/H production,
has a source-fixed polynomial bound independent of hierarchy k and code. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def tailBound (a : PointwisePCPPAlgorithm) (G D copies E K : ℕ) (delta : ℚ) (N : ℕ) :=
  FamilyCapacity.budget E K N+1+
    FamilyResources.totalCost (scale source a G D copies delta N) (FamilyCapacity.value E K N)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
