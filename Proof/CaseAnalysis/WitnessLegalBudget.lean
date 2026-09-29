import Proof.CaseAnalysis.WitnessLegalBudgetEnvelope

/-! The actual guarded source request enters one uniform legal-policy
envelope whose degree is fixed before hierarchy k and its encoded program. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure
open CloseoutWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def tailBound (a : PointwisePCPPAlgorithm) (G D copies e den : ℕ) (delta : ℚ) (sym : Bool) (N : ℕ) :=
  LegalBudget.envelope e den copies delta sym
    (ColdFamily.scale source a G D copies delta N+FamilyResources.coreBound D N+1)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
