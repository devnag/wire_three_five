import Proof.CaseAnalysis.WitnessBoundedFamilyLayout
import Proof.CaseAnalysis.WitnessFamilySupportLayout

/-! The original all-input bounded header pays exactly one cold mode.
The hierarchy-independent tail covers both mode choices before k is fixed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def outerBound (a : PointwisePCPPAlgorithm) (G D copies E K symDen thrDen : ℕ) (delta : ℚ) (N : ℕ):=
  26010*(N+1)^2+2+
    ColdFamily.outerBound source a G D copies 5 E K symDen delta true N+
    ColdFamily.outerBound source a G D copies 9 E K thrDen delta false N

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
