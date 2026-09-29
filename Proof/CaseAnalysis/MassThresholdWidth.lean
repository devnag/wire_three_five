import Proof.CaseAnalysis.WitnessCoefficientPolicy

/-! The fixed exact mass threshold already fits the produced coefficient
width. Its reduced fraction is bounded by the original rational parameters;
no extra input cutoff, larger mass cap or runtime width test is required. -/
namespace NearCubicWires.RepairSource.CloseoutMassThreshold
open RepairOrdinary RepairRepresentation RepairXor CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def literalWidth (delta : ℚ) (copies : Nat) := natBitLength (2*delta.den^copies)

end NearCubicWires.RepairSource.CloseoutMassThreshold
