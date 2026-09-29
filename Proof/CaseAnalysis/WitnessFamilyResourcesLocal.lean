import Proof.CaseAnalysis.CloseoutWitnessFamilyColdRun

/-! Uniform numerical bounds for the unchanged all-raw family parser.
The scalar S includes the actual source quantities; its eventual polynomial
degree is fixed before the hierarchy clock. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def capacity (S : ℕ) := 100000000000000000000000000000000*(S+2)^26

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
