import Proof.CaseAnalysis.WitnessFamilyFromPolicyLayout

/-! The retained actual source policy pays P/H and immediately executes
the complete family verifier, including all raw rejection branches. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFromPolicy
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth FamilyResources
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFromPolicy
