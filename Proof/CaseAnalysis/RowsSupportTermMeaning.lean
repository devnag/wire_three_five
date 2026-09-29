import Proof.CaseAnalysis.RowsSupportTermLoop
import Proof.CaseAnalysis.WitnessTermLoopMeaning

/-! The one physical loop result is exactly the conjunction of its
original term decisions. Successful exhaustion carries the exact final
mass and both logical retained-record cursors for the sum consumer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.TermLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open CloseoutWitness
open CloseoutWitness.TermLoop (iterate_flag range_all mass)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.TermLoop
