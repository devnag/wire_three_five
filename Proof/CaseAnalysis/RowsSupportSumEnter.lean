import Proof.CaseAnalysis.RowsSupportSumLayout
import Proof.CaseAnalysis.WitnessSumWorkRun

/-! The old single driver move enters the actual extended sum worker;
its new support head and tape are outside that move. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumWork
open LocalBitMultitape CloseoutWitness
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def enter {s : ℕ} (p : Machine 3062 s):=
  Composition.machine (TapeEmbedding.machine 1 (SumCursor.move .right)) p

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumWork
