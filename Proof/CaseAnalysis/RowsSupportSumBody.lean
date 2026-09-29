import Proof.CaseAnalysis.RowsSupportSumFinish
import Proof.CaseAnalysis.WitnessSumBodyFields

/-! One complete prepared sum: the actual counted term loop rejects
immediately, or the original final mass test runs once and resets the
accumulator. Both retained record streams keep their logical cursors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumBody
open LocalBitMultitape RecoveryRootRound RecoveryExecution CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

noncomputable def machine {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ) :=
  RecoveryGatedSequence.machine (TermLoop.machine circuit) (ending k q) 724

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumBody
