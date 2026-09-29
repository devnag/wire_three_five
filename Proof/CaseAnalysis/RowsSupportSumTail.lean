import Proof.CaseAnalysis.RowsSupportSumEnter
import Proof.CaseAnalysis.WitnessSumCleanup

/-! A false term or mass verdict halts immediately. Only the successful
whole sum body enters the single rewind/erase tail and returns the exact
next-sum layout, with all three retained output cursors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumTail
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def ending:=TapeEmbedding.machine 1 SumCleanup.machine
noncomputable def machine {s : ℕ} (body : Machine 3062 s):=
  RecoveryGatedSequence.machine body ending 724

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumTail
