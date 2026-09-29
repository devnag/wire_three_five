import Proof.CaseAnalysis.RowsSupportSumTail

/-! One complete raw sum: exact header and actual count, retained count
record, counted original terms, fixed mass check, and successful reset.
Every failure stops before the next stage and needs no restored layout. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumRound
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

noncomputable def worker {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  SumWork.enter (SumWork.body circuit k q)
noncomputable def tail {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  SumTail.machine (worker circuit k q)
noncomputable def machine {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  RecoveryGatedSequence.machine (TapeEmbedding.machine 1 SumDock.reader) (tail circuit k q) 724

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumRound
