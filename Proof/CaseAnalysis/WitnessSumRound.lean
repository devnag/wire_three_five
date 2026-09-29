import Proof.CaseAnalysis.WitnessSumCleanup

/-! One complete raw sum: exact header and actual count, retained count
record, counted original terms, fixed mass check, and successful reset.
Every failure stops before the next stage and needs no restored layout. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumRound
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def passed (C T : ℕ) (q : ℚ) (bits arity : List Bool) (circuitPass : List Bool → Bool):=
  SumHeader.flag bits arity T && SumBody.passed C q (SumHeader.words bits) circuitPass

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumRound
