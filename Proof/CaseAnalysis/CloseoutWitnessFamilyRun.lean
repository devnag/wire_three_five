import Proof.CaseAnalysis.WitnessFamilyWork

/-! The original family code is checked once, then its actual count and
field stream drive the complete rejecting sum loop. Failed headers stop
before any sum; successful runs retain the three ordered native streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyRun
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def passed (V C T : ℕ) (q : ℚ) (bits arity : List Bool) (circuitPass : List Bool → Bool):=
  FamilyCount.accepted bits V && FamilyLoop.passed C T q (FamilyFields.words bits) arity circuitPass

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyRun
