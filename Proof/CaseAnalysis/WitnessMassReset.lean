import Proof.CaseAnalysis.WitnessMassStep

/-! Reinitialize the existing mass accumulator between sums, retaining the
same paid width words and clearing driver. No policy is recomputed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassReset
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorSumFold CompetitorReusableDecision CompetitorRationalDecision
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassReset
