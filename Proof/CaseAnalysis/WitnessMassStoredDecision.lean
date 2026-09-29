import Proof.CaseAnalysis.WitnessMassCompareFields

/-! The actual mass decision retains an exact bounded accumulator store,
so the checked reset can serve the next sum using the same native bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassStoredDecision
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorSumFold CompetitorThresholdAmbient
open CompetitorReusableDecision CompetitorRationalDecision
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassStoredDecision
