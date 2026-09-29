import Proof.CaseAnalysis.WitnessMassCheck

/-! Retained operands and bounded native scratch of the same exact mass
comparison, needed to reuse its accumulator bank for the next sum. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassCompareFields
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorRationalDecision CompetitorReusableDecision
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassCompareFields
