import Proof.CaseAnalysis.WitnessTermCommit

/-! The actual mass comparator reuses sixteen cleared parser tapes for its
constant scratch. Native mass storage remains exactly the existing Store. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassPaddedCheck
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorThresholdAmbient
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutWitness.MassPaddedCheck
