import Proof.CaseAnalysis.WitnessMassStoredDecision

/-! Complete mass cap comparison with the exact native store retained for
the next paid sum reset. This is the original threshold-tail machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassReusableCheck
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open CompetitorSumFold CompetitorThresholdAmbient
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassReusableCheck
