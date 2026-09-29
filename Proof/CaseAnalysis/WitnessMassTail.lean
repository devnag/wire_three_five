import Proof.CaseAnalysis.WitnessMassTrace

/-! Reuse the existing native addition and copy-back directly after the
retained coefficient fields are installed. No mass-record stream is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Mass
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open CompetitorSumFold CompetitorReusableDecision
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutWitness.Mass
