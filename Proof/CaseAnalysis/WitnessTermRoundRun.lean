import Proof.CaseAnalysis.WitnessTermRoundFinish

/-! The retained-field reader and actual circuit receipt now join the
complete successful term controller. The circuit supplier is explicit;
its output is not decoded or copied a second time. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
