import Proof.CaseAnalysis.WitnessSumFinish

/-! The reusable Store itself bounds every native tape. No per-iteration
workspace promise is needed after choosing the shared actual capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassCapacity
open LocalBitMultitape CompetitorSumFold CompetitorReusableDecision SignedSortKey
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassCapacity
