import Proof.Hierarchy.CompetitorCrossSchedulerDock

/-! One source-fixed ordinary program executes original framed Request ->
all signed Williams packets -> the exact cross-bucket P/N bank. The request
supplies no dimensions, matrices, capacity, zero bank or semantic premise. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open MatrixScoreBatch (Request)
open CompetitorPlaneTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def budget (a : WilliamsAlgorithm) (r : Request) := prefixBudget a r+1+
  CompetitorCrossTableCold.budget (natBitLength r.U)
    (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p

end NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
