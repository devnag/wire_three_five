import Proof.Hierarchy.CompetitorCrossSchedulerPrefix

/-! Narrow transport into the fixed complete cross-table. The prefix state
space remains abstract while endpoint proofs are elaborated. No program,
clock or cursor changes; this is the actual original-request caller dock. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open MatrixScoreBatch (Request)
open CompetitorPlaneTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (p : Program) (pos : ℕ) (i : Fin (tapes p)) := if i.val=93 then pos else 0

theorem cross_heads (p : Program) (pos : ℕ) (i : Fin 120) :
    CompetitorCrossTableCold.heads pos i=heads p pos (crossSlots p i) := by
  unfold CompetitorCrossTableCold.heads heads
  rw [cross_value]
  split_ifs <;> omega

end NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
