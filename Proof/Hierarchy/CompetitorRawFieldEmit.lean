import Proof.Hierarchy.CompetitorRawFrameAppend

/-! Focus the actual scalar appender into its enclosing producer. Every
unselected head is retained, including table and term-stream cursors. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {t : ℕ} (source target counter : Fin t) : Fin 3 → Fin t := ![source,target,counter]
noncomputable def program {t : ℕ} (source target counter : Fin t) :=
  RecoveryFocus.machine (slots source target counter) CompetitorFrameAppend.machine

end NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit
