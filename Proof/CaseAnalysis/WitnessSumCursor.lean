import Proof.CaseAnalysis.RowsCircuitCounterReturn
import Proof.CaseAnalysis.WitnessSumReset

/-! The actual term counter enters and leaves its sentinel position with
one paid step. The consumed field stream returns with the existing H
rewind driver/log before the successful sum-bank clear. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumCursor
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions (direction : HeadMove) (i : Fin 3061) := if i=2532 then direction else .stay
def move (direction : HeadMove) := DecompositionCountPosition.move (directions direction)
def rewindSlots : Fin 3 → Fin 3061 := ![722,2530,2531]
noncomputable def rewind := RecoveryFocus.machine rewindSlots CompetitorRecordRewind.machine

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumCursor
