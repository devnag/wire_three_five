import Proof.Hierarchy.CompetitorSumPrepare

/-! Actual copyback of the computed numerator pair and denominator. Each
old accumulator field is cleared first; framed copies preserve result words
and restore all local heads, retaining the term-stream cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resultSlot : Fin 3 → Fin 94 := ![63,64,85]
def copySlots (j : Fin 3) : Fin 4 → Fin 94 := ![resultSlot j,accumulatorSlot j,92,93]
noncomputable def copyProgram (j : Fin 3) := RecoveryFocus.machine (copySlots j) copyMachine
noncomputable def copyAllProgram := Composition.machine (copyProgram 0)
  (Composition.machine (copyProgram 1) (copyProgram 2))

end NearCubicWires.RepairOrdinary.CompetitorSumFold
