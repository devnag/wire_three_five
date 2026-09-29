import Proof.Hierarchy.CompetitorSumLoop

/-! Actual construction of the zero/zero/one rational accumulator. The
unary wide and short widths are retained. All other native input tapes are
blank; fixed one is printed by the accepted clock-field writer at q=0. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumConstants
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroSlots (j : Fin 2) : Fin 5 → Fin 88 := if j.val=0 then ![6,2,0,3,5] else ![6,7,1,8,9]
def powerSlots : Fin 6 → Fin 88 := ![10,11,12,13,14,15]
def normalizeSlots : Fin 5 → Fin 88 := ![84,11,4,16,17]
noncomputable def zeroProgram (j : Fin 2) := RecoveryFocus.machine (zeroSlots j) ClockNormalize.machine
noncomputable def powerProgram := RecoveryFocus.machine powerSlots ClockFields.machine
noncomputable def normalizeProgram := RecoveryFocus.machine normalizeSlots ClockNormalize.machine
noncomputable def machine := Composition.machine (zeroProgram 0)
  (Composition.machine (zeroProgram 1) (Composition.machine powerProgram normalizeProgram))

end NearCubicWires.RepairOrdinary.CompetitorSumConstants
