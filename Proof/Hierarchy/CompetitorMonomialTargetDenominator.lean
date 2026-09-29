import Proof.Hierarchy.CompetitorMonomialTargetWidth

/-! The exact coefficient-normalization denominator is physically widened
to the same common scalar width as every other record in the whole fold. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorRationalDecision CompetitorMonomialProducts CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outer (i : Fin 75) : Fin 79 := i.castAdd 4
def denominatorSlots : Fin 5 → Fin 79 := ![75,38,76,77,78]
noncomputable def prefixProgram := RecoveryFocus.machine outer prepareProgram
noncomputable def denominatorProgram := RecoveryFocus.machine denominatorSlots ClockNormalize.machine
noncomputable def targetProgram := Composition.machine prefixProgram denominatorProgram


end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
