import Proof.Hierarchy.CompetitorCountProducerHeads

/-! Cold preparation for the six-field count record. The sole size input is
the short scalar width. The existing dimension producer writes its wide
width; the zero normalizer then writes both the fourth field and the exact
zero counter used to append all six fields. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountRecordPrepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dimensionSlots (i : Fin 19) : Fin 23 := i.castAdd 4
def zeroSlots : Fin 5 → Fin 23 := ![15,19,20,21,22]
noncomputable def dimensions := RecoveryFocus.machine dimensionSlots CompetitorDimensions.machine
noncomputable def zero := RecoveryFocus.machine zeroSlots ClockNormalize.machine
noncomputable def machine := Composition.machine dimensions zero
def budget (b : ℕ) := CompetitorDimensions.budget b+1+4*CompetitorRationalDecision.width b+4

end NearCubicWires.RepairOrdinary.CompetitorCountRecordPrepare
