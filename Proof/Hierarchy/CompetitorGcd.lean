import Proof.Hierarchy.CompetitorGcdLoop

/-! Cold gcd initialization from only the two framed numeric fields.
The zero word is physically formed by copying a and subtracting a from it;
no width, zero field, scratch capacity or loop counter is supplied. -/
namespace NearCubicWires.RepairOrdinary.CompetitorGcd
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroSlots : Fin 4→Fin 7 := ![0,2,3,6]
noncomputable def coldCopy := select 0
noncomputable def coldZero := RecoveryFocus.machine zeroSlots subtractMachine
noncomputable def coldTail := Composition.machine coldZero clear
noncomputable def cold := Composition.machine coldCopy coldTail


end NearCubicWires.RepairOrdinary.CompetitorGcd
