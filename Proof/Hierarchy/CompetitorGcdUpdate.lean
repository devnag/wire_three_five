import Proof.Hierarchy.CompetitorGcdFields

/-! Physical subtraction and register replacement in the same seven-tape
gcd bank. All overwritten fields have the original witness width. -/
namespace NearCubicWires.RepairOrdinary.CompetitorGcd
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def subSlots (i : Fin 2) : Fin 4→Fin 7 := ![![0,1] i,![1,0] i,2,6]
def copySlots (i : Fin 2) : Fin 4→Fin 7 := ![2,i.castAdd 5,5,6]
def selectSlots (i : Fin 2) : Fin 4→Fin 7 := ![i.castAdd 5,2,5,6]
noncomputable def subtract (i : Fin 2) := RecoveryFocus.machine (subSlots i) subtractMachine
noncomputable def copy (i : Fin 2) := RecoveryFocus.machine (copySlots i) copyMachine
noncomputable def select (i : Fin 2) := RecoveryFocus.machine (selectSlots i) copyMachine

noncomputable def update (i : Fin 2) := Composition.machine (subtract i) (copy i)

end NearCubicWires.RepairOrdinary.CompetitorGcd
