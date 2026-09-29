import Proof.Hierarchy.CompetitorWitnessBounded

/-! Literal reusable scalar operations for canonical-rational gcd checking.
The enclosing witness cap is executed before this numeric loop. -/
namespace NearCubicWires.RepairOrdinary.CompetitorGcd
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def compareSlots (i : Fin 3) : Fin 4→Fin 7 := ![![0,1,0] i,![3,3,1] i,4,6]
noncomputable def compare (i : Fin 3) := RecoveryFocus.machine (compareSlots i) compareMachine

def clear : Machine 7 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun i=>if i.val=4 then some false else none,fun _=>.stay⟩ else none
noncomputable def check (i : Fin 3) := Composition.machine clear (compare i)

end NearCubicWires.RepairOrdinary.CompetitorGcd
