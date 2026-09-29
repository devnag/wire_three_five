import Proof.CaseAnalysis.WitnessGcdPolicy
import Proof.Hierarchy.CompetitorGcd

/-! The guarded consumer's complete cold gcd check. Two paid copies retain
the exact coefficient fields; the existing cold initializer and loop work
only on their copies, and the existing classifier tests the actual gcd. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalGcd
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftSlots : Fin 4→Fin 18:=![0,2,3,4]
def rightSlots : Fin 4→Fin 18:=![1,5,6,7]
def gcdSlots : Fin 7→Fin 18:=![2,5,8,9,10,11,12]
def kindSlots : Fin 6→Fin 18:=![8,13,14,15,16,17]
noncomputable def left:=RecoveryFocus.machine leftSlots copyMachine
noncomputable def right:=RecoveryFocus.machine rightSlots copyMachine
noncomputable def gcd:=RecoveryFocus.machine gcdSlots
  (Composition.machine CompetitorGcd.cold CompetitorGcd.machine)
noncomputable def kind:=RecoveryFocus.machine kindSlots CompetitorWitnessKind.machine
noncomputable def first:=Composition.machine left right
noncomputable def second:=Composition.machine first gcd
noncomputable def machine:=Composition.machine second kind


end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalGcd
