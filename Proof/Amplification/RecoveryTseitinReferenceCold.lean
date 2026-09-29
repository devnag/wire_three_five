import Proof.Amplification.RecoveryTseitinReferenceInput
import Proof.Amplification.RecoveryTseitinReferenceRun

/-! The complete physical reference producer starts with the actual unary
arity, node position and operands. No encoded reference is supplied as input. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def order : List (Fin 4) := [0,1,2,3]
noncomputable def coldMachine := Composition.machine scalarMachine (bankMachine order)
def coldBudget (arity index left right : Nat) :=
  budget arity index left right+1+banksBudget (counts arity index left right) order
def fields (arity index left right : Nat) (k : Fin 4) :=
  ZeroPadding.pad (RecoveryTseitinTautology.Cold.driverCapacity (counts arity index left right k))
    (RepairOrdinary.frame (counts arity index left right k).bits)

end NearCubicWires.RepairSource.RecoveryTseitinReferences
