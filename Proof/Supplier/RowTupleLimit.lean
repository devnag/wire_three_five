import Proof.Supplier.RowTupleColdEnumeration
import Proof.Hierarchy.HierarchyFixedWord
import Proof.MachineModel.ClockInitialKey
import Proof.Supplier.EquationScalarArithmetic

/-! Construct the tuple loop's terminal field and its paid extent from the
runtime unary product. Both fields were supplied to the earlier cold loop. -/
namespace NearCubicWires.RepairOrdinary.RowTupleLimit
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def oneSlots : Fin 2→Fin 12 := ![8,9]
def sumSlots : Fin 4→Fin 12 := ![0,8,10,11]
def fieldSlots : Fin 6→Fin 12 := ![0,1,2,3,4,5]
def predSlots : Fin 3→Fin 12 := ![1,6,7]
noncomputable def one := RecoveryFocus.machine oneSlots (HierarchyFixedWord.machine [true])
noncomputable def sum := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def field := RecoveryFocus.machine fieldSlots ClockFields.machine
noncomputable def predecessor := RecoveryFocus.machine predSlots RecoveryListPredecessor.machine
noncomputable def first := Composition.machine one sum
noncomputable def second := Composition.machine first field
noncomputable def machine := Composition.machine second predecessor

end NearCubicWires.RepairOrdinary.RowTupleLimit
