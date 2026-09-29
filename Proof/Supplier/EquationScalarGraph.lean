import Proof.Supplier.EquationScalarPrepare
import Proof.Supplier.EquationScalarEmit

/-! A fixed finite graph for the two signed scalar operations. Every node
is an already executed local program; graph returns cost a physical step. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar.Graph
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def incSlots : Fin 2→Fin 12 := ![2,5]
def predSlots : Fin 3→Fin 12 := ![2,4,5]
def scanSlots : Fin 4→Fin 12 := ![2,6,7,8]
def emitSlots : Fin 5→Fin 12 := ![2,1,7,9,11]
def sizes : Fin 5→Nat := ![10,5,7,8,8]
def programs (negate : Bool) : (j : Fin 5)→Machine 12 (sizes j) :=
  Fin.cases Prepare.machine (Fin.cases
    (RecoveryFocus.machine incSlots FramedIncrement.machine) (Fin.cases
    (RecoveryFocus.machine predSlots RecoveryListPredecessor.machine) (Fin.cases
    (RecoveryFocus.machine scanSlots Scan.machine) (Fin.cases
    (RecoveryFocus.machine emitSlots (Emit.machine negate)) (fun i => nomatch i)))))
def next (negate : Bool) (j : Fin 5) (_ : Fin (sizes j)) (bs : Fin 12→Bool) : Option (Fin 5) :=
  if j=0 then some (if negate then 3 else if bs 1 then 2 else 1)
  else if j=1 ∨ j=2 then some 3 else if j=3 then some 4 else none
def machine (negate : Bool) := RecoveryCalls.machine sizes (programs negate) 0 (next negate)


end
end NearCubicWires.RepairOrdinary.EquationScalar.Graph
