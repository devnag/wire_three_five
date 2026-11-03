import Proof.Packets.PhysicalConditional
import Proof.Rows.PhysicalFocusBoundary

/-! A physical bit test followed by an optional ordinary worker call. The
branch is chosen from the actual tape under the actual head. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalBitCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

def probe {t : Nat} (slot : Fin t) : Machine t 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val != 0
  rule:=fun q bits=>if q.val=0 then
    some ⟨if bits slot then 1 else 2,fun _=>none,fun _=>.stay⟩ else none

def accept (q : Fin 3) : Bool := q.val==1
noncomputable def machine {t s : Nat} (slot : Fin t) (p : Machine t s) :=
  PhysicalConditional.machine (probe slot) p accept

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalBitCall
