import Proof.Packets.PhysicalCopyInto
import Proof.Rows.PhysicalDriverMoves
import Proof.Packets.VectorCounterDecrement

/-! Reload a physical unary index from a resident padded word. The index
cursor is lowered from1 to0, R bits are copied, and the cursor is restored. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalIndexReload
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slot {t : Nat} (target : Fin t) : Fin 1→Fin t := fun _=>target
def move {t : Nat} (target : Fin t) (d : HeadMove) :=
  RecoveryFocus.machine (slot target) (Completion.PhysicalDriverMoves.machine 1 d)
def machine {t : Nat} (width source target : Fin t) := Composition.machine (move target .left)
  (Composition.machine (PhysicalCopyInto.machine width source target) (move target .right))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalIndexReload
