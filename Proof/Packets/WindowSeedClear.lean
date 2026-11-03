import Proof.Packets.WindowSeedPrimitives
import Proof.Rows.PhysicalFocusBoundary

/-! Actual allocation/reentry clearing of every private window field. The
shared raw reserve and erase log, and all seven actual metadata masters,
are retained. The same machine accepts blank or previously used capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def privateSlot (j : Fin 60) : Fin 69 :=
  if h:j.val<50 then ⟨j.val,by omega⟩ else ⟨j.val+2,by omega⟩
def clearSlots : Fin 62→Fin 69 := Fin.addCases (m:=60) (n:=2) privateSlot ![50,51]
def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 60)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
