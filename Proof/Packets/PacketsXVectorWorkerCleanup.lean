import Proof.Packets.PacketsXVectorWorkerArena

/-! Paid cleanup of all seventeen numeric scratch ports. The metadata outputs
and retained masters are outside the erased range. The same physical raw-R
and log backing are returned, so the operation is reusable. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def scratch (j : Fin 17) : Fin 296 := ⟨264+j.val,by omega⟩
def eraseSlots : Fin 19→Fin 296 := Fin.addCases (m:=17) (n:=2) (motive:=fun _=>Fin 296)
  scratch (![32,33])
def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 17)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
