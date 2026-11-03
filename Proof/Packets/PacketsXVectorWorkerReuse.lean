import Proof.Packets.PacketsXVectorWorkerArena
import Proof.Packets.PhysicalCopyInto

/-! Existing metadata frames are physically cleared before their next cold
scalar calculation. No prior frame is replaced by a mathematical assignment. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def clearFields := Composition.machine
  (Composition.machine (PhysicalCopyInto.machine (31 : Fin 296) 0 180)
    (PhysicalCopyInto.machine (31 : Fin 296) 0 181)) (PhysicalCopyInto.machine (31 : Fin 296) 0 182)
def reusableMetadata := Composition.machine clearFields metadataMachine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
