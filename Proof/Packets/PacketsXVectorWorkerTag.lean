import Proof.Packets.PacketsXVectorWorkerArena
import Proof.Packets.PhysicalCounterCopy

/-! Runtime literal tag from the actual descending level counter. Terminal
tag zero and delta tag level+1 are both physically written into provider187. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def deltaTag := Composition.machine (PhysicalIndexReload.move (187 : Fin 296) .right)
  (Composition.machine (PhysicalCounterCopy.successor (31 : Fin 296) 260 187)
    (PhysicalIndexReload.move (187 : Fin 296) .left))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
