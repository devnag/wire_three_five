import Proof.Packets.VectorAccumulatorData

/-! Reset saved parent-accumulator storage using the arithmetic arena's
actual retained zero tape. The R-bit writes and both cursor returns are paid. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def reset := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 0 34)
  (PhysicalCopyInto.machine (31 : Fin 36) 0 35)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
