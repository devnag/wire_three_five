import Proof.Packets.VectorAccumulatorData

/-! Actual transfer of the current right packet into the left operand.
The right packet and both resident accumulator tapes are preserved. -/
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
noncomputable section

def rightToLeft := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 26 25)
  (PhysicalCopyInto.machine (31 : Fin 36) 27 28)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
