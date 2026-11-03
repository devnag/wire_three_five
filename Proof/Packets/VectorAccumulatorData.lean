import Proof.Packets.PhysicalCopyInto
import Proof.Packets.ReusableArithmeticLeft
import Proof.Packets.ReusableNormalizedArithmetic

/-! Resident accumulator storage alongside the reusable arithmetic arena.
Loading and saving are actual fixed-width copies with all heads restored. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def load := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 34 25)
  (PhysicalCopyInto.machine (31 : Fin 36) 35 28)
def save := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 25 34)
  (PhysicalCopyInto.machine (31 : Fin 36) 28 35)



end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
