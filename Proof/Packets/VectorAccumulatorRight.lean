import Proof.Packets.VectorAccumulator

/-! Symmetric resident-accumulator transaction for foldr order: the current
left product is added to the old stored accumulator on the right. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def loadRight := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 34 26)
  (PhysicalCopyInto.machine (31 : Fin 36) 35 27)
def saveRight := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 26 34)
  (PhysicalCopyInto.machine (31 : Fin 36) 27 35)

def addRight := TapeEmbedding.machine 2 (ReusableArithmetic.machine NormalizedAddition.machine)
def machineRight := Composition.machine loadRight (Composition.machine addRight saveRight)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
