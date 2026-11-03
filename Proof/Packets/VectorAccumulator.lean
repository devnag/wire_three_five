import Proof.Packets.VectorAccumulatorData

/-! Exact forward-child accumulator transaction. Load the stored accumulator,
add the current right operand, then physically store the new accumulator. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def add := TapeEmbedding.machine 2 (ReusableArithmetic.machineLeft NormalizedAddition.machine)
def machine := Composition.machine load (Composition.machine add save)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
