import Proof.Packets.VectorAccumulator

/-! The closed arithmetic body of one bottom-up right contribution:
left packet times right packet, followed by accumulator plus that term.
The resulting accumulator is physically saved on ports34/35. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def multiply := TapeEmbedding.machine 2 (ReusableArithmetic.machine NormalizedMultiply.machine)
def machine := Composition.machine multiply VectorAccumulator.machine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildArithmetic
