import Proof.Packets.PhysicalRepeatStep
import Proof.MachineModel.OrdinaryFramedIncrement
import Proof.MachineModel.OrdinaryTransitionTapeZero

/-! A reusable fixed-width scalar producer. It physically zeroes the existing
framed binary allocation and increments it once for every mark of the actual
unary count driver. Scalar/count cursors and the rewind log are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ScalarFromCounter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

def count := RepeatMachine.machine FramedIncrement.machine (fun _ _=>true)
def clear := TapeEmbedding.machine 1 TransitionTapeZero.machine
def machine := Composition.machine clear count

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ScalarFromCounter
