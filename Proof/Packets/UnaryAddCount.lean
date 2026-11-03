import Proof.Packets.PhysicalRepeatStep
import Proof.Packets.VectorCounter

/-! Add an actual unary count to a resident unary counter. The Repeat driver
is scanned and restored by the ordinary machine; no sum word is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.UnaryAddCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def machine := RepeatMachine.machine VectorCounter.increment (fun _ _=>true)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.UnaryAddCount
