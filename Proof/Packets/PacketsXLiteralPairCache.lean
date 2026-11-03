import Proof.Packets.PacketsXLiteralPairReusable
import Proof.Packets.VectorCounterDecrement
import Proof.Packets.PhysicalRepeatStep

/-! Actual descending reflected literal cache. The counter is decremented
before every record, so the emitted numeric Nat.pair codes have exactly the
frozen reverse order, including the zero code at the end of terminal caches. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairCache
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def decrement := RecoveryFocus.machine LiteralPairReusable.indexSlot VectorCounter.decrement
def body := Composition.machine decrement LiteralPairReusable.machine
def machine := RepeatMachine.machine body (fun _ _=>true)


end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairCache
