import Proof.Packets.IdentityCodeRecord
import Proof.Packets.VectorCounterDecrement
import Proof.Packets.PhysicalRepeatStep

/-! Runtime-counted descending identity-address cache, generated from a
retained count and a physical unary index. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def indexSlot : Fin 1→Fin 2 := ![0]
noncomputable def decrement := RecoveryFocus.machine indexSlot VectorCounter.decrement
noncomputable def body := Composition.machine decrement IdentityCodeRecord.machine
noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeLoop
