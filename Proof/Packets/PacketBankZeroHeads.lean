import Proof.Packets.PacketBankLookup
import Proof.Packets.PacketBankPrimitives

/-! Paid cursor adapters for the reusable arithmetic arena, whose operand
payload and row-count tapes both have cursor zero at the public boundary. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def lookupZero := Composition.machine countUp (Composition.machine lookup countDown)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
