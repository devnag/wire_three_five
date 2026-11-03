import Proof.Packets.PacketBankPrimitives

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def lookup := Composition.machine countDown
  (Composition.machine seek (Composition.machine seek
    (Composition.machine copyPayload (Composition.machine seekRow
      (Composition.machine copyCount (Composition.machine backRow
        (Composition.machine back (Composition.machine back countUp))))))))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
