import Proof.Packets.PacketBankLookup

/-! Actual indexed replacement of one resident two-R-bit packet. Source
operands and all cursors are retained; every other bank entry is unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
noncomputable section

def storeSelected := Composition.machine countDown
  (Composition.machine seek (Composition.machine seek
    (Composition.machine appendPayload (Composition.machine seekRow
      (Composition.machine appendCount (Composition.machine backRow
        (Composition.machine back (Composition.machine back countUp))))))))

def storeSelectedZero := Composition.machine countUp (Composition.machine storeSelected countDown)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
