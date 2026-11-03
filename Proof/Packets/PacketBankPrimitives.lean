import Proof.Packets.PhysicalBankCopy
import Proof.Rows.PhysicalDriverMoves
import Proof.Rows.MaskProductBody

/-! Actual six-tape packet bank operations. A packet occupies two R-bit
blocks, holding the padded raw mask bank and padded physical row counter. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def indexedSlots : Fin 4→Fin 6 := ![0,1,5,4]
def rowSlots : Fin 3→Fin 6 := ![0,1,5]
def payloadSlots : Fin 3→Fin 6 := ![0,1,2]
def countSlots : Fin 3→Fin 6 := ![0,1,3]
def appendPayloadSlots : Fin 3→Fin 6 := ![0,2,1]
def appendCountSlots : Fin 3→Fin 6 := ![0,3,1]
def counterSlot : Fin 1→Fin 6 := ![3]
def seek := RecoveryFocus.machine indexedSlots MaskSeek.machine
def back := RecoveryFocus.machine indexedSlots MaskBack.machine
def seekRow := RecoveryFocus.machine rowSlots MaskSeek.body
def backRow := RecoveryFocus.machine rowSlots MaskBack.body
def copyPayload := RecoveryFocus.machine payloadSlots PhysicalBankCopy.machine
def copyCount := RecoveryFocus.machine countSlots PhysicalBankCopy.machine
def appendPayload := RecoveryFocus.machine appendPayloadSlots PhysicalBankCopy.machine
def appendCount := RecoveryFocus.machine appendCountSlots PhysicalBankCopy.machine
def countDown := RecoveryFocus.machine counterSlot (Completion.PhysicalDriverMoves.machine 1 .left)
def countUp := RecoveryFocus.machine counterSlot (Completion.PhysicalDriverMoves.machine 1 .right)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
