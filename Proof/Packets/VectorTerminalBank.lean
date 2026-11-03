import Proof.Packets.PhysicalZeroBank
import Proof.Packets.PacketBankWrite
import Proof.Packets.PacketVector

/-! Actual terminal-vector initialization: allocate every packet, generate
one from the runtime mask width, and overwrite the first packet. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorTerminalBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] PhysicalZeroBank.machine MaskConstant.oneMachine PacketBank.storeSelected

def allocateSlots : Fin 4→Fin 8 := ![0,1,2,3]
def oneSlots : Fin 1→Fin 8 := ![6]
def writeSlots : Fin 6→Fin 8 := ![0,1,5,6,7,2]
def allocate := RecoveryFocus.machine allocateSlots PhysicalZeroBank.machine
def one := RecoveryFocus.machine oneSlots (MaskConstant.countMachine true)
def write := RecoveryFocus.machine writeSlots PacketBank.storeSelected
def machine := Composition.machine allocate (Composition.machine one write)







end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorTerminalBank
