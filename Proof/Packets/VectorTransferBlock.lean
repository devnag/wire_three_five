import Proof.Packets.PacketBankPrimitives

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorTransfer
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def copySlots : Fin 3→Fin 5 := ![0,1,2]
def clearSlots : Fin 3→Fin 5 := ![0,3,1]
def sourceSlots : Fin 3→Fin 5 := ![0,1,4]
def targetSlots : Fin 3→Fin 5 := ![0,2,4]
abbrev copyMachine := RecoveryFocus.machine copySlots PhysicalBankCopy.machine
abbrev clearMachine := RecoveryFocus.machine clearSlots PhysicalBankCopy.machine
abbrev seekSource := RecoveryFocus.machine sourceSlots MaskSeek.body
abbrev seekTarget := RecoveryFocus.machine targetSlots MaskSeek.body
abbrev block := Composition.machine copyMachine
  (Composition.machine clearMachine (Composition.machine seekSource seekTarget))

abbrev packet := Composition.machine block block

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorTransfer
