import Proof.Packets.VectorTransferLoop

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorTransfer
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def backSourceSlots : Fin 4→Fin 6 := ![0,1,4,5]
def backTargetSlots : Fin 4→Fin 6 := ![0,2,4,5]
def backSource := RecoveryFocus.machine backSourceSlots MaskBack.machine
def backTarget := RecoveryFocus.machine backTargetSlots MaskBack.machine
def machine := Composition.machine loop (Composition.machine backSource
  (Composition.machine backSource (Composition.machine backTarget backTarget)))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorTransfer
