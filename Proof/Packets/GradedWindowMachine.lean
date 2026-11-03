import Proof.Packets.GradedHalveLoop
import Proof.Packets.UnaryThird
import Proof.Packets.RawUnaryOffset
import Proof.Packets.PhysicalIndexReload

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def copyRoot := PhysicalCopyInto.machine (12 : Fin 13) 11 0
def thirdSlots : Fin 3→Fin 13 := ![6,7,8]
def third := RecoveryFocus.machine thirdSlots UnaryThird.returned
def floor := Composition.machine (PhysicalIndexReload.move (6 : Fin 13) .left)
  (Composition.machine third (PhysicalIndexReload.move (6 : Fin 13) .right))
def halfSlots : Fin 7→Fin 13 := ![0,1,2,3,4,5,7]
def halves := RecoveryFocus.machine halfSlots GradedHalveLoop.machine
def offsetSlots : Fin 3→Fin 13 := ![0,9,10]
def offset := RecoveryFocus.machine offsetSlots (RawUnaryOffset.returned 64)
def clearValue := PhysicalCopyInto.machine (12 : Fin 13) 1 0
def clearQuotient := PhysicalCopyInto.machine (12 : Fin 13) 1 7

end
end PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
