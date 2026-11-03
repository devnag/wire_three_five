import Proof.Packets.MaskFrameReverse
import Proof.Packets.MaskProductReady

/-! Actual raw addition input: the left bank in reverse record order, then
right bank, with a physically produced total count and all cursors ready. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskAddition
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
abbrev seekSlots := MaskProduct.leftBackSlots
def reverseSlots : Fin 6→Fin 9 := ![0,8,1,3,4,6]
def frameSlots : Fin 6→Fin 9 := ![0,8,2,3,4,5]
def rightBackSlots : Fin 4→Fin 9 := ![0,2,8,5]
abbrev machine := Composition.machine (RecoveryFocus.machine seekSlots MaskSeek.machine)
  (Composition.machine (RecoveryFocus.machine reverseSlots MaskFrame.reverseLoop)
    (Composition.machine (RecoveryFocus.machine frameSlots MaskFrame.loop)
      (Composition.machine (RecoveryFocus.machine rightBackSlots MaskBack.machine)
        (Composition.machine (RecoveryFocus.machine MaskProduct.countSlots PairCountReady.machine)
          (RecoveryFocus.machine MaskProduct.outputBackSlots MaskBack.machine)))))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MaskAddition
