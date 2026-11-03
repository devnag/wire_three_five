import Proof.Packets.MaskProductOuter
import Proof.Packets.MaskProductCountReady

/-! A fixed nine-tape Cartesian mask producer. The resident raw mask banks,
B and record-width templates, and original row-count drivers are retained.
It returns the emitted support-record bank and its actual unary count with
both consumer cursors at their entry positions. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def outerSlots (i : Fin 7) : Fin 9 := i.castAdd 2
def leftBackSlots : Fin 4→Fin 9 := ![0,1,8,6]
def countSlots : Fin 1→Fin 9 := ![4]
def outputBackSlots : Fin 4→Fin 9 := ![7,3,8,4]
abbrev readyMachine := Composition.machine (RecoveryFocus.machine outerSlots outer)
  (Composition.machine (RecoveryFocus.machine leftBackSlots MaskBack.machine)
    (Composition.machine (RecoveryFocus.machine countSlots PairCountReady.machine)
      (RecoveryFocus.machine outputBackSlots MaskBack.machine)))


end
end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
