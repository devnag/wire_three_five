import Proof.Packets.PacketsXVectorControllerInitialize
import Proof.Packets.PacketVector

/-! Physical dense atom-bank allocation in the fixed 299-tape arena. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def denseSlots : Fin 4 → Fin 299 := ![31,140,263,24]
def allocateDense := RecoveryFocus.machine denseSlots PhysicalZeroBank.machine
def initializeDense := Composition.machine (PhysicalIndexReload.move (24 : Fin 299) .right)
  (Composition.machine allocateDense (PhysicalIndexReload.move (24 : Fin 299) .left))
attribute [local irreducible] PhysicalZeroBank.machine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
