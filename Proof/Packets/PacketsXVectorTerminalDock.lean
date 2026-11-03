import Proof.Packets.VectorTerminalBank
import Proof.Amplification.RecoveryScratchErase
import Proof.Packets.GradedWindowReusable
import Proof.Packets.PacketsXDeltaMetadata
import Proof.Packets.PhysicalIndexReload

/-! The actual terminal-bank initializer in the shared299-port controller.
Both bank allocations begin at empty logical banks and accept outer padding
for a retained physical capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] VectorTerminalBank.machine PhysicalZeroBank.machine

def terminalSlots : Fin 8→Fin 299 := ![31,256,263,296,24,25,28,258]
def terminalBody := RecoveryFocus.machine terminalSlots VectorTerminalBank.machine
def terminalPrevious := Composition.machine (PhysicalIndexReload.move (24 : Fin 299) .right)
  (Composition.machine terminalBody (Composition.machine
    (PhysicalIndexReload.move (24 : Fin 299) .left) (PhysicalIndexReload.move (28 : Fin 299) .left)))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
