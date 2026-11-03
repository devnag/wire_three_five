import Proof.Packets.PacketsXVectorTerminalDock

/-! Both resident vector banks are physically initialized before the depth
loop: terminal one/zeros in the previous bank and zeros in the next bank. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] PhysicalZeroBank.machine terminalPrevious

def nextSlots : Fin 4→Fin 299 := ![31,257,263,297]
def initializeNext := RecoveryFocus.machine nextSlots PhysicalZeroBank.machine
def initializeVectors := Composition.machine terminalPrevious initializeNext

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
