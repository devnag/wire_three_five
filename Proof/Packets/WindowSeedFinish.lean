import Proof.Packets.WindowSeedDock
import Proof.Packets.WindowWidthDriver

/-! Paid retirement of temporary unary metadata and construction of the
outer window count from the retained actual half-window. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def clearOneSlots (d : Fin 69) : Fin 3→Fin 69 := ![d,50,51]
def clearOneAt (d : Fin 69) := RecoveryFocus.machine (clearOneSlots d) (RecoveryScratchErase.resetMachine 1)
def widthSlots : Fin 2→Fin 69 := ![61,68]
def widthAt := RecoveryFocus.machine widthSlots WindowWidthDriver.machine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
