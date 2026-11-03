import Proof.Packets.PacketsXVectorLiteralPaletteBoot
import Proof.Amplification.RecoveryScratchErase

/-! Paid full-arena erasure and restoration from retained input masters. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding CloseoutRowsModeCache
noncomputable section

def paletteEraseSlots (j : Fin 301) : Fin 316 := j.natAdd 15
def paletteErase := RecoveryFocus.machine paletteEraseSlots (RecoveryScratchErase.resetMachine 299)
def paletteReset := Composition.machine paletteLower paletteErase

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
