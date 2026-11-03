import Proof.Packets.PacketsXVectorLiteralPalette
import Proof.Rows.PhysicalDriverMoves

/-! Actual fifteen-word fanout and paid positioning of the seven arena
cursors. All 299 destination tapes may be empty at entry. -/
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

def paletteArenaSlots (i : Fin 299) : Fin 316 := (i.natAdd 15).castAdd 2
def paletteHeadSlots : Fin 7 → Fin 316 := ![46,273,274,275,311,312,313]
def paletteRaise := RecoveryFocus.machine paletteHeadSlots (Completion.PhysicalDriverMoves.machine 7 .right)
def paletteLower := RecoveryFocus.machine paletteHeadSlots (Completion.PhysicalDriverMoves.machine 7 .left)
def coldPaletteBoot := Composition.machine (NativeFanout.machine coldSelect) paletteRaise

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
