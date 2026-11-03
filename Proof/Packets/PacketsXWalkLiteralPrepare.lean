import Proof.Packets.PacketsXWalkLiteralPalette
import Proof.Packets.PhysicalZeroRectangle

/-! Physical preparation of the 333-tape walk arena and its entire transcript.
All 299 vector work tapes and the transcript start empty. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open VectorBottomUp CloseoutRowsModeCache
noncomputable section

def bootArena := TapeEmbedding.machine 1 (PhysicalPrepend.machine 15 (TapeEmbedding.machine 1 paletteMachine))

def allocateSlots : Fin 5→Fin 333 := ![61,331,291,327,332]
def allocate := RecoveryFocus.machine allocateSlots PhysicalZeroRectangle.machine

def prepare := Composition.machine bootArena allocate

end
end Theorem25Completion.WalkLiteralCold
