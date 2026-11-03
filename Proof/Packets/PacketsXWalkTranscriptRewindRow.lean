import Proof.Packets.PacketVectorRewind
import Proof.Packets.PacketsXWalkLiteralLoopRun

/-! Paid rewind of one row using the words retained by the literal collector. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptRewind
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer
open VectorBottomUp
noncomputable section

def paletteRow := RecoveryFocus.machine collectSlots PacketVectorRewind.machine
def row := PhysicalPrepend.machine 15 paletteRow

end
end Theorem25Completion.WalkTranscriptRewind
