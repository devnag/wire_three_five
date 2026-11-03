import Proof.Packets.PacketsXWalkLiteralVisit
import Proof.Packets.PacketsXWalkTimeLoop

/-! The resident walk advances while retaining the palette, its bounded
workspace, and the transcript at its current cursor. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralAdvance
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk
open PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
noncomputable section

def machine := TapeEmbedding.machine 317 (TapeEmbedding.machine 7 WalkPoweredRun.machine)

end
end Theorem25Completion.WalkLiteralAdvance
