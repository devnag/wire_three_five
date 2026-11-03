import Proof.Packets.PacketsXWalkPaletteSeedCopy
import Proof.Packets.PacketsXWalkSeedCleanup
import Proof.Packets.PacketsXVectorLiteralPaletteBoot
import Proof.Rows.PhysicalFocusBoundary

/-! Decode an actual walk vertex, copy its three seed words into retained
palette masters, and clear the decoder for the next visit. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 18000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkPaletteSeedReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
noncomputable section

def machine := Composition.machine (TapeEmbedding.machine 316 WalkSeedResident.machine)
  (Composition.machine WalkPaletteSeedCopy.machine (TapeEmbedding.machine 316 WalkSeedCleanup.machine))

end
end Theorem25Completion.WalkPaletteSeedReady
