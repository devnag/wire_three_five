import Proof.Packets.PacketsXWalkTranscriptRewindRow

/-! A counted return across all `n+1` rows of a positive walk transcript.
The existing physical count word is reused and restored. -/
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

def machine := Composition.machine (RepeatMachine.machine row (fun _ _=>true))
  (TapeEmbedding.machine 1 row)
attribute [local irreducible] row

end
end Theorem25Completion.WalkTranscriptRewind
