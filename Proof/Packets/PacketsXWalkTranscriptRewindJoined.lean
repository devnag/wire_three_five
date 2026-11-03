import Proof.Packets.PacketsXWalkTranscriptRewindRun

/-! One ordinary counted walk program writes the exact coordinate transcript
and pays for returning the transcript head to its initial position. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptRewind
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer
open Theorem25Completion.CycleBounds VectorBottomUp
noncomputable section
variable {population active depth n : Nat}

def collectedMachine := Composition.machine WalkLiteralLoop.machine machine
attribute [local irreducible] WalkLiteralLoop.machine machine

end
end Theorem25Completion.WalkTranscriptRewind
