import Proof.Packets.PacketsXWalkLiteralLoopStep

/-! One fixed ordinary program visits every vertex of a positive walk,
collecting all coordinates in time order. Its count driver is actual input
and is restored; private work is existentially hidden and remains bounded. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer
open Theorem25Completion.CycleBounds VectorBottomUp
noncomputable section
variable {population active depth n : Nat}

def machine := Composition.machine (RepeatMachine.machine body (fun _ _=>true))
  (TapeEmbedding.machine 1 WalkLiteralVisit.machine)
attribute [local irreducible] body WalkLiteralVisit.machine

end
end Theorem25Completion.WalkLiteralLoop
