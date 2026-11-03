import Proof.Packets.PacketsXWalkLiteralResident
import Proof.Packets.PacketsXWalkLiteralJoined

/-! A complete cold walk-transcript program. Vector workspace, walk scratch,
rewind logs and the transcript are physically created from empty tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open VectorBottomUp CloseoutRowsModeCache Theorem25Completion.CycleBounds
noncomputable section
variable {population active depth n : Nat}

def residentArena := TapeEmbedding.machine 1 (TapeEmbedding.machine 317 residentMachine)

attribute [local irreducible] residentArena machine

end
end Theorem25Completion.WalkLiteralCold
