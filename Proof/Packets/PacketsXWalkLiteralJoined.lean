import Proof.Packets.PacketsXWalkLiteralPrepare

/-! The physical walk collector starts with empty vector work tapes and an
empty transcript, builds their storage, and returns the complete ordered bank. -/
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

def machine := Composition.machine prepare WalkTranscriptRewind.collectedMachine
attribute [local irreducible] prepare WalkTranscriptRewind.collectedMachine

end
end Theorem25Completion.WalkLiteralCold
