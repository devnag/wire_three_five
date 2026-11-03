import Proof.Packets.PacketsXVectorCoordinateCollectReset
import Proof.Packets.PacketsXVectorLiteralCoordinateReset
import Proof.Rows.PhysicalFocusBoundary

/-! One fixed ordinary 299-tape program builds the literal vector and then
materializes every normalized masked coordinate by whole-coordinate
substitution. All three nested vector loops and the coordinate loop use
concrete machines with proved executions. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

def literalProgram:=Composition.machine (machine WindowProvider.literalProvider WindowProvider.levelProvider)
  (TapeEmbedding.machine 2 (collectedCandidates literalCoordinateCallback))
attribute [local irreducible] machine collectedCandidates literalCoordinateCallback

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
