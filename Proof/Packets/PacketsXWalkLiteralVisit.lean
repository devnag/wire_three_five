import Proof.Packets.PacketsXVectorLiteralRefreshedCollect
import Proof.Packets.PacketsXWalkPaletteSeedReady
import Proof.Packets.PhysicalPrepend

/-! One complete paid walk visit: decode the resident vertex, overwrite
its three Toeplitz seed words, rebuild all literal coordinates, and append
the resulting vector to the ordered transcript. No execution is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralVisit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open PCJ9eff70d512234a4c_Fixed.Materializer
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds
open VectorBottomUp SubstitutionCensus
noncomputable section

def machine := Composition.machine (TapeEmbedding.machine 1 WalkPaletteSeedReady.machine)
  (PhysicalPrepend.machine 15 literalPaletteRefreshCollectProgram)
attribute [local irreducible] WalkPaletteSeedReady.machine literalPaletteRefreshCollectProgram

end
end Theorem25Completion.WalkLiteralVisit
