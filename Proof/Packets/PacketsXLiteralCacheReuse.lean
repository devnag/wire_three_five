import Proof.Packets.PacketsXLiteralCacheReload

/-! Reentry of the reflected-cache provider. The previous cache and all
private backing are physically cleared, metadata is reloaded from retained
actual templates, and the new exact stream is returned at cursor zero. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheReuse
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.ProjectionNormalization Completion
open Theorem25Completion Theorem25Completion.CycleLiteralPairCost
noncomputable section

abbrev loop:=LiteralCacheCold.loop
abbrev rewind:=LiteralCacheCold.rewind
def machine:=Composition.machine (Composition.machine LiteralCacheReload.machine loop) rewind


end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheReuse
