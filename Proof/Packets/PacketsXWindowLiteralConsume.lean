import Proof.Packets.PacketsXWindowConsume

/-! Per-child literal windows are normalized before vector construction.
Substitution is deliberately deferred until the full vector coordinate has
been constructed, matching the frozen ordered-polynomial definition. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (cacheWord)
open NormalizedFiniteTransport WindowNativeOrder Theorem25Completion.CycleBounds

attribute [local irreducible] closeSource renameNormalize lower
noncomputable def literalConsume := Composition.machine closeSource (Composition.machine renameNormalize lower)

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
