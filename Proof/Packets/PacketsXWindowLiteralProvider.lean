import Proof.Packets.PacketsXWindowEmitDock
import Proof.Packets.PacketsXWindowLevelAtoms
import Proof.Packets.PacketsXWindowLiteralConsume
import Proof.Packets.SubstitutionPrepareCopies
import Proof.Packets.WindowNativeDock
import Proof.Packets.WindowWorkspace

/-! Complete fixed per-child provider: allocate/reset private words, generate
and execute the actual nested window stream, then close, rename and normalize
it. Atom substitution is applied only after the whole literal vector. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (cacheWord)
open NormalizedFiniteTransport WindowNativeOrder Theorem25Completion.CycleBounds

attribute [local irreducible] Workspace.machine seedEmit literalConsume
noncomputable def literalProvider := Composition.machine Workspace.machine
  (Composition.machine seedEmit literalConsume)

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
