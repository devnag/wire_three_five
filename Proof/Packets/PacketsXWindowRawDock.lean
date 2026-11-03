import Proof.Packets.WindowNativeDock
import Proof.Packets.PacketsXRawSingletonSubstitution

/-! Actual singleton-cache renaming in the fixed provider arena. Only native
source122 changes; all source, cache and reusable scratch words are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (Pair cacheWord)

noncomputable def rename := RecoveryFocus.machine rawPorts RawSingletonSubstitution.machine

noncomputable def renameNormalize := Composition.machine rename normalize

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
