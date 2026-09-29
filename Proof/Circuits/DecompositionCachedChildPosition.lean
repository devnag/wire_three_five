import Proof.Circuits.DecompositionSourceRecords
import Proof.Amplification.RecoveryFocusDock

/-! Position the same native decomposition cache at a selected child.
The existing counted native scan pays for preceding fields; the consumer
reads the selected weight/target block directly, without a second encoding. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCachedChild
open LocalBitMultitape RepairRepresentation DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def header := TapeEmbedding.machine 2 (PCPPQueryField.machine false)
noncomputable def machine := Composition.machine header Records.machine

end NearCubicWires.RepairOrdinary.DecompositionCachedChild
