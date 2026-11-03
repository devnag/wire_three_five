import Proof.Packets.PacketsXModeCacheCommon
import Proof.Packets.WindowSeedClear
import Proof.Packets.PhysicalBoundedLeftRewind

/-! Complete reusable delta-cache call: physically clear the old output,
produce both original sibling/child halves, retain the actual child count,
and return the new source cursor. All protected parameter masters may have
common-R zero backing supplied by their actual producers. -/
set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 1000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
attribute [local irreducible] ModeCacheCommon.delta RecoveryScratchErase.resetMachine

def clearSlots : Fin 3→Fin 29 := ![20,26,27]
def backSlots : Fin 2→Fin 29 := ![28,20]
noncomputable def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def delta := TapeEmbedding.machine 1 ModeCacheCommon.delta
noncomputable def back := RecoveryFocus.machine backSlots Completion.PhysicalBoundedLeftRewind.machine
noncomputable def machine := Composition.machine clear (Composition.machine delta back)
attribute [local irreducible] machine delta

end PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheReady
