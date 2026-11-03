import Proof.Packets.WindowSeedScalar
import Proof.Packets.WindowSeedBody

/-! The actual raw level is derived from the retained successor tag.
Both old private allocations are cleared; the original tag survives and the
temporary counter is erased after conversion. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ModeLevelRaw
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open WindowSeed (source)

def clearSlots : Fin 4→Fin 5 := ![1,2,3,4]
def copySlots : Fin 4→Fin 5 := ![0,2,3,4]
def predSlots : Fin 1→Fin 5 := ![2]
def rawSlots : Fin 3→Fin 5 := ![2,1,4]
def lastSlots : Fin 3→Fin 5 := ![2,3,4]
noncomputable def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def copy := RecoveryFocus.machine copySlots WindowSeed.copy
noncomputable def pred := RecoveryFocus.machine predSlots WindowSeed.countPred
noncomputable def raw := RecoveryFocus.machine rawSlots WindowSeed.raw
noncomputable def last := RecoveryFocus.machine lastSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine clear (Composition.machine copy
  (Composition.machine pred (Composition.machine raw last)))

end PCJ9eff70d512234a4c_Fixed.Materializer.ModeLevelRaw
