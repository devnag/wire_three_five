import Proof.Rows.MinimumMaskRun

/-! Reusable minimizing-mask producer: rewind the retained native source and
input masks, clear only parser scratch, and leave the q-bit answer at head zero. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_MinimumMaskReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open StablePartition.Workspace
open PCJ45bee56da9f34d5a_MinimumMaskRun
noncomputable section

def produce := TapeEmbedding.machine 2 PCJ45bee56da9f34d5a_MinimumMaskRun.machine
def rewindSlots : Fin 7→Fin 8 := ![0,1,2,3,4,6,7]
def clearSlots : Fin 3→Fin 8 := ![1,6,7]
def rewind := RecoveryFocus.machine rewindSlots (PCJ45bee56da9f34d5a_HeaderRewind.machine 5)
def erase := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
def machine := Composition.machine (Composition.machine produce rewind) erase

end
end PCJ45bee56da9f34d5a_MinimumMaskReady
