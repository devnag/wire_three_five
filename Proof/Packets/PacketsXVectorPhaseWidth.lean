import Proof.Amplification.RecoveryScratchErase
import Proof.Packets.GradedWindowReusable
import Proof.Packets.PacketsXDeltaMetadata
import Proof.Packets.WindowSeedPrimitives
import Proof.PCP.PCPSerializerTapeSupport
import Proof.Packets.SourceDigitWidth

/-! Recompute the provider's logarithmic subset width from its actual count.
The raw input is physically copied, the twelve-port binary/length worker runs,
its result overwrites185, and every private work tape is erased. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open RecoveryRootRound
noncomputable section

def widthSlots (j : Fin 12) : Fin 299 := ⟨283+j.val,by omega⟩
def rawSlots : Fin 3→Fin 299 := ![184,283,33]
def widthEraseSlots : Fin 14→Fin 299 := Fin.addCases (m:=12) (n:=2) (motive:=fun _=>Fin 299)
  widthSlots (![32,33])
def widthRaw := RecoveryFocus.machine rawSlots WindowSeed.raw
def widthWorker := RecoveryFocus.machine widthSlots Completion.SourceDigitWidth.machine
def widthCopy := PhysicalCopyInto.machine (31 : Fin 299) 293 185
def widthErase := RecoveryFocus.machine widthEraseSlots (RecoveryScratchErase.resetMachine 12)
def regenerateWidth := Composition.machine widthRaw
  (Composition.machine widthWorker (Composition.machine widthCopy widthErase))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
