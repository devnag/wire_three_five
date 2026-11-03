import Proof.PCP.ProjectionNormalizationClauseEquality
import Proof.Packets.DedupMaterialReady
import Proof.Packets.MaskReverseReady
import Proof.Packets.ParityFilterReady
import Proof.Packets.NormalizerOrder
import Proof.Amplification.RecoveryFocusDock

/-! Fixed tape wiring and concrete reserves for the complete normalization
pipeline. Bounds only pad erased work logs, never polynomial/source bytes. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

def records (raw : List (List Bool)) := raw.map PhysicalParityScan.supportRecord



def reverseSlots : Fin 5→Fin 24 := ![13,2,14,11,15]
def filterSlots : Fin 12→Fin 24 := ![14,0,16,17,18,3,19,20,21,11,22,23]

noncomputable def dedupMachine := TapeEmbedding.machine 11 DedupMaterialReady.machine
noncomputable def reverseMachine := RecoveryFocus.machine reverseSlots MaskReverseReady.machine
noncomputable def filterMachine := RecoveryFocus.machine filterSlots ParityFilter.readyMachine
noncomputable def prefixMachine := Composition.machine dedupMachine reverseMachine
noncomputable def machine := Composition.machine prefixMachine filterMachine

end PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
