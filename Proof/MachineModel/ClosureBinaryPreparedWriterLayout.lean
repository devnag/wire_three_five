import Proof.MachineModel.ClosureRawRelabelFamily
import Proof.MachineModel.ClosureBinaryWriter

/-! Consumer-first layout for producing native source 262 before the fixed
cold writer. Raw-family output shares 262, its repeat driver shares 277;
all seven other work tapes and one paid reset log are beyond the 440 bank. -/
namespace NearCubicWires.P1Closure.BinaryPreparedWriter
open LocalBitMultitape RepairOrdinary ExtIncidence ExtDecompositionBatch RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots : Fin 10→Fin 448:=![440,441,442,443,262,444,445,446,277,447]
noncomputable def prepare:=RecoveryFocus.machine slots
  (MaskedReset.machine RawRelabelFamily.machine (fun i=>decide (i=4)))
noncomputable def writer:=TapeEmbedding.machine 8 CompactColdFamily.machine
noncomputable def machine:=Composition.machine prepare writer


end
end NearCubicWires.P1Closure.BinaryPreparedWriter
