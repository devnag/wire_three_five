import Proof.Packets.MaskAdditionReady
import Proof.PCP.ProjectionNormalizationClauseEquality
import Proof.Packets.MaskFrameLoop
import Proof.Packets.PhysicalParityScan
import Proof.Packets.NormalizerCold

/-! Fixed physical ports for raw-sum production followed by cold
ordered normalization. Operands, counts, and two width templates are the
only nonconstant entry data. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedAddition
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch

def additionSlots : Fin 9→Fin 30 := ![24,25,26,0,3,27,28,13,29]
noncomputable def additionMachine := RecoveryFocus.machine additionSlots MaskAddition.machine
noncomputable def normalizeMachine := TapeEmbedding.machine 6 NormalizeCold.machine
noncomputable def machine := Composition.machine additionMachine normalizeMachine

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedAddition
