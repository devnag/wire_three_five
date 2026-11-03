import Proof.PCP.ProjectionDimensionTemplate
import Proof.MachineModel.ClockUnarySum
import Proof.MachineModel.Runs

/-! A fixed finite program computes c*n+d from one raw unary n. Both constants
are printed by finite control, all intermediate words are physically produced,
and every head returns to zero. Pool seed uses (8,12), (1,1), and (2,0). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Completion.UnaryAffine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization

def templateSlots : Fin 3→Fin 11 := ![0,1,2]
def powerSlots : Fin (DimensionPower.tapes 1)→Fin 11 := ![1,3,4,5,6]
def literalSlots : Fin 2→Fin 11 := ![7,8]
def sumSlots : Fin 4→Fin 11 := ![5,7,9,10]


noncomputable def machine (c d : Nat) := Composition.machine
  (Composition.machine
    (Composition.machine (RecoveryFocus.machine templateSlots (DimensionTemplate.machine false))
      (RecoveryFocus.machine powerSlots (DimensionPower.machine 1 c)))
    (RecoveryFocus.machine literalSlots (HierarchyFixedWord.machine (List.replicate d true))))
  (RecoveryFocus.machine sumSlots ClockUnarySum.machine)

end Completion.UnaryAffine
