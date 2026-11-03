import Proof.MachineModel.Layout
import Proof.MachineModel.Runs
import Proof.CaseAnalysis.RowsModeCacheReuseRun
import Proof.Hierarchy.CompetitorSignedDecision
import Proof.Hierarchy.CompetitorSignedResidue
import Proof.Amplification.RecoveryRootRoundTapes

/-! The actual capped-target arithmetic has a runtime sign guard. A paid
copy supplies the second child operand, existing signed-decision code forms
both sums, and total borrow subtraction supplies the guarded target word.
Negative candidates are marked invalid; a zero target remains valid. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdOneHotTargetArithmetic
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 4→Fin 12 := ![2,3,4,5]
def decisionSlots : Fin 8→Fin 12 := ![0,2,3,1,6,7,8,9]
def subtractSlots : Fin 4→Fin 12 := ![6,7,10,11]
noncomputable def first := RecoveryFocus.machine copySlots RecoveryRootRound.copyMachine
noncomputable def second := RecoveryFocus.machine decisionSlots CompetitorSignedDecision.machine
noncomputable def third := RecoveryFocus.machine subtractSlots CompetitorSignedResidue.subtractProgram
noncomputable def machine := Composition.machine (Composition.machine first second) third

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdOneHotTargetArithmetic
