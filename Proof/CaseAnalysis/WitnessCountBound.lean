import Proof.MachineModel.UWalkUnary
import Proof.CaseAnalysis.ScheduleCompare

/-! The canonical traversal's actual count is compared with a paid policy
cap. Only that bounded count is copied; a declared numeral is never expanded. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CountBound
open LocalBitMultitape RecoveryRootRound RepairSource VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def copySlots : Fin 3→Fin 8:=![0,2,3]
def compareSlots : Fin 6→Fin 8:=![2,1,4,5,6,7]
def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
def compare:=RecoveryFocus.machine compareSlots CloseoutSchedule.RawCompare.machine
def machine:=Composition.machine copy compare

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.CountBound
