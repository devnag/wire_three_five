import Proof.MachineModel.CountIndexCopy

/-! One shared-capacity sweep erases every count-conversion private cell.
Both copies of the actual index, the width and driver remain available. -/
namespace NearCubicWires.ExtIncidence.CountIndexClean
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 15→Fin 18:=![0,1,2,3,4,5,6,7,8,9,12,13,14,16,17]
noncomputable def erase:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 13)
noncomputable def machine:=Composition.machine CountIndexCopy.machine erase
def budget (C w M : ℕ):=CountIndex.budget w M+4*C+10

end NearCubicWires.ExtIncidence.CountIndexClean
