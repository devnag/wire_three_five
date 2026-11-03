import Proof.MachineModel.CountIndexClean
import Proof.PCP.PCPSerializerCapacityFocus

/-! Dock the actual count converter into the existing native bank. Shared
ports are count115, width109, fields52/107 and driver104/log105. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 18→Fin 128:=
  ![115,116,117,118,119,120,121,122,123,124,109,52,125,126,127,107,104,105]
noncomputable def machine:=RecoveryFocus.machine slots CountIndexClean.machine

end NearCubicWires.ExtIncidence.BankCount
