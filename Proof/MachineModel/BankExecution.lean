import Proof.CaseAnalysis.RowsCircuitCounterReturn
import Proof.MachineModel.Bridge

/-! Execute the ordered incidence stream directly into native table36, using
the existing child template38 and paid bank driver104/log105. New slots are
stream113, scratch114, and the actual raw row count115. -/
namespace NearCubicWires.ExtIncidence.BankExecution
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5 → Fin 116 := ![113,38,114,36,115]
noncomputable def printer:=RecoveryFocus.machine slots ExtIncidence.machine

def returnSlots (i : Fin 116) : Fin 3 → Fin 116 := ![i,104,105]
noncomputable def returning (i : Fin 116):=
  RecoveryFocus.machine (returnSlots i) CompetitorRecordRewind.machine
noncomputable def tableReady:=Composition.machine printer (returning 36)
noncomputable def machine:=Composition.machine tableReady (returning 115)
def budget (B C : ℕ) (ms : List (List ℕ)):=cost B ms+4*C+6

end NearCubicWires.ExtIncidence.BankExecution
