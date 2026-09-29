import Proof.CaseAnalysis.RowsFamilyLoop
import Proof.CaseAnalysis.RowsSourceMeaning
import Proof.MachineModel.Machine

namespace NearCubicWires.ExtIncidence
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution SupplierPrinter
open RepairOrdinary.CloseoutRowsSourceDigits
open RepairOrdinary.CloseoutRowsCacheInput RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawIndices {B : ℕ} (ms : List (List (Fin B))) := ms.map (List.map Fin.val)
def rawRows {B : ℕ} (ms : List (List (Fin B))) :=
  ms.map (fun m=>List.ofFn (fun i : Fin B=>decide (i∈m)))

end NearCubicWires.ExtIncidence
