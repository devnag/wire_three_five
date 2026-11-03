import Proof.MachineModel.Machine
import Proof.CaseAnalysis.RowsSourceDigits
import Proof.CaseAnalysis.RowsBankPolynomial
import Proof.CaseAnalysis.RowsFamilyLoop
import Proof.CaseAnalysis.RowsSourceMeaning

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

/-- The canonical monomial occurrence list of `P`, as child indices. Repeated
variables inside one monomial stay repeated here and collapse in the row. -/
noncomputable def occurrences {B : ℕ} (P : MvPolynomial (Fin B) (ZMod 2)) : List (List ℕ) :=
  (polynomialMonomialOccurrences P).map (List.map Fin.val)

end NearCubicWires.ExtIncidence
