import Proof.MachineModel.BankCountNative
import Proof.CaseAnalysis.RowsProjectionReset
import Proof.MachineModel.BankMetadata
import Proof.MachineModel.CountIndex

/-! Execute count metadata and the original polynomial worker on the same
actual incidence table. No last-index word is supplied to this consumer. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def consumer:=RecoveryFocus.machine old CloseoutRowsBankPolynomial.machine
noncomputable def counted:=Composition.machine machine consumer
def budget (C Q w M : ℕ):=CountIndexClean.budget C w M+1+CloseoutRowsBankPolynomial.budget Q C

end NearCubicWires.ExtIncidence.BankCount
