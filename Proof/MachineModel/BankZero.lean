import Proof.MachineModel.BankConsumer

/-! The empty raw stream has no polynomial call. Its actual incidence run and
paid clear return the same native bank; no unrelated metadata is required. -/
namespace NearCubicWires.ExtIncidence.BankZero
open LocalBitMultitape RepairOrdinary BankConsumer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def clearing:=RecoveryFocus.machine old CloseoutRowsBankClear.machine
noncomputable def machine:=Composition.machine BankExecution.machine clearing
def budget (B C : ℕ):=BankExecution.budget B C []+1+CloseoutRowsBankClear.budget C

end NearCubicWires.ExtIncidence.BankZero
