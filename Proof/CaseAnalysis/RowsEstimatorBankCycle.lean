import Proof.MachineModel.BankCountOptional
import Proof.MachineModel.NativeBankPosition

/-! One actual reusable native call preserves every ambient port outside its bank. -/
namespace NearCubicWires.ExtIncidence.EstimatorBankCycle
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def last:=RecoveryFocus.machine bank BankCount.optional
noncomputable def machine:=Composition.machine NativeBankPosition.machine last
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) (ms : List (List ℕ)):=
  1+1+BankCount.optionalBudget gs.length (NativeMeasured.capacity gs Q w) Q w ms

end NearCubicWires.ExtIncidence.EstimatorBankCycle
