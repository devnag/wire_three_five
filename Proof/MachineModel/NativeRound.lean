import Proof.CaseAnalysis.RowsEstimatorBankCycle
import Proof.MachineModel.NativeFanoutReusable
import Proof.MachineModel.NativeInitializedPorts

/-! The actual polynomial worker and one retained-metadata reload return
the reusable entry bank, ready for the next original raw polynomial. -/
namespace NearCubicWires.ExtIncidence.NativeRound
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine EstimatorBankCycle.machine NativeFanoutLayout.machine
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) (ms : List (List ℕ)):=
  EstimatorBankCycle.budget gs Q w ms+1+(2*NativeMeasured.capacity gs Q w+4)

end NearCubicWires.ExtIncidence.NativeRound
