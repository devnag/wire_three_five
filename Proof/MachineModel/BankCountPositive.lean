import Proof.MachineModel.BankCountRaw

/-! One positive raw polynomial now produces its actual incidence table,
count and both binary index fields before calling the original worker. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def positive:=Composition.machine raw counted
def positiveBudget (B C Q w : ℕ) (ms : List (List ℕ)):=
  BankExecution.budget B C ms+1+budget C Q w ms.length

end NearCubicWires.ExtIncidence.BankCount
