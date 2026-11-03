import Proof.MachineModel.BankCountBranch

/-! Every original raw polynomial, including the empty polynomial, executes
without a supplied row count or either last-index field. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def optionalBudget (B C Q w : ℕ) (ms : List (List ℕ)):=
  max (positiveBudget B C Q w ms) (BankZero.budget B C)+2

end NearCubicWires.ExtIncidence.BankCount
