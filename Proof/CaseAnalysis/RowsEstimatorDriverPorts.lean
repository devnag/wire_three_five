import Proof.CaseAnalysis.RowsEstimatorDriverPower

/-! Routing the original variable-arity unary workers into the driver bank.
Inputs are shared read-only ports; all other worker tapes occupy fresh cells. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverPorts
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {N t k : ℕ} (base : ℕ) (source : Fin k → Fin N) (hB : base+t ≤ N)
    (i : Fin t) : Fin N :=
  if h : i.val<k then source ⟨i.val,h⟩ else ⟨base+i.val,by omega⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverPorts
