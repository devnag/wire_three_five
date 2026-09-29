import Proof.CaseAnalysis.RowsEstimatorPrepare

/-! The actual emitted cut stream and raw retained d,p,odd fields now reach
EquationRowRaw's exact framed source. No G or length driver is input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Framed
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 59) : Fin 68:=
  if h:j.val<55 then ⟨j.val,by omega⟩ else ⟨j.val+9,by omega⟩


end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Framed
