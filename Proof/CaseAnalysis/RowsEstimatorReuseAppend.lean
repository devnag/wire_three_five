import Proof.CaseAnalysis.RowsEstimatorReuseLayout

/-! Append the estimator's actual padded record in its reusable ambient
bank. The copy changes only the growing scalar stream and its cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def append (p : Program):=RecoveryFocus.machine (copySlots p) AppendCopy.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
