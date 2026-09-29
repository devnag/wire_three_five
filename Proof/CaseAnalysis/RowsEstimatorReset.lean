import Proof.Amplification.RecoveryTseitinReadOnly
import Proof.CaseAnalysis.RowsEstimatorAppendCopy

/-! Reuse the estimator's private bank with physically supplied D backing.
The native cut tape is external and enters at a nonzero append cursor, so
it is deliberately excluded from the zero-head reset and support claims.
D is separate from native C: the initial paid C rewind itself costs 2C+2. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reset
open LocalBitMultitape RepairRepresentation
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reset
