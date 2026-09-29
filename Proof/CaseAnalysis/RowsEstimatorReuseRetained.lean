import Proof.CaseAnalysis.CaseTwoAddressRetention
import Proof.CaseAnalysis.RowsEstimatorReuseRun

/-! The same enclosing reusable program preserves both externally owned
native tapes through the original estimator, masked reset, append and sweep. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RepairSource.RecoveryTseitinReadOnly
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
