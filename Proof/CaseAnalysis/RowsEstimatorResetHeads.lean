import Proof.CaseAnalysis.RowsEstimatorReset

/-! Complete head projections of the already executed private reset,
including its reusable log. The source receipt supplies the native head. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reset
open LocalBitMultitape RepairRepresentation
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reset
