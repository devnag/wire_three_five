import Proof.CaseAnalysis.RowsEstimatorWhole

/-! The original complete estimator also returns its external native source
head and native capacity, needed by the enclosing fixed-row loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WholeRetained
open LocalBitMultitape MatrixScoreBatch RepairRepresentation Whole
open CompetitorSelectedCount CompetitorCountMask
open CompetitorCrossScheduler (producer)
open CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WholeRetained
