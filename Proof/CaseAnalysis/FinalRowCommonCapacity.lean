import Proof.CaseAnalysis.FinalRowFrameJoin

/-! The actual warm row at one caller-produced capacity shared by every label.
The extra inequality only enlarges its paid rewind/reset capacity. It neither
allocates the entry bank nor changes the estimator, table, or denominator.
Paper A.3 and C.10: row preparation is charged once per external label. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10RowCommonCapacity
open LocalBitMultitape RepairRepresentation RepairOrdinary
open RepairOrdinary.MatrixScoreBatch RepairOrdinary.CloseoutRowsEstimator
open RepairOrdinary.CompetitorSelectedCount RepairOrdinary.CompetitorCountMask
open RepairOrdinary.CloseoutRowsEstimatorCoefficients
open RepairOrdinary.CompetitorCrossScheduler (producer)
open RepairOrdinary.C10RowFrameJoin
open ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairSource.CloseoutFinal.C10RowCommonCapacity
