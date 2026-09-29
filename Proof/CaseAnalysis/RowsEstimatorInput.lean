import Proof.CaseAnalysis.RowsProjectionReset

/-! Consumer-first interface for the shared physical row estimator. Only
the selection mask reaches its input; all natural table values are computed
by the existing Williams/count-table machine itself. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorCountMask CompetitorSelectedCount CompetitorMonomialStream
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
