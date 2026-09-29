import Proof.CaseAnalysis.RowsEstimatorActual

/-! Native cut bytes and their original C driver remain read-only through
the warm estimator, its ordinary rewind, scalar append and private sweep. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmActual
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RepairSource.RecoveryTseitinReadOnly
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmActual
