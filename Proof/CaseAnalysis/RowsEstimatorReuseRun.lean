import Proof.CaseAnalysis.RowsEstimatorResetHeads
import Proof.CaseAnalysis.RowsEstimatorReuseAfter

/-! The original physical estimator, private reset, six-field append and
owned scratch sweep, composed in one finite program. D and every row input
remain physically supplied by the enclosing metadata producer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


def budget (fuel b D : ℕ):=(2*fuel+2)+1+afterBudget b D


end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
