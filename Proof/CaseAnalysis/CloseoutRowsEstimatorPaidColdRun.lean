import Proof.CaseAnalysis.CloseoutRowsEstimatorPaidWarmRun
import Proof.CaseAnalysis.RowsEstimatorPaidRetire

/-! The original native append input reaches the scalar consumer through
the mandatory scan, actual D allocation, paid copies, Warm and retirement. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def retiredMachine (a : WilliamsAlgorithm):=Composition.machine (warmMachine a) (retire a (producer a))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
