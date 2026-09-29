import Proof.CaseAnalysis.RowsEstimatorPaidLayout

/-! The concrete driver run has no supplier-Ready assumption. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def driver (a : WilliamsAlgorithm):=RecoveryFocus.machine (slots a (producer a)) (ScannedClean.machine a)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
