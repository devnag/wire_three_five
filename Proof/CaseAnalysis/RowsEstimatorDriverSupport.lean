import Proof.CaseAnalysis.RowsEstimatorDriverLayout

/-! The actual driver bank needs only a fixed number of D-cell sweeps. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def sweepCount (a : WilliamsAlgorithm) := 20*e a+2002

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
