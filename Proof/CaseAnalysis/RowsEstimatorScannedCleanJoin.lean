import Proof.CaseAnalysis.RowsEstimatorScannedCleanPorts

/-! Symbolic finite-control join of the actual driver and cleanup donors.
Keeping callee controls abstract prevents unfolding thousands of fixed passes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def cleanBudget (a : WilliamsAlgorithm) (D : ℕ) :=
  2*D+6+1+(DriverLayout.sweepCount a*(5*D+10)+1)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ) :=
  DriverLayout.budget a row.d row.p row.cuts.length C+1+
    cleanBudget a (Driver.value a row.d row.p row.cuts.length C)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
