import Proof.CaseAnalysis.RowsEstimatorDriverIterate

/-! Fixed D-driven cleanup passes, with actual receipts at every boundary. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverPasses
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def forward (t K : ℕ) := DriverIterate.machine (DriverSweep.round t) K
noncomputable def back (t K : ℕ) := DriverIterate.machine (DriverReturnMany.machine t) K

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverPasses
