import Proof.CaseAnalysis.RowsEstimatorDriverPasses

/-! Physically erase the bounded private driver bank, then return all
scratch heads, using only the two retained D words and their existing log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverClean
open LocalBitMultitape RecoveryExecution RecoveryRootRound StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (t K : ℕ) :=
  Composition.machine (DriverPasses.forward t K) (DriverPasses.back t K)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverClean
