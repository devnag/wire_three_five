import Proof.CaseAnalysis.RowsEstimatorDriverSupport

/-! The existing masked reset returns each selected cursor by its recorded
step count even when that cursor began farther right. No head bound is
needed for this exact subtraction endpoint. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open Rewind (recording rewinding config)
open SelectiveReset (finished)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep
