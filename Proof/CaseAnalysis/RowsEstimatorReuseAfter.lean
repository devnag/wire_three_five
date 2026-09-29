import Proof.CaseAnalysis.RowsEstimatorReuseAppend

/-! The exact post-estimator append and sweep. Every private tape is erased
after the six-field record has reached the retained growing scalar stream. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RecoveryRootRound CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def after (p : Program):=Composition.machine (append p) (erase p)
def afterBudget (b D : ℕ):=2*D+40*b+61

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
