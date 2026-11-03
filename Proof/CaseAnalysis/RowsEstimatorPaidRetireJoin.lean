import Proof.CaseAnalysis.RowsEstimatorPaidRetire
import Proof.CaseAnalysis.CloseoutRowsEstimatorPaidWarmRun

/-! Append the actual two-word retirement to the completed estimator run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem restart_state {n s t : ℕ} (c : Configuration n s) (q : Fin t)
    (H : Fin n → ℕ) (A : Fin n → List Bool) (hh : c.heads=H) (ht : c.tapes=A) :
    Composition.restart c q=(⟨q,H,A⟩ : Configuration n t) := by
  apply configuration_ext
  · rfl
  · exact hh
  · exact ht

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
