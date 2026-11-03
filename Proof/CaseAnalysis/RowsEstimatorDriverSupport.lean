import Proof.CaseAnalysis.RowsEstimatorDriverRuntime

/-! The actual driver bank needs only a fixed number of D-cell sweeps. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def sweepCount (a : WilliamsAlgorithm) := 20*e a+2002

theorem value_positive (a : WilliamsAlgorithm) (d p G C : ℕ) : 1 ≤ Driver.value a d p G C := by
  unfold Driver.value
  omega

theorem fuel_support (a : WilliamsAlgorithm) (d p G C : ℕ) :
    budget a d p G C+1 ≤ sweepCount a*Driver.value a d p G C := by
  have hb := budget_linear a d p G C
  have hp := value_positive a d p G C
  have hmul := Nat.mul_le_mul_left (10*e a+1000) (show Driver.value a d p G C+1 ≤ 2*Driver.value a d p G C by omega)
  unfold sweepCount
  nlinarith only [hb,hp,hmul]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
