import Proof.MachineModel.TopDownPaidReusableCost

/-! Shared row reserves are linear in the already paid driver, with constants
depending only on the fixed Williams program. This supplies capacity bounds;
it does not manufacture the physical unary templates or the source stream. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusableReserves
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open P1TopDownPaidReusable

noncomputable def coefficient (a : WilliamsAlgorithm) : Nat :=
  10*DriverLayout.e a+10*DriverLayout.sweepCount a+1300

end NearCubicWires.P1TopDownPaidReusableReserves
