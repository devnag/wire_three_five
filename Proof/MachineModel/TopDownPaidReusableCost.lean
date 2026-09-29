import Proof.MachineModel.TopDownPaidReusableFamily

/-! The shared capacity gives a uniform linear transaction budget. The
Williams table cost occurs only inside S, never multiplied by itself. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open P1TopDownPaidPayload (tapes)
attribute [local irreducible] CompetitorCrossScheduler.producer machine

end NearCubicWires.P1TopDownPaidReusable
