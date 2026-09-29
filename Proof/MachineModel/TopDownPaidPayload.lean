import Proof.CaseAnalysis.RowsEstimatorPaidOwnedRun
import Proof.MachineModel.ClosureActualRawRow

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidPayload
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask
open CompetitorCrossScheduler (producer)
open P1Closure RecoveryRootRound
attribute [local irreducible] CompetitorCrossScheduler.producer Paid.warmMachine Paid.driver Paid.warm
  RawRowJoin.machine

def estimate : CompetitorValidity.Estimate := ⟨0,0,1⟩
noncomputable def tapes (a : WilliamsAlgorithm) := Paid.tapes a (producer a)
noncomputable def port (a : WilliamsAlgorithm) : Fin (tapes a) :=
  Paid.old a (producer a) (WarmPrepare.spare (producer a))

end NearCubicWires.P1TopDownPaidPayload
