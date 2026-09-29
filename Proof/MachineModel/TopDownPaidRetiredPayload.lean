import Proof.CaseAnalysis.RowsEstimatorPaidOwned
import Proof.MachineModel.TopDownPaidPayload

/-! Apply the existing paid retirement/backing parent before extracting the
already-computed count. No scan of an old false-tail length is introduced.
The scanner input words and next-row reload remain explicit boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidRetiredPayload
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask
open CompetitorCrossScheduler (producer)
open P1Closure RecoveryRootRound
open P1TopDownPaidPayload (estimate port tapes)
attribute [local irreducible] CompetitorCrossScheduler.producer Paid.warmMachine
  Paid.driver Paid.warm Paid.retire Paid.retiredMachine RawRowJoin.machine

noncomputable def fuel (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat) :=
  Paid.warmBudget a row C Q+1+(2*Driver.value a row.d row.p row.cuts.length C+4)

end NearCubicWires.P1TopDownPaidRetiredPayload
