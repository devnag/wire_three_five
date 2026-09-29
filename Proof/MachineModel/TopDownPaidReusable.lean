import Proof.MachineModel.ClosureBinaryRequest
import Proof.MachineModel.TopDownPaidReloadCore
import Proof.MachineModel.TopDownPaidReusableBody

/-! The complete source-stream → scanner → actual paid count → retirement →
raw append → reusable false bank transaction. Only the original framed row
source and shared physical capacity templates remain upstream duties. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open CompetitorCrossScheduler (producer)
open P1TopDownPaidPayload (estimate port tapes)
attribute [local irreducible] CompetitorCrossScheduler.producer Paid.warmMachine
  Paid.driver Paid.warm Paid.retire Paid.retiredMachine RawRowJoin.machine
  P1TopDownPaidReloadCore.rawMachine P1TopDownPaidReusableBody.machine

noncomputable def machine (a : WilliamsAlgorithm) :=
  P1TopDownPaidReusableBody.machine (P1TopDownPaidReloadCore.rawMachine a)
noncomputable def word (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  P1TopDownPaidReusableBody.word (P1TopDownPaidReloadCore.input a row C Q select)
noncomputable def heads (a : WilliamsAlgorithm) := P1TopDownPaidReusableBody.heads (tapes a)
noncomputable def bank (a : WilliamsAlgorithm) (source : List Bool) (S R B : Nat) (out : List Bool) :=
  P1TopDownPaidReusableBody.bank (fun _ : Fin (tapes a)=>List.replicate S false) source S R B out

end NearCubicWires.P1TopDownPaidReusable
