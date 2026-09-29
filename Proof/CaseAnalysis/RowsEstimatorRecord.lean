import Proof.CaseAnalysis.RowsEstimatorConsumer
import Proof.CaseAnalysis.RowsEstimatorCoefficientsRequest

/-! Shared SYM/THR consumer: the original row producer and Williams count
table emit the same six-field record with equivalent unreduced coefficient
operands. Only selection-mask bytes, never count values, enter the bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Record
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorCountMask CompetitorSelectedCount
open CompetitorCrossScheduler (producer)
open CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (p : Program) (row : EquationRow.Input) (Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool):=
  Consumer.input p row (Table.input p (EquationRow.request row) Q row.odd q denominator
    (CompetitorSelectedCells.cells row.odd (fun _ _=>0) select))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Record
