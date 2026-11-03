import Proof.CaseAnalysis.RowsRawRecord
import Proof.CaseAnalysis.RowsProjectionReset

/-! Consumer-first interface for the shared physical row estimator. Only
the selection mask reaches its input; all natural table values are computed
by the existing Williams/count-table machine itself. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorCountMask CompetitorSelectedCount CompetitorMonomialStream
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cells_mask {u : ℕ} (odd : Bool) (f g : Fin u→Fin u→ℕ)
    (select : Fin u→Fin u→Bool) :
    mask (CompetitorSelectedCells.cells odd f select)=mask (CompetitorSelectedCells.cells odd g select) := by
  cases odd <;> simp [CompetitorSelectedCells.cells,CompetitorSelectedCells.rect,mask,
    List.map_flatten,List.map_ofFn,Function.comp_def]

def input (p : Program) (row : EquationRow.Input) (Q : ℕ) (q : ℚ) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  CloseoutRowsRawRecord.input p row Q q denominator
    (CompetitorSelectedCells.cells row.odd (fun _ _=>0) select)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
