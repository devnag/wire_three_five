import Proof.CaseAnalysis.RowsEstimatorMetadataBatch
import Proof.CaseAnalysis.RowsEstimatorActual

/-! The seven literal caller fields of the original Warm estimator bank.
No matrix, count packet, or source stream is supplied by these fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmFields
open LocalBitMultitape MatrixScoreBatch RepairRepresentation CompetitorCountMask
open CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def promote (p : Program) (i : Fin (CompetitorCountTableRecord.tapes p)) : Fin (WholePrefix.tapes p) :=
  (i.natAdd 130).natAdd 70
def slots (p : Program) : Fin 7 → Fin (WholePrefix.tapes p) :=
  ![promote p (((CompetitorCountTable.fresh p 1).castAdd 92).castAdd 27),
    promote p (((CompetitorCountTable.fresh p 3).castAdd 92).castAdd 27),
    promote p ((CompetitorSelectedTable.fresh p 0).castAdd 27),
    promote p ((22 : Fin 27).natAdd (CompetitorSelectedTable.tapes p)),
    promote p ((23 : Fin 27).natAdd (CompetitorSelectedTable.tapes p)),
    promote p ((24 : Fin 27).natAdd (CompetitorSelectedTable.tapes p)),
    promote p ((25 : Fin 27).natAdd (CompetitorSelectedTable.tapes p))]
def words (row : EquationRow.Input) (Q : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) : Fin 7 → List Bool :=
  let b := scalarWidth (EquationRow.request row) Q
  ![List.replicate Q true,[row.odd],
    mask (CompetitorSelectedCells.cells row.odd (fun _ _=>0) select),
    frame (SignedSortKey.binary (CompetitorRationalDecision.width b) q.positive),
    frame (SignedSortKey.binary (CompetitorRationalDecision.width b) q.negative),
    frame (SignedSortKey.binary (CompetitorRationalDecision.width b) q.denominator),
    frame (SignedSortKey.binary b denominator)]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmFields
