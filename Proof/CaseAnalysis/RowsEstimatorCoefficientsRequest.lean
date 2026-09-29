import Proof.CaseAnalysis.RowsEstimatorCoefficientsLoop
import Proof.Hierarchy.CompetitorCountTableRecord

/-! The unchanged selected-count and actual count-table programs append
unreduced coefficient fields. Their counts still come from the original
physical table and selected SUM, never from a supplied count numeral. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairRepresentation MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
open CompetitorRationalDecision
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace CountRequest
open CompetitorCountRecordRequest

def extra (b : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ) (i : Fin 27) : List Bool :=
  match i.val with
    | 22 => frame (binary (width b) (q.positive))
    | 23 => frame (binary (width b) (q.negative))
    | 24 => frame (binary (width b) q.denominator)
    | 25 => frame (binary b denominator)
    | _ => []

end CountRequest

namespace Table
open CompetitorCountTableRecord

def input (p : Program) (r : Request) (Q : ℕ) (odd : Bool)
    (q : CompetitorValidity.Estimate) (denominator : ℕ) (xs : List (Bool × ℕ)) :=
  Fin.addCases (m := CompetitorSelectedTable.tapes p) (n := 27) (motive := fun _ => List Bool)
    (CompetitorSelectedTable.extend p xs (CompetitorCountTable.input p r Q odd))
    (CountRequest.extra (scalarWidth r Q) q denominator)

end Table
end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
