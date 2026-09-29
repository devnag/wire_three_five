import Proof.PCP.ProjectionNormalizationReuse

namespace NearCubicWires.RepairSource.ProjectionNormalization.SuffixScan
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Clause := Fin 3 → List Bool
def stream (rows : List Clause) := (rows.map ClauseEquality.stream).flatten
noncomputable def endEq (left : Clause) : List Clause → Bool → Bool
  | [],old => old
  | right::rows,_ => endEq left rows (decide (left=right))
noncomputable def seen (left : Clause) (rows : List Clause) (old : Bool) := old||decide (left∈rows)

@[simp] theorem stream_nil : stream []=[] := rfl
@[simp] theorem stream_cons (row : Clause) (rows : List Clause) :
    stream (row::rows)=ClauseEquality.stream row++stream rows := rfl

theorem seen_cons (left right : Clause) (rows : List Clause) (old : Bool) :
    seen left rows (old||decide (left=right))=seen left (right::rows) old := by
  classical
  simp [seen,List.mem_cons,Bool.or_assoc]

end NearCubicWires.RepairSource.ProjectionNormalization.SuffixScan
