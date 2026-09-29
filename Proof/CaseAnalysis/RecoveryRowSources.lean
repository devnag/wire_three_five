import Proof.Amplification.RecoveryProjectionRowsRewind
import Proof.CaseAnalysis.RecoveryRowBudget

/-! The existing source normalizer supplies the exact original compact
clauses and their actual count, once for every randomness row. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRow
open LocalBitMultitape SourceInterfaces RepairRepresentation
open RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clause_word {q : ℕ} (clause : Fin 3→Literal q) :
    RecoveryBoundedClauseRun.word clause=QueryBytes.framedCodes (clauseCodes clause) := by
  simp [RecoveryBoundedClauseRun.word,QueryBytes.framedCodes,clauseCodes,List.ofFn_succ,List.append_assoc]

theorem clauses_word {q : ℕ} (clauses : List (Fin 3→Literal q)) :
    RecoveryBoundedClauseList.word clauses=(clauses.map clauseCodes).flatMap QueryBytes.framedCodes := by
  simp only [RecoveryBoundedClauseList.word,List.flatMap_map]
  apply congrArg (fun f=>clauses.flatMap f)
  funext clause
  exact clause_word clause

theorem original_clause_source (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : ℕ} (input : BitInput n) (randomness : BitInput R) :
    RecoveryBoundedClauseList.word ((compactProjectionPCP (p.normalized R Q hr hq)).decision input randomness).clauses=
      DedupBytes.fields p := by
  rw [clauses_word,Codec.decision_codes]
  rfl

theorem original_clause_count (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : ℕ} (input : BitInput n) (randomness : BitInput R) :
    ((compactProjectionPCP (p.normalized R Q hr hq)).decision input randomness).clauses.length=(Codec.clauses p).length := by
  have h:=congrArg List.length (Codec.decision_codes p R Q hr hq input randomness)
  simpa only [List.length_map] using h

end NearCubicWires.RepairOrdinary.RecoveryBoundedRow
