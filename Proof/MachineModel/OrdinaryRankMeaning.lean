import Proof.MachineModel.OrdinaryRankCarrier

/-! The exact output of the ordinary label scan contains the original word
followed by its sequential rank. This is the interface to the paper's ranks. -/
namespace NearCubicWires.RepairOrdinary.RankMeaning
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def annotated (width n : ℕ) : List (List Bool) → List (List Bool)
  | [] => []
  | word :: words => (word ++ SignedSortKey.binary width n) :: annotated width (n + 1) words

theorem output_stream (width n : ℕ) (words : List (List Bool)) :
    RankLoop.labels width n words ++ [false] = RankLoop.stream (annotated width n words) := by
  have h : RankLoop.labels width n words = (annotated width n words).flatMap frame := by
    induction words generalizing n with
    | nil => rfl
    | cons word words ih => simp [RankLoop.labels, annotated, ih]
  rw [h]
  rfl

end NearCubicWires.RepairOrdinary.RankMeaning
