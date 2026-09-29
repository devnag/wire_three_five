import Proof.MachineModel.OrdinaryKeyLoop

/-! The keyed scan consumes the literal existing annotator encoding, with
sequential ranks and the preserved score/id words. -/
namespace NearCubicWires.RepairOrdinary.KeyLoop
open LocalBitMultitape SignedSortKey
open KeyCell (config)
open RecordController (test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def indexed (n : ℕ) : List (ℤ × ℕ) → List Record
  | [] => []
  | (score, id) :: entries => (score, id, n) :: indexed (n + 1) entries
def words (S K : ℕ) (entries : List (ℤ × ℕ)) : List (List Bool) :=
  entries.map (fun e => RadixSemantics.word (encode S K e.1 e.2))

@[simp] theorem indexed_length (n : ℕ) (entries : List (ℤ × ℕ)) : (indexed n entries).length = entries.length := by
  induction entries generalizing n with
  | nil => rfl
  | cons e entries ih => rcases e with ⟨score, id⟩; simp [indexed, ih]

theorem indexed_fields (S K n : ℕ) (entries : List (ℤ × ℕ)) :
    fields S K (indexed n entries) = (RankMeaning.annotated (K + S + 1) n (words S K entries)).flatMap frame := by
  induction entries generalizing n with
  | nil => rfl
  | cons e entries ih =>
    rcases e with ⟨score, id⟩
    simpa [fields, indexed, words, word, RankMeaning.annotated] using
      congrArg (fun tail => frame (RadixSemantics.word (encode S K score id) ++ binary (K + S + 1) n) ++ tail) (ih (n + 1))

theorem indexed_stream (S K n : ℕ) (entries : List (ℤ × ℕ)) :
    stream S K (indexed n entries) = RankLoop.stream (RankMeaning.annotated (K + S + 1) n (words S K entries)) := by
  rw [stream, indexed_fields]
  rfl

theorem indexed_fits (W n : ℕ) (entries : List (ℤ × ℕ)) (hn : n + entries.length < 2 ^ W) :
    ∀ r ∈ indexed n entries, r.2.2 < 2 ^ W := by
  induction entries generalizing n with
  | nil => simp [indexed]
  | cons e entries ih =>
    rcases e with ⟨score, id⟩
    intro r hm
    simp only [indexed, List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp only [List.length_cons] at hn
      exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hn
    · exact ih (n + 1) (by simp only [List.length_cons] at hn; omega) r hm

end NearCubicWires.RepairOrdinary.KeyLoop
