import Codec.ParityW
import Worker.Meaning

/-!
# W3dl, piece 2: exact entries (the near-cubic-gates paper)

The exact terms of eq:gadget-pair-identity (a pure parity, two parities, a repeated circuit) need no counter call:
their raw interval is `(parityMean S, 0)` or `(0, 0)` (`Worker.Guess.intervalOf`). `exactEntryW o OP F H` appends the
term's entry `marks (bitWord f ++ outputWord (p, 0))` to the I-stream, with `f = [F ≠ 0]` and `p = 1/2` iff `H ≠ 0`.
Value lemmas: `parityMean` as the `H` test, `symmDiff` nonempty iff the supports differ, canonical lists.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.Platform
open NearCubicGates.Close.Joins (bitWord outputWord)

variable {ns nr : ℕ}

/-- The raw mean of an exact entry: `1/2` when the flag is set. -/
def halfIf (h : Bool) : ℚ := if h then 1 / 2 else 0


/-! ## Value lemmas -/

open NearCubicGates.Close.Gadget in
theorem canonList_ne_nil_iff {q : ℕ} (S : Finset (Fin q)) : (canonList S).map Fin.val ≠ [] ↔ S.Nonempty := by
  rw [Ne, List.map_eq_nil_iff]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨i, (mem_canonList S i).1 hi⟩
  · rintro ⟨i, hi⟩ h
    have := (mem_canonList S i).2 hi
    rw [h] at this; simp at this

open NearCubicGates.Close.Gadget in
theorem canonList_inj {q : ℕ} (S T : Finset (Fin q)) : (canonList S).map Fin.val = (canonList T).map Fin.val ↔ S = T := by
  constructor
  · intro h
    have h' : canonList S = canonList T := List.map_injective_iff.2 Fin.val_injective h
    ext i; rw [← mem_canonList S i, ← mem_canonList T i, h']
  · rintro rfl; rfl

theorem parityMean_halfIf {q : ℕ} (S : Finset (Fin q)) :
    Worker.parityMean S = halfIf (decide S.Nonempty) := by
  unfold Worker.parityMean halfIf; by_cases h : S.Nonempty <;> simp [h]

theorem symmDiff_nonempty_iff {α : Type} [DecidableEq α] (S T : Finset α) : (symmDiff S T).Nonempty ↔ S ≠ T := by
  rw [Finset.nonempty_iff_ne_empty, Ne, Ne, ← Finset.bot_eq_empty, symmDiff_eq_bot]

end NearCubicGates.Close.WorkerArith
