import Proof.Wire_3_5.Primitive.SeedFix.SeedFixJLink
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixFetch

/-! # (c′) (B): the degenerate call's padded batch (mode-generic)

"For each candidate child prefix, print its signed equation expression" (P3:3034-3035) through `alg:compiler`
(P3:1886-1906), whose precondition needs at least one factor per term (`1 ≤ m`). At a call with no rows (`R = 0`: no
carriers and `a = 0`, which `Call` allows), every entry is empty and every printed term has no factor. The SYM/THR/HASH
stage then runs on the PADDED batch: one constant-`1` row appended to every entry (`R′ = 1`, one factor `1` per term,
`m = 8`); the row evaluates to `1`, so the objective, the greedy sample and the seed word are unchanged (the side).

* `constRow` (the term `1·(1)`: coefficient `1`, one factor, the constant polynomial `[[]]`), `padEnts`, `padBatch`,
  **`chunk_pad`** (the padded batch's chunk at `R′ = 1` is the padded entries of the `R = 0` chunk), `blockWord_empty`,
  `blockWord_pad` (the two tape words).

Paper quantity of the main type: the degenerate call's batch, padded by the constant factor `1`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Pad
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix

/-- **The constant row**: one term, coefficient `1`, one factor, the constant polynomial `1 = [[]]` (one empty
monomial). -/
def constRow : SExpr := [((1 : ℤ), [[[]]])]

/-- **The padded entries**: the constant row appended to every entry. -/
def padEnts (ents : List (List SExpr)) : List (List SExpr) := ents.map fun rs => rs ++ [constRow]

/-- **The padded batch** of a call with `n_T` states and `N` columns (`R′ = 1`): the constant row per entry. -/
def padBatch (N nT : ℕ) : List SExpr := List.replicate (nT * N ^ 2) constRow

theorem chunk_zero (N nT : ℕ) (batch : List SExpr) :
    JLink.chunk N nT 0 batch = List.replicate (nT * N ^ 2) [] := by
  simp [JLink.chunk, List.map_const']

/-- **The padded batch's chunk at `R′ = 1` is the padded entries of the `R = 0` chunk.** -/
theorem chunk_pad (N nT : ℕ) (batch : List SExpr) :
    JLink.chunk N nT 1 (padBatch N nT) = padEnts (JLink.chunk N nT 0 batch) := by
  rw [chunk_zero]
  unfold JLink.chunk padEnts padBatch
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, List.nil_append, List.range_one,
      List.map_cons, List.map_nil, Nat.mul_one, Nat.add_zero]
    have hi : i < nT * N ^ 2 := by simpa using h1
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_replicate]

/-- The tape word of `E` empty entries. -/
theorem blockWord_empty (E : ℕ) :
    blockWord (List.replicate E []) = (List.replicate E [true, false]).flatten ++ [false] := by
  unfold blockWord
  congr 1
  induction E with
  | zero => rfl
  | succ E ih => rw [List.replicate_succ, List.flatMap_cons, List.replicate_succ, List.flatten_cons, ih]; rfl

/-- The tape word of `E` padded entries. -/
theorem blockWord_pad (E : ℕ) :
    blockWord (padEnts (List.replicate E [])) =
      (List.replicate E (true :: (rowRec constRow ++ [false]))).flatten ++ [false] := by
  unfold blockWord padEnts
  rw [List.map_replicate]
  congr 1
  induction E with
  | zero => rfl
  | succ E ih => rw [List.replicate_succ, List.flatMap_cons, List.replicate_succ, List.flatten_cons, ih]; rfl

end NearCubicWires.WireExponent3_5.PrimT.C4Pad
