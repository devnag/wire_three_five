import Proof.Wire_3_5.Lists.ListMachinePrintOuter

/-! # C2p, the interpolation printer (P3:1482-1488)

Realizes the printer of "the explicit monomial lists" by interpolation: for a Boolean function `f` of `L` coordinates
with a point evaluator (`PointEval`, C5's blocks), the machine appends to the output the word
`polyWord (Interp.interpPrint f L d)` of the degree-`≤ d` reduced expansion of `f` (exact whenever some explicit
polynomial of degree `≤ d` computes `f`, `Interp.interpPrint_eval`). The outer loop visits the support bitmaps of at
most `d` ones in increasing order (`Interp.sw_iterate`), the inner loop computes each coefficient (`inner_run`), the
outer pass prints and steps (`outerRest_step`).

The paper quantity is the printed expansion. Results: `outerBody_step`, the loop `outerLoop`, and **`print_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun)
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)

/-! ## The visited supports -/

/-- The support bitmap before pass `k`. -/
def xsAt (L d k : ℕ) : List Bool := (Interp.sw d)^[k] (binary L 0)

theorem xsAt_succ (L d k : ℕ) : xsAt L d (k + 1) = Interp.sw d (xsAt L d k) := by
  simp [xsAt, Function.iterate_succ_apply']

theorem xsAt_length (L d k : ℕ) : (xsAt L d k).length = L := by
  induction k with
  | zero => simp [xsAt]
  | succ k ih => rw [xsAt_succ, sw_length, ih]

/-- The mask tape before pass `k`. -/
def mAt (L d : ℕ) (m0 : List Bool) : ℕ → List Bool
  | 0 => m0
  | k + 1 => Block.ripple Interp.gL Interp.hL false (xsAt L d k) (xsAt L d k)

theorem mAt_length (L d : ℕ) (m0 : List Bool) (hm0 : m0.length = L) (k : ℕ) : (mAt L d m0 k).length = L := by
  cases k with
  | zero => exact hm0
  | succ k => simp [mAt, ripple_length _ _ _ _ _ rfl, xsAt_length]

theorem any_binary (L X : ℕ) (hX : X < 2 ^ L) : (binary L X).any id = decide (X ≠ 0) := by
  by_cases h : X = 0
  · subst h; simp [Interp.binary_zero]
  · have hpos := Interp.pop_binary_pos L X (Nat.pos_of_ne_zero h) hX
    have hmem : true ∈ binary L X := List.count_pos_iff.mp hpos
    rw [decide_eq_true h]
    exact List.any_eq_true.mpr ⟨true, hmem, rfl⟩

theorem xsAt_goods (L d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : k < (Interp.goods L d).length) :
    xsAt L d k = binary L (Interp.goods L d)[k] := (Interp.sw_iterate L d hd).1 k hk

theorem xsAt_end (L d : ℕ) (hd : 1 ≤ d) : xsAt L d (Interp.goods L d).length = binary L 0 :=
  (Interp.sw_iterate L d hd).2

theorem xsAt_pop (L d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : k < (Interp.goods L d).length) :
    Interp.pop (xsAt L d k) ≤ d := by
  rw [xsAt_goods L d hd k hk]
  exact (Interp.mem_goods.mp (List.getElem_mem hk)).2

/-- The outer flag after pass `k`: the next support is nonzero exactly while supports remain. -/
theorem fo_next (L d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : k < (Interp.goods L d).length) :
    (Interp.sw d (xsAt L d k)).any id = decide (k + 1 < (Interp.goods L d).length) := by
  rw [← xsAt_succ]
  rcases Nat.lt_or_eq_of_le (show k + 1 ≤ (Interp.goods L d).length by omega) with h | h
  · rw [xsAt_goods L d hd (k + 1) h, any_binary L _ (Interp.mem_goods.mp (List.getElem_mem h)).1]
    obtain ⟨h0len, h0⟩ := Interp.goods_zero L d
    have := List.pairwise_iff_getElem.mp (Interp.goods_pairwise L d) 0 (k + 1) h0len h (by omega)
    simp [h]; omega
  · rw [h, xsAt_end L d hd]; simp [Interp.binary_zero]

/-! ## One pass of the outer loop -/

noncomputable def setFIM := RecoveryFocus.machine sFI (GF2.CellOp.machine (constOp true))

/-! ## The printer -/

theorem flatMap_range_getD {α β : Type} (l : List α) (x0 : α) (F : α → List β) :
    (List.range l.length).flatMap (fun i => F (l.getD i x0)) = l.flatMap F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.flatMap_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [ih]

theorem filter_map_flatMap {α β : Type} (l : List α) (g : α → List ℕ) (P : List ℕ → Bool) (r : List ℕ → List β) :
    ((l.map g).filter P).flatMap r = l.flatMap fun x => if P (g x) then r (g x) else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : P (g a) = true <;> simp [h, ih]


end NearCubicWires.WireExponent3_5.ListMachine.Print
