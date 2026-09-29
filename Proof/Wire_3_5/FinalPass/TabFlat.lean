import Proof.Wire_3_5.FinalPass.TabUnit

/-! # S4 (f1), the tables writer, part 8: the units' emissions are the seeds' tables (P3:2036-2101)

**`tabEmit_flat`**: for every loop bound `b ≥ 2·|seeds|`, the units' emissions `(range b).flatMap (tabEmit FP L₀ L₁)`
are every seed's two framed tables in the enumeration's order (`Enum.gapSeedEquiv`), `tabWord FP L₀ L₁`; the units
past the seeds emit nothing.

Paper quantity of the main type: the seeds' filter tables `tableWord (filterTable FP e Lₖ)` of every seed `e` and
carrier `k` (P3:2036-2101), in one word. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters

/-- **The seeds' tables**: per seed (in the enumeration's order) its two framed tables. -/
def tabWord (FP : GapParams) (L0 L1 : ℕ) : List Bool :=
  ((List.finRange (Fintype.card (GapSeed FP))).map (Enum.gapSeedEquiv FP).symm).flatMap fun e =>
    frame (tableWord (filterTable FP e L0)) ++ frame (tableWord (filterTable FP e L1))

theorem range_flatMap_finRange (n : ℕ) (G : ℕ → List Bool) :
    (List.range n).flatMap G = (List.finRange n).flatMap fun i => G i.val := by
  have h : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  rw [← h, List.flatMap_map]

theorem range_pairs (f : ℕ → List Bool) (k : ℕ) :
    (List.range (2 * k)).flatMap f = (List.range k).flatMap fun i => f (2 * i) ++ f (2 * i + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.range_succ, List.range_succ, List.flatMap_append,
      List.flatMap_append, ih, List.range_succ, List.flatMap_append]
    simp [List.append_assoc]

theorem tabEmit_flat (FP : GapParams) (L0 L1 b : ℕ) (hb : 2 * Fintype.card (GapSeed FP) ≤ b) :
    (List.range b).flatMap (tabEmit FP L0 L1) = tabWord FP L0 L1 := by
  set nE := Fintype.card (GapSeed FP) with hnE
  have hsplit : List.range b = List.range (2 * nE) ++ (List.range (b - 2 * nE)).map (2 * nE + ·) := by
    rw [← List.range_add]
    congr 1
    omega
  have htail : ((List.range (b - 2 * nE)).map (2 * nE + ·)).flatMap (tabEmit FP L0 L1) = [] := by
    rw [List.flatMap_map]
    apply List.flatMap_eq_nil_iff.mpr
    intro i _
    unfold tabEmit
    rw [dif_neg (by omega)]
  rw [hsplit, List.flatMap_append, htail, List.append_nil, range_pairs, range_flatMap_finRange, tabWord,
    List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  have h0 : (2 * i.val) / 2 < nE := by have := i.isLt; omega
  have h1 : (2 * i.val + 1) / 2 < nE := by have := i.isLt; omega
  unfold tabEmit
  rw [dif_pos h0, dif_pos h1]
  have e0 : (⟨2 * i.val / 2, h0⟩ : Fin nE) = i := Fin.ext (by simp)
  have e1 : (⟨(2 * i.val + 1) / 2, h1⟩ : Fin nE) = i := Fin.ext (by simp; omega)
  rw [e0, e1]
  simp

end NearCubicWires.WireExponent3_5.FinalPass.TabW
