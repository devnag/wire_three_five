import Proof.Wire_3_5.Selection.GateKeyMath

/-! # C1.4: the joins' arithmetic without overflow (P3:1345-1358)

Paper: "Sum its exact count" (P3:1358). C1.4's math gives a gate's row count as
`(Yh + 2·Σ_ℓ K1_ℓ) − (Yl + 2·Σ_ℓ K3_ℓ)` (`gateJoin_tab`), whose two sides can each reach `(V + 1)·|L|·|R|`. The machine
keeps every word below `2|L||R|`: it subtracts level by level, `ACC := Yh − Yl`, then `ACC := ACC − e_ℓ − e_ℓ` with
`e_ℓ = K3_ℓ − K1_ℓ` (every subtraction truncated, `ℕ`). This module proves the two agree (**`levels_fold`**), from
the pointwise order of the level queries (**`K1_le_K3`**: `lvlK1 ≤ lvlK3` entry by entry, so `J<(K2; K1) ≤ J<(K2; K3)`),
and bounds every join by its pair count (`joinLt_le`). Paper quantity: a gate's row count, as the machine accumulates
it. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.WireExponent3_5.SelectionMachine.Math

/-- The machine's accumulation over the levels `0, …, m − 1`. -/
def accFold (yh yl : ℕ) (e : ℕ → ℕ) (m : ℕ) : ℕ := (List.range m).foldl (fun a ℓ => a - e ℓ - e ℓ) (yh - yl)

theorem accFold_succ (yh yl : ℕ) (e : ℕ → ℕ) (m : ℕ) :
    accFold yh yl e (m + 1) = accFold yh yl e m - e m - e m := by
  unfold accFold; rw [List.range_succ, List.foldl_append]; rfl

/-- **The level-by-level subtraction is the joins' difference.** -/
theorem levels_fold (yh yl : ℕ) (k1 k3 : ℕ → ℕ) (hk : ∀ ℓ, k1 ℓ ≤ k3 ℓ) : ∀ m,
    (yh + 2 * ((List.range m).map k1).sum) - (yl + 2 * ((List.range m).map k3).sum) =
      accFold yh yl (fun ℓ => k3 ℓ - k1 ℓ) m
  | 0 => by simp [accFold]
  | m + 1 => by
    rw [accFold_succ, ← levels_fold yh yl k1 k3 hk m, List.range_succ, List.map_append, List.map_append,
      List.sum_append, List.sum_append]
    have := hk m
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    omega

/-- A `<`-join is monotone in its queries, entry by entry. -/
theorem joinLt_mono {α : Type} (A : List ℕ) (T : List α) (f f' : α → ℕ) (h : ∀ d ∈ T, f d ≤ f' d) :
    joinLt A (T.map f) ≤ joinLt A (T.map f') := by
  unfold joinLt
  rw [List.map_map, List.map_map]
  apply List.sum_le_sum
  intro i hi
  simp only [Function.comp]
  apply List.countP_mono_left
  intro a _ ha
  simp only [decide_eq_true_eq] at ha ⊢
  exact lt_of_lt_of_le ha (h _ hi)

/-- **The level-`ℓ` queries are ordered**: `lvlK1 ≤ lvlK3` entry by entry, for keys below `2^W`. -/
theorem K1_le_K3 (W ℓ : ℕ) (D I : List (ℕ × ℕ)) (hI : ∀ J ∈ I, J.1 < 2 ^ W) :
    joinLt (lvlK2 W ℓ D) (lvlK1 W ℓ I) ≤ joinLt (lvlK2 W ℓ D) (lvlK3 W ℓ I) := by
  unfold lvlK1 lvlK3
  apply joinLt_mono
  intro J hJ
  split_ifs
  · have := hI J hJ; nlinarith
  · exact le_rfl

/-- **A join counts at most every pair.** -/
theorem joinLt_le (A B : List ℕ) : joinLt A B ≤ A.length * B.length := by
  unfold joinLt
  induction B with
  | nil => simp
  | cons b B ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := List.countP_le_length (p := fun a => decide (a < b)) (l := A)
    nlinarith

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
