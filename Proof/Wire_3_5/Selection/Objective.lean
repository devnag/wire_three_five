import Proof.Wire_3_5.Selection.MathPlan

/-! # C1.1 R2: the objective compare by exact rational keys (P3:1357-1360)

Paper: "Sum its exact count with the rational population weights, over gates and rows. [...] Select a minimum
objective" (P3:1357-1360). The machine never forms the objective `E_x Σ_X p_X R_X(x)` itself: it accumulates the
numerator `Σ_X p_X · T_X` as an unnormalized fraction (`ratAcc`, adding `(a/b)·T` for `p_X = a/b`) and compares two
cosets by cross-multiplication (`ratLt`). Proves **`r2Objective : R2Objective`**: for nonnegative weights,
`selObjective R l < selObjective R l' ↔ ratLt (objKey R h l) (objKey R h l')`, from `ratAcc_val` (the accumulated
fraction's value), `ratLt_iff` (cross-multiplication, positive denominators), `gateRows_default` (an index outside
the gate list reads the zero gate, whose row counts vanish) and `selObjective_eq_key`
(`selObjective R l = ratVal (objKey R h l) / 2^n`). Paper quantity: the objective of a coset. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Math.Objective
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Math

/-! ## The accumulated fraction -/

theorem ratAcc_foldl (xs : List (ℕ × ℕ × ℕ)) (hb : ∀ x ∈ xs, 0 < x.2.1) :
    ∀ acc : RegRat, 0 < acc.2 →
      0 < (xs.foldl ratAccStep acc).2 ∧
        ratVal (xs.foldl ratAccStep acc) = ratVal acc + (xs.map fun x => (x.1 : ℚ) / x.2.1 * x.2.2).sum := by
  induction xs with
  | nil => intro acc h; simp [h]
  | cons x xs ih =>
    intro acc hacc
    have hx : 0 < x.2.1 := hb x List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)) (ratAccStep acc x)
      (Nat.mul_pos hacc hx)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, List.map_cons, List.sum_cons]
    have e : ratVal (ratAccStep acc x) = ratVal acc + (x.1 : ℚ) / x.2.1 * x.2.2 := by
      unfold ratVal ratAccStep
      have hD : (acc.2 : ℚ) ≠ 0 := by exact_mod_cast hacc.ne'
      have hB : (x.2.1 : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
      push_cast
      field_simp
    rw [e, add_assoc]

/-- **The accumulated fraction's value**: `ratAcc xs = Σ (a/b)·T` with a positive denominator. -/
theorem ratAcc_val (xs : List (ℕ × ℕ × ℕ)) (hb : ∀ x ∈ xs, 0 < x.2.1) :
    0 < (ratAcc xs).2 ∧ ratVal (ratAcc xs) = (xs.map fun x => (x.1 : ℚ) / x.2.1 * x.2.2).sum := by
  obtain ⟨h1, h2⟩ := ratAcc_foldl xs hb (0, 1) Nat.one_pos
  refine ⟨h1, ?_⟩
  unfold ratAcc
  rw [h2]
  simp [ratVal]

/-- **Cross-multiplication** decides the strict order of two fractions with positive denominators. -/
theorem ratLt_iff (x y : RegRat) (hx : 0 < x.2) (hy : 0 < y.2) : ratLt x y = true ↔ ratVal x < ratVal y := by
  unfold ratLt ratVal
  rw [decide_eq_true_iff, div_lt_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  exact_mod_cast Iff.rfl

/-! ## The zero gate and the objective -/

/-- The zero gate (the default of `getD`) has no nonzero mixed residual, so its row counts vanish. -/
theorem gateRows_default (R : SelectionReq) (h : ParamsOk R) (σ : (starParamsOf R h).Translation) :
    gateRows (starParamsOf R h) σ (gateOf (⟨fun _ => 0, 0⟩ : IntGate R.n)) = 0 := by
  unfold gateRows
  apply Finset.sum_eq_zero; intro u _
  apply Finset.sum_eq_zero; intro v _
  rw [StarParams.rowCount_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c _ hc
  apply hc.2
  simp [mixedDifference, gateOf, NormalizedThresholdGate.eval, bitZ]

theorem gateRows_getD (R : SelectionReq) (h : ParamsOk R) (σ : (starParamsOf R h).Translation) (i : ℕ) :
    gateRows (starParamsOf R h) σ (gateOf (R.gates.getD i ⟨fun _ => 0, 0⟩)) =
      if hi : i < R.gates.length then gateRows (starParamsOf R h) σ (gateOf R.gates[i]) else 0 := by
  split_ifs with hi
  · rw [List.getD_eq_getElem _ _ hi]
  · rw [List.getD_eq_default _ _ (by omega)]
    exact gateRows_default R h σ

/-- **The objective is the key's value over `2^n`** (nonnegative weights). -/
theorem selObjective_eq_key (R : SelectionReq) (h : ParamsOk R) (hp : ∀ X ∈ R.pops, 0 ≤ X.2) (l : List ℕ) :
    selObjective R l = ratVal (objKey R h l) / 2 ^ R.n := by
  rw [selObjective_eq R h l]
  unfold objKey
  rw [(ratAcc_val _ (by
    intro x hx
    obtain ⟨X, _, rfl⟩ := List.mem_map.mp hx
    exact X.2.den_pos)).2]
  unfold StarParams.starObjectiveRef popsOf
  congr 1
  unfold starParamsOf
  rw [List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro X hX
  simp only [Function.comp_apply]
  have hnum : ((X.2.num.toNat : ℕ) : ℚ) = (X.2.num : ℚ) := by
    have : 0 ≤ X.2.num := Rat.num_nonneg.mpr (hp X hX)
    exact_mod_cast Int.toNat_of_nonneg this
  rw [hnum]
  have hq : (X.2.num : ℚ) / (X.2.den : ℚ) = X.2 := Rat.num_div_den X.2
  rw [hq]
  congr 1
  unfold popRows
  push_cast
  rw [List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  have e := gateRows_getD R h ((starParamsOf R h).translationOfCodes l) i
  unfold gateRows at e ⊢
  unfold starParamsOf at e ⊢
  simp only [Function.comp_apply]
  split_ifs at e ⊢ with hi
  · exact_mod_cast e
  · exact_mod_cast e

/-- **R2**: the exact objectives compare as their keys under the cross-multiplied compare. -/
theorem r2Objective : R2Objective := by
  intro R h hp l l'
  have hk : ∀ l, 0 < (objKey R h l).2 := fun l => by
    unfold objKey
    exact (ratAcc_val (R.pops.map fun X => (X.2.num.toNat, X.2.den, popRows R h l X)) (by
      intro x hx
      obtain ⟨X, _, rfl⟩ := List.mem_map.mp hx
      exact X.2.den_pos)).1
  rw [selObjective_eq_key R h hp, selObjective_eq_key R h hp, ratLt_iff _ _ (hk l) (hk l')]
  exact div_lt_div_iff_of_pos_right (by positivity)

end NearCubicWires.WireExponent3_5.SelectionMachine.Math.Objective
