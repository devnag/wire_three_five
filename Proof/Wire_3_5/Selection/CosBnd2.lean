import Proof.Wire_3_5.Selection.CosBnd1

/-! # C1.5 widths, part 2: the row counts and the exact accumulator fit in `W` bits (P3:1337-1360)

Paper: "Enumerate its `2^k` error rows [...] count pairs [...] Sum its exact count with the rational population
weights" (P3:1339-1357). A gate's row count at a coset counts centers over the `2^k` error rows: `gateRows ≤ 2^(n+k)`
(`rowCount_eq`: the centers of one row are at most `2^n`; `|Errors|² = 2^k`). A population's count is then at most
`L·2^(n+k)`, and the exact accumulator `(AN, AD)` over any prefix of the populations stays below `D·(j·M)` with
`D = Π den ≤ 2^L` and `M = 2^L·L·2^(n+k)`: every word the coset loop writes fits in `W` bits. Main declarations:
**`gateRows_le`**, `popT_le`, `dens_prod_le`, `fold_inv`, **`popsFit_all`**, **`key_bounds`**. Paper quantity: the
objective's exact numerators and denominators. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.RepairRepresentation (natWord intWord natListWord)

/-! ## Row counts -/

theorem errors_card (P : StarParams) : Fintype.card P.Errors = 2 ^ (P.s * (P.r / 2)) := by
  have hb : P.b + 1 = 2 ^ P.s := by
    have := Nat.one_le_two_pow (n := P.s); unfold StarParams.b; omega
  simp only [StarParams.Errors, Fintype.card_fun, Fintype.card_option, Fintype.card_fin, hb, ← pow_mul]

/-- **A gate's row count at a coset is at most `2^(n+k)`.** -/
theorem gateRows_le (P : StarParams) (σ : P.Translation) (g : NormalizedThresholdGate P.n) :
    gateRows P σ g ≤ 2 ^ (P.n + P.k) := by
  classical
  have hrow : ∀ u v, P.rowCount σ g u v ≤ 2 ^ P.n := fun u v => by
    rw [P.rowCount_eq]
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hsum : gateRows P σ g ≤ Fintype.card P.Errors * (Fintype.card P.Errors * 2 ^ P.n) := by
    unfold gateRows
    calc (∑ u : P.Errors, ∑ v : P.Errors, P.rowCount σ g u v) ≤ ∑ _u : P.Errors, ∑ _v : P.Errors, 2 ^ P.n :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hrow u v
      _ = Fintype.card P.Errors * (Fintype.card P.Errors * 2 ^ P.n) := by
          simp [Finset.sum_const, Finset.card_univ]
  rw [errors_card] at hsum
  have hr : P.r / 2 * 2 = P.r := Nat.div_mul_cancel (even_iff_two_dvd.mp P.r_even)
  have e : 2 ^ (P.s * (P.r / 2)) * (2 ^ (P.s * (P.r / 2)) * 2 ^ P.n) = 2 ^ (P.n + P.k) := by
    rw [← mul_assoc, ← pow_add, ← pow_add, StarParams.k]
    congr 1
    have : P.s * (P.r / 2) + P.s * (P.r / 2) = P.r * P.s := by
      rw [← Nat.mul_add, ← two_mul, show 2 * (P.r / 2) = P.r by omega, Nat.mul_comm]
    omega
  rw [e] at hsum
  exact hsum

theorem rowsAt_le (R : SelectionReq) (h : ParamsOk R) (N i : ℕ) : rowsAt R h N i ≤ 2 ^ (R.n + R.r * R.s) := by
  unfold rowsAt
  split_ifs
  · exact gateRows_le _ _ _
  · exact Nat.zero_le _

/-- A population's row count at a coset. -/
theorem popT_le (R : SelectionReq) (h : ParamsOk R) (N : ℕ) (X : List ℕ × ℚ) :
    popT R h N X ≤ X.1.length * 2 ^ (R.n + R.r * R.s) := by
  unfold popT
  have : ∀ l : List ℕ, (l.map (rowsAt R h N)).sum ≤ l.length * 2 ^ (R.n + R.r * R.s) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := rowsAt_le R h N a
      nlinarith
  exact this X.1

/-! ## The denominators -/

theorem prod_lt_pow : ∀ l : List ℕ, l.prod < 2 ^ (l.map natBitLength).sum + 1
  | [] => by simp
  | a :: l => by
    have ih := prod_lt_pow l
    have ha := lt_pow_natBitLength a
    simp only [List.prod_cons, List.map_cons, List.sum_cons, pow_add]
    have h1 : a * l.prod ≤ (2 ^ natBitLength a - 1) * (2 ^ (l.map natBitLength).sum) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 := Nat.one_le_two_pow (n := natBitLength a)
    have h3 := Nat.one_le_two_pow (n := (l.map natBitLength).sum)
    have : (2 ^ natBitLength a - 1) * 2 ^ (l.map natBitLength).sum ≤ 2 ^ natBitLength a * 2 ^ (l.map natBitLength).sum :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- **The denominators' product is at most `2^L`.** -/
theorem dens_prod_le (R : SelectionReq) : (R.pops.map fun X => X.2.den).prod ≤ 2 ^ Lof R := by
  have h := prod_lt_pow (R.pops.map fun X => X.2.den)
  have hb : ((R.pops.map fun X => X.2.den).map natBitLength).sum ≤ Lof R := by
    refine le_trans ?_ (pops_len_sum R)
    rw [List.map_map]
    apply List.sum_le_sum
    intro X _
    show natBitLength X.2.den ≤ (natListWord X.1 ++ WireExponent3_5.ratWord X.2).length
    rw [popWord_len]; omega
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hb
  omega

theorem dens_pos (ps : List (List ℕ × ℚ)) : 1 ≤ (ps.map fun X => X.2.den).prod := by
  induction ps with
  | nil => simp
  | cons X ps ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero X.2.den_pos.ne' (by omega))

/-! ## The accumulator -/

/-- **The accumulator's invariant** along the populations: `1 ≤ AD`, `AD · Π(remaining dens) ≤ D`, `AN ≤ AD·(j·M)`. -/
theorem fold_inv (R : SelectionReq) (h : ParamsOk R) (N M D : ℕ)
    (hM : ∀ X ∈ R.pops, X.2.num.toNat * popT R h N X ≤ M) :
    ∀ (ps : List (List ℕ × ℚ)) (acc : RegRat) (j : ℕ), (∀ X ∈ ps, X ∈ R.pops) → 1 ≤ acc.2 →
      acc.2 * (ps.map fun X => X.2.den).prod ≤ D → acc.1 ≤ acc.2 * (j * M) →
      1 ≤ (ps.foldl (popStep R h N) acc).2 ∧ (ps.foldl (popStep R h N) acc).2 ≤ D ∧
        (ps.foldl (popStep R h N) acc).1 ≤ (ps.foldl (popStep R h N) acc).2 * ((j + ps.length) * M)
  | [], acc, j, _, h1, hD, hN => by
    refine ⟨h1, by simpa using hD, by simpa using hN⟩
  | X :: ps, acc, j, hps, h1, hD, hN => by
    have hX := hM X (hps X List.mem_cons_self)
    have hden := X.2.den_pos
    simp only [List.map_cons, List.prod_cons] at hD
    have ih := fold_inv R h N M D hM ps (popStep R h N acc X) (j + 1) (fun Y hY => hps Y (List.mem_cons_of_mem _ hY))
      (by simp only [popStep, ratAccStep]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
      (by simp only [popStep, ratAccStep]; rw [Nat.mul_assoc]; exact hD)
      (by
        simp only [popStep, ratAccStep]
        have e1 : acc.1 * X.2.den ≤ acc.2 * (j * M) * X.2.den := Nat.mul_le_mul_right _ hN
        have e2 : X.2.num.toNat * popT R h N X * acc.2 ≤ M * acc.2 := Nat.mul_le_mul_right _ hX
        have e3 : M * acc.2 ≤ M * acc.2 * X.2.den := Nat.le_mul_of_pos_right _ hden
        nlinarith)
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨ih.1, ih.2.1, ?_⟩
    have := ih.2.2
    rw [show j + 1 + ps.length = j + (ps.length + 1) by ring] at this
    exact this

/-- **Every weighted step fits** in `W` bits. -/
theorem popsFit_all (R : SelectionReq) (h : ParamsOk R) (N W cap M D : ℕ)
    (hM : ∀ X ∈ R.pops, X.2.num.toNat * popT R h N X ≤ M) (hDp : (R.pops.map fun X => X.2.den).prod ≤ D)
    (hfit : D * ((R.pops.length + 1) * M) + D < 2 ^ W) (hT : ∀ X ∈ R.pops, popT R h N X < 2 ^ W)
    (hI : ∀ X ∈ R.pops, ∀ i ∈ X.1, i < 2 ^ W) (hC : ∀ X ∈ R.pops, X.1.length ≤ cap) :
    PopsFit R h N W cap (0, 1) R.pops := by
  have main : ∀ (ps : List (List ℕ × ℚ)) (acc : RegRat) (j : ℕ), (∀ X ∈ ps, X ∈ R.pops) → 1 ≤ acc.2 →
      acc.2 * (ps.map fun X => X.2.den).prod ≤ D → acc.1 ≤ acc.2 * (j * M) → j + ps.length ≤ R.pops.length →
      PopsFit R h N W cap acc ps := by
    intro ps
    induction ps with
    | nil => intros; trivial
    | cons X ps ih =>
      intro acc j hps h1 hD hN hj
      have hXm := hps X List.mem_cons_self
      have hX := hM X hXm
      have hden := X.2.den_pos
      have hrest := dens_pos ps
      simp only [List.map_cons, List.prod_cons] at hD
      have hAD : acc.2 * X.2.den ≤ D := le_trans (Nat.le_mul_of_pos_right _ hrest) (by rw [Nat.mul_assoc]; exact hD)
      have hstep : acc.1 * X.2.den + X.2.num.toNat * popT R h N X * acc.2 ≤ D * ((R.pops.length + 1) * M) := by
        have e1 : acc.1 * X.2.den ≤ acc.2 * (j * M) * X.2.den := Nat.mul_le_mul_right _ hN
        have e2 : X.2.num.toNat * popT R h N X * acc.2 ≤ M * acc.2 := Nat.mul_le_mul_right _ hX
        have e3 : M * acc.2 ≤ M * acc.2 * X.2.den := Nat.le_mul_of_pos_right _ hden
        have e4 : acc.2 * X.2.den * ((j + 1) * M) ≤ D * ((R.pops.length + 1) * M) :=
          Nat.mul_le_mul hAD (Nat.mul_le_mul_right _ (by simp at hj; omega))
        nlinarith
      have hd1 : X.2.den ≤ D := le_trans (Nat.le_mul_of_pos_left _ h1) hAD
      have ha1 : acc.2 ≤ D := le_trans (Nat.le_mul_of_pos_right _ hden) hAD
      refine ⟨⟨hC X hXm, hI X hXm, hT X hXm, h1, by omega, by omega, by omega, by omega⟩, ?_⟩
      exact ih (popStep R h N acc X) (j + 1) (fun Y hY => hps Y (List.mem_cons_of_mem _ hY))
        (by simp only [popStep, ratAccStep]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
        (by simp only [popStep, ratAccStep]; rw [Nat.mul_assoc]; exact hD)
        (by
          simp only [popStep, ratAccStep]
          have e1 : acc.1 * X.2.den ≤ acc.2 * (j * M) * X.2.den := Nat.mul_le_mul_right _ hN
          have e2 : X.2.num.toNat * popT R h N X * acc.2 ≤ M * acc.2 := Nat.mul_le_mul_right _ hX
          have e3 : M * acc.2 ≤ M * acc.2 * X.2.den := Nat.le_mul_of_pos_right _ hden
          nlinarith)
        (by simp at hj; omega)
  exact main R.pops (0, 1) 0 (fun X hX => hX) le_rfl (by simpa using hDp) (by simp) (by simp)

/-- **The keys fit**: `keyAt N = (AN, AD)` with `AD ≤ D` and `AN ≤ D·(#pops·M)`. -/
theorem key_bounds (R : SelectionReq) (h : ParamsOk R) (N M D : ℕ)
    (hM : ∀ X ∈ R.pops, X.2.num.toNat * popT R h N X ≤ M) (hDp : (R.pops.map fun X => X.2.den).prod ≤ D) :
    1 ≤ (keyAt R h N).2 ∧ (keyAt R h N).2 ≤ D ∧ (keyAt R h N).1 ≤ D * (R.pops.length * M) := by
  have := fold_inv R h N M D hM R.pops (0, 1) 0 (fun X hX => hX) le_rfl (by simpa using hDp) (by simp)
  unfold keyAt
  rw [← popsFold_eq_objKey]
  obtain ⟨a, b, c⟩ := this
  refine ⟨a, b, ?_⟩
  rw [Nat.zero_add] at c
  exact le_trans c (Nat.mul_le_mul_right _ b)

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
