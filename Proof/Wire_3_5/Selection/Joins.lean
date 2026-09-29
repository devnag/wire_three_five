import Proof.Wire_3_5.Selection.MathPlan

/-! # C1.1 R4–R6: the pair count by sorted `<`-joins (P3:1343-1356)

Paper: "For each of the sixteen corner patterns, count pairs satisfying its four weak inequalities, after changing a
strict integer cut into a weak cut with threshold shifted by one. For clarity, constant-dimensional dominance counting
needs only `O(U log^{O(1)} U)` comparisons for two lists of length `U` [...] The pattern determines whether the mixed
residual is nonzero" (P3:1343-1357). The corner structure collapses the sixteen patterns: with `t = θ − a`,
`t' = θ − a'` and `J = [min(t,t'), max(t,t'))`, the mixed difference is `±([b' ∈ J] − [b ∈ J])`, so a pair has a
nonzero mixed residual exactly when one of `b, b'` lies in `J`. Two 1-d counts and one 2-d dominance count remain, and
every count is a `<`-join of sorted keys:
* **`r4JForm`**: `pairCount + 2·dom2 = inCount` (pointwise `ind_J`);
* **`r5OneDim`**: `inCount I Y + J<(Y; lo) = J<(Y; hi)`;
* **`r6Levels`**: `dom2 I D + Σ_ℓ J<(K2_ℓ; K1_ℓ) = Σ_ℓ J<(K2_ℓ; K3_ℓ)` over the most-significant-bit levels
  (`lt_eq_sum_levels`: `[M < hi]` is the sum over `ℓ` of `[hi` has bit `ℓ`, `M` not, same prefix above `ℓ]`), with
  null queries and sentinel keys keeping every list's length;
* **`rKey`**: the offset-binary key `z + 2^V` (base `SignedSortKey.shifted`) is below `2^(V+1)` and order-preserving.
Paper quantity: the number of pairs with a nonzero mixed residual (`pairCount`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Math.Joins
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.SelectionMachine.Math

/-! ## R4: the J-form -/

/-- The J-form on explicit values. -/
theorem ind_J_core (θ a a' b b' : ℤ) :
    (if bitZ (decide (θ ≤ a' + b')) - bitZ (decide (θ ≤ a' + b)) - bitZ (decide (θ ≤ a + b')) +
        bitZ (decide (θ ≤ a + b)) ≠ 0 then 1 else 0) +
        2 * (if min (θ - a) (θ - a') ≤ min b b' ∧ max b b' < max (θ - a) (θ - a') then 1 else 0) =
      (if min (θ - a) (θ - a') ≤ b ∧ b < max (θ - a) (θ - a') then 1 else 0) +
        (if min (θ - a) (θ - a') ≤ b' ∧ b' < max (θ - a) (θ - a') then 1 else 0) := by
  rcases le_total a' a with h | h
  · rw [min_eq_left (show θ - a ≤ θ - a' by omega), max_eq_right (show θ - a ≤ θ - a' by omega)]
    by_cases p1 : θ ≤ a' + b' <;> by_cases p2 : θ ≤ a' + b <;> by_cases p3 : θ ≤ a + b' <;>
      by_cases p4 : θ ≤ a + b <;> simp [p1, p2, p3, p4, bitZ] <;> (try split_ifs) <;> omega
  · rw [min_eq_right (show θ - a' ≤ θ - a by omega), max_eq_left (show θ - a' ≤ θ - a by omega)]
    by_cases p1 : θ ≤ a' + b' <;> by_cases p2 : θ ≤ a' + b <;> by_cases p3 : θ ≤ a + b' <;>
      by_cases p4 : θ ≤ a + b <;> simp [p1, p2, p3, p4, bitZ] <;> (try split_ifs) <;> omega

/-- **Pointwise J-form**: `[Δ ≠ 0] + 2·[b, b' ∈ J] = [b ∈ J] + [b' ∈ J]`. -/
theorem ind_J (θ : ℤ) (p q : ℤ × ℤ) :
    (if cornerDelta (cutCorners θ p q) ≠ 0 then 1 else 0) +
        2 * (if loOf θ p ≤ min q.1 q.2 ∧ max q.1 q.2 < hiOf θ p then 1 else 0) =
      (if loOf θ p ≤ q.1 ∧ q.1 < hiOf θ p then 1 else 0) + (if loOf θ p ≤ q.2 ∧ q.2 < hiOf θ p then 1 else 0) :=
  ind_J_core θ p.1 p.2 q.1 q.2

theorem countP_J (θ : ℤ) (p : ℤ × ℤ) (R : List (ℤ × ℤ)) :
    R.countP (fun q => decide (cornerDelta (cutCorners θ p q) ≠ 0)) +
        2 * R.countP (fun q => decide (loOf θ p ≤ min q.1 q.2 ∧ max q.1 q.2 < hiOf θ p)) =
      R.countP (fun q => decide (loOf θ p ≤ q.1 ∧ q.1 < hiOf θ p)) +
        R.countP (fun q => decide (loOf θ p ≤ q.2 ∧ q.2 < hiOf θ p)) := by
  induction R with
  | nil => rfl
  | cons q R ih =>
    simp only [List.countP_cons, decide_eq_true_eq]
    have h := ind_J θ p q
    omega

theorem sum_pointwise {α : Type} (L : List α) (A B C : α → ℕ) (h : ∀ p, A p + 2 * B p = C p) :
    (L.map A).sum + 2 * (L.map B).sum = (L.map C).sum := by
  induction L with
  | nil => rfl
  | cons p L ih => simp only [List.map_cons, List.sum_cons]; have := h p; omega

/-- **R4**. -/
theorem r4JForm : R4JForm := by
  intro θ L R
  have hdom : dom2 (L.map fun p => (loOf θ p, hiOf θ p)) (R.map fun q => (min q.1 q.2, max q.1 q.2)) =
      (L.map fun p => R.countP (fun q => decide (loOf θ p ≤ min q.1 q.2 ∧ max q.1 q.2 < hiOf θ p))).sum := by
    unfold dom2
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    rw [Function.comp_apply, List.countP_map]
    rfl
  have hin : inCount (L.map fun p => (loOf θ p, hiOf θ p)) (R.map Prod.fst ++ R.map Prod.snd) =
      (L.map fun p => R.countP (fun q => decide (loOf θ p ≤ q.1 ∧ q.1 < hiOf θ p)) +
        R.countP (fun q => decide (loOf θ p ≤ q.2 ∧ q.2 < hiOf θ p))).sum := by
    unfold inCount
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    rw [Function.comp_apply, List.countP_append, List.countP_map, List.countP_map]
    rfl
  rw [hdom, hin]
  exact sum_pointwise L _ _ _ (fun p => countP_J θ p R)

/-! ## R5: the 1-d terms -/

theorem countP_interval (lo hi : ℕ) (hle : lo ≤ hi) (Y : List ℕ) :
    Y.countP (fun y => decide (lo ≤ y ∧ y < hi)) + Y.countP (fun y => decide (y < lo)) =
      Y.countP (fun y => decide (y < hi)) := by
  induction Y with
  | nil => rfl
  | cons y Y ih =>
    simp only [List.countP_cons, decide_eq_true_eq]
    split_ifs <;> omega

/-- **R5**. -/
theorem r5OneDim : R5OneDim := by
  intro I Y hI
  induction I with
  | nil => rfl
  | cons J I ih =>
    unfold inCount joinLt at *
    simp only [List.map_cons, List.sum_cons]
    have h := countP_interval J.1 J.2 (hI J List.mem_cons_self) Y
    have := ih (fun J' hJ' => hI J' (List.mem_cons_of_mem _ hJ'))
    omega

/-! ## R6: the 2-d term by most-significant-bit levels -/

/-- The level-`ℓ` event: `hi` has bit `ℓ`, `M` has not, and they agree above `ℓ`. -/
def lvl (ℓ M hi : ℕ) : Prop := hi.testBit ℓ = true ∧ M.testBit ℓ = false ∧ M / 2 ^ (ℓ + 1) = hi / 2 ^ (ℓ + 1)

instance (ℓ M hi : ℕ) : Decidable (lvl ℓ M hi) := by unfold lvl; infer_instance

theorem lvl_succ (ℓ M hi : ℕ) : lvl (ℓ + 1) M hi ↔ lvl ℓ (M / 2) (hi / 2) := by
  unfold lvl
  rw [Nat.testBit_succ, Nat.testBit_succ, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-- **`[M < hi]` is the sum of the level events** (keys below `2^W`). -/
theorem lt_eq_sum_levels : ∀ (W M hi : ℕ), M < 2 ^ W → hi < 2 ^ W →
    (if M < hi then 1 else 0) = ((List.range W).map fun ℓ => if lvl ℓ M hi then 1 else 0).sum
  | 0, M, hi, hM, hh => by
    have e1 : M = 0 := by simpa using hM
    have e2 : hi = 0 := by simpa using hh
    subst e1; subst e2; rfl
  | W + 1, M, hi, hM, hh => by
    have ih := lt_eq_sum_levels W (M / 2) (hi / 2) (by rw [Nat.pow_succ] at hM; omega)
      (by rw [Nat.pow_succ] at hh; omega)
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have e : ((List.range W).map ((fun ℓ => if lvl ℓ M hi then 1 else 0) ∘ Nat.succ)) =
        (List.range W).map fun ℓ => if lvl ℓ (M / 2) (hi / 2) then 1 else 0 := by
      apply List.map_congr_left
      intro ℓ _
      rw [Function.comp_apply, Nat.succ_eq_add_one]
      exact if_congr (lvl_succ ℓ M hi) rfl rfl
    rw [e, ← ih]
    have h0 : lvl 0 M hi ↔ (hi % 2 = 1 ∧ M % 2 = 0 ∧ M / 2 = hi / 2) := by
      unfold lvl
      rw [Nat.testBit_zero, Nat.testBit_zero, decide_eq_true_eq, decide_eq_false_iff_not, zero_add, pow_one]
      constructor <;> intro h' <;> omega
    rw [if_congr h0 rfl rfl]
    split_ifs <;> omega

/-- Composite keys: `pM·X + m < pH·X + lo` is the lexicographic order when `m, lo < X`. -/
theorem key_lt_iff (X pM m pH lo : ℕ) (hm : m < X) (hlo : lo < X) :
    pM * X + m < pH * X + lo ↔ pM < pH ∨ (pM = pH ∧ m < lo) := by
  rcases Nat.lt_trichotomy pM pH with h | h | h
  · have h1 : (pM + 1) * X ≤ pH * X := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at h1
    constructor
    · intro _; exact Or.inl h
    · intro _; omega
  · subst h
    constructor
    · intro h'; right; exact ⟨rfl, by omega⟩
    · rintro (h' | ⟨_, h'⟩) <;> omega
  · have h1 : (pH + 1) * X ≤ pM * X := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at h1
    constructor
    · intro h'; omega
    · rintro (h' | ⟨h', _⟩) <;> omega

/-- The level-`ℓ` indicator identity for one pair: `[K2 < K3] = [K2 < K1] + [lvl ∧ lo ≤ m]`. -/
theorem level_pair (W ℓ : ℕ) (J d : ℕ × ℕ) (hJ : J.1 < 2 ^ W ∧ J.2 < 2 ^ W) (hd : d.1 < 2 ^ W ∧ d.2 < 2 ^ W) :
    (if (if d.2.testBit ℓ then 2 ^ (2 * W) - 1 else d.2 / 2 ^ (ℓ + 1) * 2 ^ W + d.1) <
        (if J.2.testBit ℓ then (J.2 / 2 ^ (ℓ + 1) + 1) * 2 ^ W else 0) then 1 else 0) =
      (if (if d.2.testBit ℓ then 2 ^ (2 * W) - 1 else d.2 / 2 ^ (ℓ + 1) * 2 ^ W + d.1) <
          (if J.2.testBit ℓ then J.2 / 2 ^ (ℓ + 1) * 2 ^ W + J.1 else 0) then 1 else 0) +
        (if lvl ℓ d.2 J.2 ∧ J.1 ≤ d.1 then 1 else 0) := by
  have hXX : 2 ^ (2 * W) = 2 ^ W * 2 ^ W := by rw [← Nat.pow_add, Nat.two_mul]
  have hl : (lvl ℓ d.2 J.2 ∧ J.1 ≤ d.1) ↔
      ((J.2.testBit ℓ = true ∧ d.2.testBit ℓ = false ∧ d.2 / 2 ^ (ℓ + 1) = J.2 / 2 ^ (ℓ + 1)) ∧ J.1 ≤ d.1) :=
    Iff.rfl
  rw [hXX, if_congr hl rfl rfl]
  have hH : J.2 / 2 ^ (ℓ + 1) ≤ J.2 / 2 :=
    Nat.div_le_div_left (by rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := ℓ); omega) (by norm_num)
  set X := 2 ^ W with hX
  set pH := J.2 / 2 ^ (ℓ + 1) with hpH
  set pM := d.2 / 2 ^ (ℓ + 1) with hpM
  cases hb : J.2.testBit ℓ
  · simp
  · have hpos : 0 < J.2 := by
      rcases Nat.eq_zero_or_pos J.2 with h | h
      · rw [h, Nat.zero_testBit] at hb; exact absurd hb (by simp)
      · exact h
    have hq : pH + 1 < X := by omega
    cases hm : d.2.testBit ℓ
    · have c3 : pM * X + d.1 < (pH + 1) * X ↔ pM ≤ pH := by
        have := key_lt_iff X pM d.1 (pH + 1) 0 hd.1 (by omega)
        rw [Nat.add_zero] at this
        rw [this]; omega
      have c1 := key_lt_iff X pM d.1 pH J.1 hd.1 hJ.1
      simp only [Bool.false_eq_true, ↓reduceIte, true_and]
      rw [if_congr c3 rfl rfl, if_congr c1 rfl rfl]
      split_ifs <;> omega
    · have h3 : (pH + 1) * X ≤ X * X - 1 := by
        have h4 : (pH + 2) * X ≤ X * X := Nat.mul_le_mul_right _ (by omega)
        rw [show pH + 2 = (pH + 1) + 1 by omega, Nat.succ_mul] at h4
        omega
      have h1 : pH * X + J.1 < (pH + 1) * X := by rw [Nat.succ_mul]; omega
      simp only [↓reduceIte, Bool.true_eq_false, false_and, and_false]
      rw [if_neg (by omega), if_neg (by omega)]

/-- Sums over the levels commute with sums over a list. -/
theorem sum_comm_range {α : Type} (I : List α) (W : ℕ) (f : α → ℕ → ℕ) :
    (I.map fun J => ((List.range W).map (f J)).sum).sum =
      ((List.range W).map fun ℓ => (I.map fun J => f J ℓ).sum).sum := by
  induction I with
  | nil => simp
  | cons J I ih => simp only [List.map_cons, List.sum_cons, ih, List.sum_map_add]

theorem countP_eq_sum' {α : Type} (l : List α) (p : α → Bool) :
    l.countP p = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.countP_cons, ih, List.map_cons, List.sum_cons]; omega

/-- **R6**. -/
theorem r6Levels : R6Levels := by
  intro W I D hI hD
  have hjoin : ∀ (k2 : ℕ × ℕ → ℕ) (k1 : ℕ × ℕ → ℕ),
      joinLt (D.map k2) (I.map k1) = (I.map fun J => (D.map fun d => if k2 d < k1 J then 1 else 0).sum).sum := by
    intro k2 k1
    unfold joinLt
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro J _
    rw [Function.comp_apply, countP_eq_sum', List.map_map]
    congr 1
    apply List.map_congr_left
    intro d _
    simp only [Function.comp_apply, decide_eq_true_eq]
  have hdom : dom2 I D = (I.map fun J => (D.map fun d => if J.1 ≤ d.1 ∧ d.2 < J.2 then 1 else 0).sum).sum := by
    unfold dom2
    congr 1
    apply List.map_congr_left
    intro J _
    rw [countP_eq_sum']
    simp only [decide_eq_true_eq]
  unfold lvlK1 lvlK2 lvlK3
  simp only [hjoin, hdom]
  rw [← sum_comm_range, ← sum_comm_range, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro J hJ
  rw [← sum_comm_range, ← sum_comm_range, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro d hd
  have hlt := lt_eq_sum_levels W d.2 J.2 (hD d hd).2 (hI J hJ).2
  have hsplit : ∀ ℓ ∈ List.range W,
      (if (if d.2.testBit ℓ then 2 ^ (2 * W) - 1 else d.2 / 2 ^ (ℓ + 1) * 2 ^ W + d.1) <
        (if J.2.testBit ℓ then (J.2 / 2 ^ (ℓ + 1) + 1) * 2 ^ W else 0) then 1 else 0) =
      (if (if d.2.testBit ℓ then 2 ^ (2 * W) - 1 else d.2 / 2 ^ (ℓ + 1) * 2 ^ W + d.1) <
          (if J.2.testBit ℓ then J.2 / 2 ^ (ℓ + 1) * 2 ^ W + J.1 else 0) then 1 else 0) +
        (if lvl ℓ d.2 J.2 ∧ J.1 ≤ d.1 then 1 else 0) :=
    fun ℓ _ => level_pair W ℓ J d (hI J hJ) (hD d hd)
  rw [List.map_congr_left hsplit, List.sum_map_add]
  have hfac : ((List.range W).map fun ℓ => if lvl ℓ d.2 J.2 ∧ J.1 ≤ d.1 then 1 else 0).sum =
      if J.1 ≤ d.1 ∧ d.2 < J.2 then 1 else 0 := by
    by_cases hle : J.1 ≤ d.1
    · simp only [hle, and_true, true_and]
      exact hlt.symm
    · simp [hle]
  rw [hfac]
  omega

/-! ## The key transfer -/

/-- **RKey**. -/
theorem rKey : RKey := by
  intro V z z' hz hz'
  have hc : (0 : ℤ) < ((2 ^ V : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos V
  have b1 : -((2 ^ V : ℕ) : ℤ) < z ∧ z < ((2 ^ V : ℕ) : ℤ) := by
    constructor <;> [skip; skip] <;> omega
  have b2 : -((2 ^ V : ℕ) : ℤ) < z' ∧ z' < ((2 ^ V : ℕ) : ℤ) := by
    constructor <;> [skip; skip] <;> omega
  have k1 : ((keyOf V z : ℕ) : ℤ) = z + ((2 ^ V : ℕ) : ℤ) := by
    unfold keyOf RepairOrdinary.SignedSortKey.shifted
    exact Int.toNat_of_nonneg (by omega)
  have k2 : ((keyOf V z' : ℕ) : ℤ) = z' + ((2 ^ V : ℕ) : ℤ) := by
    unfold keyOf RepairOrdinary.SignedSortKey.shifted
    exact Int.toNat_of_nonneg (by omega)
  have hpow : ((2 ^ (V + 1) : ℕ) : ℤ) = 2 * ((2 ^ V : ℕ) : ℤ) := by push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · have : ((keyOf V z : ℕ) : ℤ) < ((2 ^ (V + 1) : ℕ) : ℤ) := by rw [k1, hpow]; omega
    exact_mod_cast this
  · rw [← Nat.cast_lt (α := ℤ), k1, k2]; omega
  · rw [← Nat.cast_le (α := ℤ), k1, k2]; omega

end NearCubicWires.WireExponent3_5.SelectionMachine.Math.Joins
