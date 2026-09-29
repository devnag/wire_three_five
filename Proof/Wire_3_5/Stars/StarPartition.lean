import Proof.Wire_3_5.Foundations.StarPartition
import Proof.Wire_3_5.Stars.StarPopulation

/-! # `star:partition` (P3:1186-1218), proved

Realizes the lemma "There are `2^k` explicitly described partitions of `{0,1}^n`, each into `2^{n−k}` cells of size
`2^k`. A point of a cell is specified by one choice from `{0,e_1,…,e_b}` in each of `r` disjoint blocks. For every
partition, uniform cell and uniform point give a uniform original input. Averaging the partition and its uniformly
chosen center gives a uniform ambient center, independently of the point choices. The center bits can be divided
into two halves differing in size by at most one while keeping each code block on its assigned side." (P3:1188-1197),
by the paper's proof (P3:1199-1218): syndrome decoding in each block, all `2^s` cosets per block, cardinalities by
multiplication.

Main results, at the seed definitions of `Proof.Wire_3_5.Foundations.StarPartition`:
* `errorOf_unique`, `syndrome_errorOf`: "every `x ∈ 𝔽₂^b` has exactly one representation `x = c + e`" in any fixed
  coset;
* `card_coset`: each coset has `2^{b−s}` elements (the code dimension `b − s`);
* `decomposition σ : BitInput n ≃ {c // IsCenter σ c} × Errors × Errors`: cell center plus one error choice per block;
* `card_translation = 2^k`, `card_cell = 2^k`, `card_centers = 2^{n−k}`;
* `sum_eq_sum_cells` (uniform cell and uniform point give a uniform input) and `sum_translations_inputs`,
  `average_translations_inputs` (averaging the partition and its center gives a uniform ambient center, independently
  of the point choices — the average that `starPopulation_holds` bounds);
* `centerBits_sum`, `centerBits_balanced`, `centerSide`: the two halves of the center bits. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires Finset

theorem fin2_add_self (a : Fin 2) : a + a = 0 := by fin_cases a <;> rfl

theorem syndromeVec_add_self {s : ℕ} (d : SyndromeVec s) : d + d = 0 :=
  funext fun t => fin2_add_self (d t)

theorem syndromeVec_add_eq_zero {s : ℕ} {d e : SyndromeVec s} : d + e = 0 ↔ d = e := by
  constructor
  · intro h
    have := congrArg (· + e) h
    simpa [add_assoc, syndromeVec_add_self] using this
  · rintro rfl; exact syndromeVec_add_self d

theorem finFunctionFinEquiv_zero {s : ℕ} : (finFunctionFinEquiv (0 : SyndromeVec s)).val = 0 := by
  rw [finFunctionFinEquiv_apply]; simp

namespace StarParams
variable (P : StarParams)

/-! ## One block: syndrome decoding (P3:1202-1206) -/

/-- The block of one error choice: `0` or a unit vector `e_i`. -/
def errBits (e : Option (Fin P.b)) : Fin P.b → Bool := fun i => decide (e = some i)

theorem syndrome_xor (y y' : Fin P.b → Bool) :
    P.syndrome (fun i => xor (y i) (y' i)) = P.syndrome y + P.syndrome y' := by
  unfold syndrome
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  by_cases h1 : y i <;> by_cases h2 : y' i <;> simp [h1, h2, syndromeVec_add_self]

theorem syndrome_errBits_none : P.syndrome (P.errBits none) = 0 := by
  simp [syndrome, errBits]

theorem syndrome_errBits_some (i : Fin P.b) : P.syndrome (P.errBits (some i)) = P.column i := by
  simp [syndrome, errBits]

theorem finFunctionFinEquiv_column (i : Fin P.b) :
    (finFunctionFinEquiv (P.column i)).val = i.val + 1 := by
  simp [column]

theorem column_ne_zero (i : Fin P.b) : P.column i ≠ 0 := by
  intro h
  have := P.finFunctionFinEquiv_column i
  rw [h, finFunctionFinEquiv_zero] at this
  omega

/-- A nonzero syndrome is the column of the coordinate `(its code) − 1`. -/
theorem column_index {d : SyndromeVec P.s} (hd : d ≠ 0) (h : (finFunctionFinEquiv d).val - 1 < P.b) :
    P.column ⟨(finFunctionFinEquiv d).val - 1, h⟩ = d := by
  have hpos : (finFunctionFinEquiv d).val ≠ 0 := by
    intro h0
    apply hd
    apply finFunctionFinEquiv.injective
    apply Fin.ext
    rw [h0, finFunctionFinEquiv_zero]
  unfold column
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp only
  omega

/-- The syndrome of `y` corrected by its error is the target: `H(y + e) = σ` (P3:1204-1206). -/
theorem syndrome_errorOf (σ : SyndromeVec P.s) (y : Fin P.b → Bool) :
    P.syndrome (fun i => xor (y i) (P.errBits (P.errorOf σ y) i)) = σ := by
  rw [syndrome_xor]
  unfold errorOf
  split_ifs with h
  · rw [syndrome_errBits_none, add_zero]; exact syndromeVec_add_eq_zero.mp h
  · rw [syndrome_errBits_some, column_index P h]
    rw [← add_assoc, syndromeVec_add_self, zero_add]

theorem errorOf_eq_none {σ : SyndromeVec P.s} {y : Fin P.b → Bool} (h : P.syndrome y + σ = 0) :
    P.errorOf σ y = none := by
  unfold errorOf; rw [if_pos h]

theorem errorOf_eq_some {σ : SyndromeVec P.s} {y : Fin P.b → Bool} {i : Fin P.b}
    (h : P.syndrome y + σ = P.column i) : P.errorOf σ y = some i := by
  unfold errorOf
  rw [if_neg (by rw [h]; exact P.column_ne_zero i)]
  congr 1
  apply Fin.ext
  show (finFunctionFinEquiv (P.syndrome y + σ)).val - 1 = i.val
  rw [h, P.finFunctionFinEquiv_column]; omega

/-- **Uniqueness** (P3:1204-1206): a point `c + e` of the coset `σ`'s cell at `c` recovers its error `e`. -/
theorem errorOf_unique {σ : SyndromeVec P.s} {c : Fin P.b → Bool} (hc : P.syndrome c = σ)
    (e : Option (Fin P.b)) : P.errorOf σ (fun i => xor (c i) (P.errBits e i)) = e := by
  have hs : P.syndrome (fun i => xor (c i) (P.errBits e i)) + σ = P.syndrome (P.errBits e) := by
    rw [syndrome_xor, hc, add_comm σ, add_assoc, syndromeVec_add_self, add_zero]
  cases e with
  | none => exact P.errorOf_eq_none (hs.trans P.syndrome_errBits_none)
  | some i => exact P.errorOf_eq_some (hs.trans (P.syndrome_errBits_some i))

theorem s_le_b : P.s ≤ P.b := by
  have := Nat.lt_two_pow_self (n := P.s); have := P.b_succ; omega

/-! ## The blocks of an input -/

theorem block_cases (J : Fin P.r) : (∃ j, J = P.leftBlock j) ∨ (∃ j, J = P.rightBlock j) := by
  have hr := Nat.div_mul_cancel (even_iff_two_dvd.mp P.r_even)
  by_cases h : J.val < P.r / 2
  · exact Or.inl ⟨⟨J.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨J.val - P.r / 2, by have := J.isLt; omega⟩, Fin.ext (by simp [rightBlock]; omega)⟩

theorem leftBlock_ne_rightBlock (j j' : Fin (P.r / 2)) : P.leftBlock j ≠ P.rightBlock j' := by
  intro h; have := congrArg Fin.val h; simp [leftBlock, rightBlock] at this; omega

theorem errorVector_blockCoord (side : Fin (P.r / 2) → Fin P.r) (e : P.Errors) (J : Fin P.r) (i : Fin P.b) :
    P.errorVector side e (P.blockCoord J i) = decide (∃ j, side j = J ∧ e j = some i) := by
  simp only [errorVector]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨j, i', he, hc⟩
    obtain ⟨hJ, hi⟩ := P.blockCoord_inj hc
    exact ⟨j, hJ, hi ▸ he⟩
  · rintro ⟨j, hJ, he⟩
    exact ⟨j, i, he, hJ ▸ rfl⟩

theorem blockBits_left_left (u : P.Errors) (j : Fin (P.r / 2)) :
    P.blockBits (P.errorVector P.leftBlock u) (P.leftBlock j) = P.errBits (u j) := by
  funext i
  simp only [blockBits, errBits, errorVector_blockCoord]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨j', hj, he⟩; rw [P.leftBlock_inj hj] at he; exact he
  · intro h; exact ⟨j, rfl, h⟩

theorem blockBits_left_right (u : P.Errors) (j : Fin (P.r / 2)) :
    P.blockBits (P.errorVector P.leftBlock u) (P.rightBlock j) = P.errBits none := by
  funext i
  simp only [blockBits, errBits, errorVector_blockCoord, reduceCtorEq, decide_false]
  simp only [decide_eq_false_iff_not, not_exists, not_and]
  intro j' hj; exact absurd hj (P.leftBlock_ne_rightBlock j' j)

theorem blockBits_right_right (v : P.Errors) (j : Fin (P.r / 2)) :
    P.blockBits (P.errorVector P.rightBlock v) (P.rightBlock j) = P.errBits (v j) := by
  funext i
  simp only [blockBits, errBits, errorVector_blockCoord]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨j', hj, he⟩; rw [P.rightBlock_inj hj] at he; exact he
  · intro h; exact ⟨j, rfl, h⟩

theorem blockBits_right_left (v : P.Errors) (j : Fin (P.r / 2)) :
    P.blockBits (P.errorVector P.rightBlock v) (P.leftBlock j) = P.errBits none := by
  funext i
  simp only [blockBits, errBits, errorVector_blockCoord, reduceCtorEq, decide_false]
  simp only [decide_eq_false_iff_not, not_exists, not_and]
  intro j' hj; exact absurd hj.symm (P.leftBlock_ne_rightBlock j j')

theorem blockBits_xorInput (x y : BitInput P.n) (J : Fin P.r) :
    P.blockBits (xorInput x y) J = fun i => xor (P.blockBits x J i) (P.blockBits y J i) := rfl

/-! ## The decomposition `x = c + u + v` (P3:1204-1209, 1220-1222) -/

theorem errBits_none_apply (i : Fin P.b) : P.errBits none i = false := by simp [errBits]

theorem center_isCenter (σ : P.Translation) (x : BitInput P.n) : P.IsCenter σ (P.center σ x) := by
  intro J
  rcases P.block_cases J with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h : P.blockBits (P.center σ x) (P.leftBlock j) =
        fun i => xor (P.blockBits x (P.leftBlock j) i)
          (P.errBits (P.errorOf (σ (P.leftBlock j)) (P.blockBits x (P.leftBlock j))) i) := by
      funext i
      simp only [center, blockBits_xorInput, blockBits_left_left, blockBits_right_left, errBits_none_apply,
        Bool.xor_false, leftErrors]
    rw [h]; exact P.syndrome_errorOf _ _
  · have h : P.blockBits (P.center σ x) (P.rightBlock j) =
        fun i => xor (P.blockBits x (P.rightBlock j) i)
          (P.errBits (P.errorOf (σ (P.rightBlock j)) (P.blockBits x (P.rightBlock j))) i) := by
      funext i
      simp only [center, blockBits_xorInput, blockBits_left_right, blockBits_right_right, errBits_none_apply,
        Bool.xor_false, rightErrors]
    rw [h]; exact P.syndrome_errorOf _ _

theorem xorInput_cancel (x a b : BitInput P.n) :
    xorInput (xorInput (xorInput (xorInput x a) b) a) b = x := by
  funext i; simp only [xorInput]; cases x i <;> cases a i <;> cases b i <;> rfl

theorem point_center (σ : P.Translation) (x : BitInput P.n) :
    P.point (P.center σ x) (P.leftErrors σ x) (P.rightErrors σ x) = x :=
  P.xorInput_cancel _ _ _

theorem leftErrors_point {σ : P.Translation} {c : BitInput P.n} (hc : P.IsCenter σ c) (u v : P.Errors) :
    P.leftErrors σ (P.point c u v) = u := by
  funext j
  have h : P.blockBits (P.point c u v) (P.leftBlock j) =
      fun i => xor (P.blockBits c (P.leftBlock j) i) (P.errBits (u j) i) := by
    funext i
    simp only [point, blockBits_xorInput, blockBits_left_left, blockBits_right_left, errBits_none_apply,
      Bool.xor_false]
  simp only [leftErrors]; rw [h]; exact P.errorOf_unique (hc _) _

theorem rightErrors_point {σ : P.Translation} {c : BitInput P.n} (hc : P.IsCenter σ c) (u v : P.Errors) :
    P.rightErrors σ (P.point c u v) = v := by
  funext j
  have h : P.blockBits (P.point c u v) (P.rightBlock j) =
      fun i => xor (P.blockBits c (P.rightBlock j) i) (P.errBits (v j) i) := by
    funext i
    simp only [point, blockBits_xorInput, blockBits_left_right, blockBits_right_right, errBits_none_apply,
      Bool.xor_false]
  simp only [rightErrors]; rw [h]; exact P.errorOf_unique (hc _) _

theorem center_point {σ : P.Translation} {c : BitInput P.n} (hc : P.IsCenter σ c) (u v : P.Errors) :
    P.center σ (P.point c u v) = c := by
  unfold center
  rw [P.leftErrors_point hc, P.rightErrors_point hc]
  exact P.xorInput_cancel _ _ _

/-- **The cell decomposition** (P3:1188-1193): in the partition `σ`, an input is exactly a cell center together
with one choice from `{0, e_1, …, e_b}` in each of the `r` blocks. -/
def decomposition (σ : P.Translation) : BitInput P.n ≃ {c // P.IsCenter σ c} × P.Errors × P.Errors where
  toFun x := (⟨P.center σ x, P.center_isCenter σ x⟩, P.leftErrors σ x, P.rightErrors σ x)
  invFun p := P.point p.1.1 p.2.1 p.2.2
  left_inv x := P.point_center σ x
  right_inv p := by
    obtain ⟨⟨c, hc⟩, u, v⟩ := p
    simp only [P.center_point hc, P.leftErrors_point hc, P.rightErrors_point hc]

/-! ## Cardinalities (P3:1189-1191, 1206-1209) -/

theorem k_le_n : P.k ≤ P.n := by
  unfold k
  calc P.r * P.s ≤ P.r * P.b := Nat.mul_le_mul_left _ P.s_le_b
    _ ≤ P.n := P.r_mul_b_le

theorem r_half_add : P.r / 2 + P.r / 2 = P.r := by have := P.r_even; obtain ⟨m, hm⟩ := this; omega

/-- There are `2^k` partitions (P3:1189-1190, 1207). -/
theorem card_translation : Fintype.card P.Translation = 2 ^ P.k := by
  simp only [Translation, SyndromeVec, Fintype.card_fun, Fintype.card_fin, k]
  rw [← pow_mul, mul_comm]

/-- Each cell has `2^k` points (P3:1190). -/
theorem card_cell : Fintype.card (P.Errors × P.Errors) = 2 ^ P.k := by
  simp only [Fintype.card_prod, StarParams.Errors, Fintype.card_fun, Fintype.card_option, Fintype.card_fin, P.b_succ]
  rw [← pow_mul, ← pow_add, ← mul_add, P.r_half_add, k, mul_comm]

/-- Each partition has `2^{n−k}` cells (P3:1190). -/
theorem card_centers (σ : P.Translation) : Fintype.card {c // P.IsCenter σ c} = 2 ^ (P.n - P.k) := by
  have h := Fintype.card_congr (P.decomposition σ)
  rw [Fintype.card_prod, P.card_cell] at h
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have hn : 2 ^ P.n = 2 ^ (P.n - P.k) * 2 ^ P.k := by rw [← pow_add, Nat.sub_add_cancel P.k_le_n]
  rw [hn] at h
  exact (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h).symm

/-! ## Uniformity (P3:1192-1195, 1210-1212) -/

/-- **Uniform cell and uniform point give a uniform original input** (P3:1192-1193), as a sum identity. -/
theorem sum_eq_sum_cells {M : Type} [AddCommMonoid M] (σ : P.Translation) (f : BitInput P.n → M) :
    ∑ x, f x = ∑ c ∈ univ.filter (P.IsCenter σ), ∑ u : P.Errors, ∑ v : P.Errors, f (P.point c u v) := by
  rw [← Equiv.sum_comp (P.decomposition σ).symm, Fintype.sum_prod_type,
    Finset.sum_subtype (p := P.IsCenter σ) (univ.filter (P.IsCenter σ)) (fun c => by simp)
      (fun c => ∑ u : P.Errors, ∑ v : P.Errors, f (P.point c u v))]
  apply Finset.sum_congr rfl; intro a _
  rw [Fintype.sum_prod_type]; rfl

/-- The syndromes of all blocks of an input: the partition in which it is a center. -/
def syndromes (c : BitInput P.n) : P.Translation := fun j => P.syndrome (P.blockBits c j)

theorem isCenter_iff (σ : P.Translation) (c : BitInput P.n) : P.IsCenter σ c ↔ P.syndromes c = σ := by
  constructor
  · intro h; funext j; exact h j
  · intro h j; rw [← h]; rfl

/-- Every input is a center of exactly one partition, so the centers of all partitions sum to the cube. -/
theorem sum_translations_centers {M : Type} [AddCommMonoid M] (g : BitInput P.n → M) :
    ∑ σ : P.Translation, ∑ c ∈ univ.filter (P.IsCenter σ), g c = ∑ c, g c := by
  have h : ∀ σ : P.Translation, univ.filter (P.IsCenter σ) = univ.filter fun c => P.syndromes c = σ := by
    intro σ; ext c; simp [P.isCenter_iff]
  simp only [h]
  exact Finset.sum_fiberwise univ P.syndromes g

/-- **Averaging the partition and its uniformly chosen center gives a uniform ambient center, independently of the
point choices** (P3:1193-1195, 1210-1212), as a sum identity: summing any function of `(center, u, v)` over all
partitions and all inputs is summing it over all ambient centers and all error choices. -/
theorem sum_translations_inputs {M : Type} [AddCommMonoid M]
    (F : BitInput P.n → P.Errors → P.Errors → M) :
    ∑ σ : P.Translation, ∑ x, F (P.center σ x) (P.leftErrors σ x) (P.rightErrors σ x) =
      ∑ c, ∑ u : P.Errors, ∑ v : P.Errors, F c u v := by
  rw [← P.sum_translations_centers fun c => ∑ u : P.Errors, ∑ v : P.Errors, F c u v]
  apply Finset.sum_congr rfl; intro σ _
  rw [P.sum_eq_sum_cells σ]
  apply Finset.sum_congr rfl; intro c hc
  have hc' : P.IsCenter σ c := (Finset.mem_filter.mp hc).2
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  rw [P.center_point hc', P.leftErrors_point hc', P.rightErrors_point hc']

/-! ## The two halves of the center bits (P3:1195-1197, 1212-1215) -/

/-- The side of a coordinate: the left blocks, and the first `⌈(n−rb)/2⌉` unblocked coordinates, are left
(P3:1213-1215: "Assign `r/2` whole blocks to each side [...] Split the remaining `n−rb` coordinates as evenly as
possible"). -/
def centerSide (x : Fin P.n) : Bool :=
  decide (x.val < P.r / 2 * P.b ∨ (P.r * P.b ≤ x.val ∧ x.val < P.r * P.b + (P.n - P.r * P.b + 1) / 2))

/-- Left center bits: `b − s` free bits in each of the `r/2` left blocks plus `⌈(n−rb)/2⌉` unblocked ones. -/
def leftCenterBits : ℕ := P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b + 1) / 2

/-- Right center bits: `b − s` free bits in each of the `r/2` right blocks plus `⌊(n−rb)/2⌋` unblocked ones. -/
def rightCenterBits : ℕ := P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b) / 2

/-- The halves together are the `n − k` center bits (P3:1190, 1214). -/
theorem centerBits_sum : P.leftCenterBits + P.rightCenterBits = P.n - P.k := by
  unfold leftCenterBits rightCenterBits k
  have h1 := P.r_mul_b_le; have h2 := P.s_le_b; have h3 := P.r_half_add
  have e1 : P.r / 2 * (P.b - P.s) + P.r / 2 * (P.b - P.s) = P.r * P.b - P.r * P.s := by
    rw [← add_mul, h3, Nat.mul_sub]
  have e2 : P.r * P.s ≤ P.r * P.b := Nat.mul_le_mul_left _ h2
  omega

/-- The halves differ in size by at most one (P3:1195-1196). -/
theorem centerBits_balanced :
    P.rightCenterBits ≤ P.leftCenterBits ∧ P.leftCenterBits ≤ P.rightCenterBits + 1 := by
  unfold leftCenterBits rightCenterBits; omega

/-- Each code block lies entirely on its assigned side (P3:1196-1197, 1213). -/
theorem centerSide_leftBlock (j : Fin (P.r / 2)) (i : Fin P.b) :
    P.centerSide (P.blockCoord (P.leftBlock j) i) = true := by
  simp only [centerSide, blockCoord, leftBlock, decide_eq_true_eq]
  left
  have := j.isLt; have := i.isLt
  calc j.val * P.b + i.val < (j.val + 1) * P.b := by nlinarith
    _ ≤ P.r / 2 * P.b := Nat.mul_le_mul_right _ (by omega)

theorem centerSide_rightBlock (j : Fin (P.r / 2)) (i : Fin P.b) :
    P.centerSide (P.blockCoord (P.rightBlock j) i) = false := by
  simp only [centerSide, blockCoord, rightBlock, decide_eq_false_iff_not, not_or, not_and, not_lt]
  have := j.isLt; have := i.isLt; have h3 := P.r_half_add
  refine ⟨?_, ?_⟩
  · calc P.r / 2 * P.b ≤ (P.r / 2 + j.val) * P.b := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (P.r / 2 + j.val) * P.b + i.val := Nat.le_add_right _ _
  · intro h
    exfalso
    have : (P.r / 2 + j.val) * P.b + i.val < (P.r / 2 + j.val + 1) * P.b := by nlinarith
    have : (P.r / 2 + j.val + 1) * P.b ≤ P.r * P.b := Nat.mul_le_mul_right _ (by omega)
    omega

/-! ## Executable check (test before prove): the decomposition at `n = 8`, `r = 2` (`s = 2`, `b = 3`, `k = 4`) -/

end StarParams

end NearCubicWires.WireExponent3_5.Shared
