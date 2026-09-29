import Proof.Wire_3_5.Sampler.SamplerCond
import Proof.Wire_3_5.Filters.FilterSoft

/-! # B6: `samp:seed`'s conditional potentials — the elimination formula, the scale `2^S`, `J₀`, and the greedy seed
(P3:2910-2966)

Realizes the remaining sentences of `samp:seed`: "For every seed prefix, its per-column conditional potential is an
explicit rational polynomial in at most `2h` Boolean matrix-entry factors per term. Multiplication by `2^S` makes it an
integer, nonnegative on every column, with the unconditional bound `0 ≤ V_p(z) ≤ J₀ [...]` Every coefficient is
computable exactly by binary Gaussian elimination. The conditional objectives of the two children average to that of
their parent, with this same scale at every prefix" (P3:2915-2926), and its proof "Gaussian elimination gives conditional
probability zero if it is inconsistent, and `2^{−a}` if its remaining rank is `a`. The denominator divides `2^S`. [...]
At a fixed full seed, `‖E_t‖ ≤ 2QN²` [...] Averaging completions, summing `I` states, and multiplying by `2^S` proves
(samp:range)" (P3:2952-2963). The seed is a number `σ < 2^S`, `S = 8ℓ`, its coefficient `a_i` the bits
`[iℓ,(i+1)ℓ)` (the machine layout of `JoinElimination.gen`); a prefix fixes the low `plen` bits. The entry bound used for
`J₀` is `|E(u,v)| ≤ QN²` (so `J₀ = 2^S·|T|·N⁸(QN²)⁸`, logarithm `O(S + log|T| + k + log Q)` as in the paper's
`2^S I(2N)(2QN²)^{2h}`).

Main declarations: `colPot` (the column-`z` potential at a seed number), **`condSum_eq`** (the sum over completions
is `Σ_{t,w,α} (Π_k D_t(c_k;z)) Σ_β (−N²)^{|β|}·condProbGauss(…)` — the explicit polynomial with elimination
coefficients), `condSum_nonneg`, **`condSum_le`** (`≤ 2^{S−plen}·|T|N⁸(QN²)⁸`, so `V_p = 2^{plen}·condSum ≤ J₀`),
**`colPot_int`** (Boolean entries make every value an integer), **`condSum_children`** (children average to the
parent); `seedOfBits` (bit seeds), `uMean_bits` (bit average = seed average), and **`samp_universal_greedy`** (the seed
fixed bit by bit by conditional expectations, `greedy`, gives a list meeting `samp:universal`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.GF
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.Filters Finset

variable (P : SeedParams)

/-- The column-`z` potential `Σ_t tr((E_tE_tᵀ)⁴)` at the sample list of the seed number `σ`. -/
noncomputable def colPot {T : Type} [Fintype T] (Dz : T → Cell P.N → ℝ) (σ : ℕ) : ℝ :=
  ∑ t, Matrix.trace ((errMatrix (Dz t) (P.pos (decodeNat P σ)) * (errMatrix (Dz t) (P.pos (decodeNat P σ))).transpose) ^ 4)

/-- The completion `r` of the prefix `pre` (low `plen` bits fixed). -/
def completion (plen pre r : ℕ) : ℕ := pre % 2 ^ plen + (r <<< plen)

/-- The sum over completions of a prefix. -/
noncomputable def condSum {T : Type} [Fintype T] (Dz : T → Cell P.N → ℝ) (plen pre : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (2 ^ (8 * P.ell - plen)), colPot P Dz (completion plen pre r)

/-- The number whose low `2kh` bits are the bits of a position. -/
noncomputable def cellNum (c : Cell P.N) : ℕ := ofVec (P.cellEquiv.symm c)

/-- The constraints of a subset `β` of the eight positions of a walk term. -/
noncomputable def consOf (α : Fin 8 → Fin P.Q) (c : Fin 8 → Cell P.N) (β : Fin 8 → Bool) : List (ℕ × ℕ) :=
  (List.finRange 8).filterMap fun k => if β k then some ((α k : ℕ), cellNum P (c k)) else none

theorem pos_eq_iff (σ : ℕ) (j : Fin P.Q) (c : Cell P.N) :
    P.pos (decodeNat P σ) j = c ↔
      JoinElimination.proj (2 * P.kh) (JoinElimination.gen P.modulus P.ell 8 σ j) = cellNum P c := by
  rw [pos_eq_gen, proj_eq_iff (2 * P.kh) _ (cellNum P c) (by unfold cellNum; exact ofVec_lt _)]
  constructor
  · intro h b hb
    have hv := congrFun (congrArg P.cellEquiv.symm h) ⟨b, hb⟩
    rw [Equiv.symm_apply_apply] at hv
    unfold cellNum
    rw [testBit_ofVec]
    by_cases hg : (JoinElimination.gen P.modulus P.ell 8 σ j).testBit b
    · rw [hg] at hv
      have : P.cellEquiv.symm c ⟨b, hb⟩ ≠ 0 := by rw [← hv]; decide
      simp [hb, this, hg]
    · simp only [Bool.not_eq_true] at hg
      rw [hg] at hv
      have : ¬ ∃ h : b < 2 * P.kh, P.cellEquiv.symm c ⟨b, h⟩ ≠ 0 := fun ⟨_, h⟩ => h (by rw [← hv]; rfl)
      simp [this, hg]
  · intro h
    rw [← P.cellEquiv.apply_symm_apply c]
    congr 1
    funext b
    have hb := h b b.isLt
    unfold cellNum at hb
    rw [testBit_ofVec] at hb
    by_cases hc : P.cellEquiv.symm c b = 0
    · have : ¬ ∃ h : (b : ℕ) < 2 * P.kh, P.cellEquiv.symm c ⟨b, h⟩ ≠ 0 := fun ⟨_, h⟩ => h hc
      simp only [this, decide_false] at hb
      rw [hb, hc]; rfl
    · have : ∃ h : (b : ℕ) < 2 * P.kh, P.cellEquiv.symm c ⟨b, h⟩ ≠ 0 := ⟨b.isLt, hc⟩
      simp only [this, decide_true] at hb
      rw [hb, zmod2_ne_zero _ hc]; rfl

theorem condProbBrute_fst (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) :
    (JoinElimination.condProbBrute p ℓ twoH k plen pre cons).1 =
      ((Finset.range (2 ^ (twoH * ℓ - plen))).filter fun r => consOk p ℓ twoH k plen pre cons r = true).card := by
  unfold JoinElimination.condProbBrute
  exact length_filter_range _ _

theorem consOk_iff (plen pre : ℕ) (α : Fin 8 → Fin P.Q) (c : Fin 8 → Cell P.N) (β : Fin 8 → Bool) (r : ℕ) :
    consOk P.modulus P.ell 8 (2 * P.kh) plen pre (consOf P α c β) r = true ↔
      ∀ k, β k = true → P.pos (decodeNat P (completion plen pre r)) (α k) = c k := by
  unfold consOk consOf
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    rw [pos_eq_iff]
    have := h ((α k : ℕ), cellNum P (c k)) (by
      rw [List.mem_filterMap]
      exact ⟨k, List.mem_finRange k, by simp [hk]⟩)
    simpa [completion] using this
  · intro h x hx
    rw [List.mem_filterMap] at hx
    obtain ⟨k, _, hk⟩ := hx
    by_cases hb : β k = true
    · simp only [hb, if_true, Option.some.injEq] at hk
      subst hk
      have := (pos_eq_iff P _ (α k) (c k)).mp (h k hb)
      simpa [completion] using this
    · simp [hb] at hk

/-! ## The explicit polynomial with elimination coefficients -/

theorem prod_yc_expand {N : ℕ} (s c : Fin 8 → Cell N) :
    ∏ k, yc N (s k) (c k) = ∑ β : Fin 8 → Bool,
      (-(N : ℝ) ^ 2) ^ (Finset.univ.filter fun k => β k = true).card *
        (if ∀ k, β k = true → s k = c k then 1 else 0) := by
  have h1 : ∀ k, yc N (s k) (c k) = ∑ b : Bool, (if b then -(N : ℝ) ^ 2 * (if s k = c k then 1 else 0) else 1) := by
    intro k; unfold yc; rw [Fintype.sum_bool]; simp only [if_true, Bool.false_eq_true, if_false]; ring
  simp_rw [h1]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl; intro β _
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => β k = true)]
  have hne : ∏ k ∈ Finset.univ.filter (fun k => ¬ β k = true),
      (if β k then -(N : ℝ) ^ 2 * (if s k = c k then 1 else 0) else 1) = 1 := by
    apply Finset.prod_eq_one; intro k hk
    simp only [Finset.mem_filter] at hk
    simp [hk.2]
  have hye : ∏ k ∈ Finset.univ.filter (fun k => β k = true),
      (if β k then -(N : ℝ) ^ 2 * (if s k = c k then 1 else 0) else 1) =
      (-(N : ℝ) ^ 2) ^ (Finset.univ.filter fun k => β k = true).card *
        ∏ k ∈ Finset.univ.filter (fun k => β k = true), (if s k = c k then (1 : ℝ) else 0) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro k hk
    simp only [Finset.mem_filter] at hk
    simp [hk.2]
  rw [hne, mul_one, hye]
  congr 1
  by_cases hall : ∀ k, β k = true → s k = c k
  · rw [if_pos hall]
    apply Finset.prod_eq_one; intro k hk
    simp only [Finset.mem_filter] at hk
    simp [hall k hk.2]
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨k, hk, hsk⟩ := hall
    apply Finset.prod_eq_zero (i := k) (by simp [hk])
    simp [hsk]

/-- A term of the column potential, expanded over walks and sample-index maps. -/
theorem colPot_expand {T : Type} [Fintype T] (Dz : T → Cell P.N → ℝ) (σ : ℕ) :
    colPot P Dz σ = ∑ t, ∑ w : Fin 8 → Fin P.N, ∑ α : Fin 8 → Fin P.Q,
      (∏ k, Dz t (cellOf (by norm_num) w k)) *
        ∏ k, yc P.N (P.pos (decodeNat P σ) (α k)) (cellOf (by norm_num) w k) := by
  unfold colPot
  apply Finset.sum_congr rfl; intro t _
  rw [← walkMoment_eq_trace]
  unfold walkMoment Ecell
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.prod_mul_distrib, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]

/-- **The conditional potential is an explicit polynomial in at most eight Boolean entries per term, with coefficients
computed by Gaussian elimination** (P3:2915-2917, 2950-2957): the sum over the completions of a prefix is
`Σ_{t,w,α} (Π_k D_t(c_k(w);z)) Σ_β (−N²)^{|β|}·(condProbGauss …).1`. -/
theorem condSum_eq {T : Type} [Fintype T] (Dz : T → Cell P.N → ℝ) (plen pre : ℕ) (hplen : plen ≤ 8 * P.ell) :
    condSum P Dz plen pre = ∑ t, ∑ w : Fin 8 → Fin P.N, ∑ α : Fin 8 → Fin P.Q,
      (∏ k, Dz t (cellOf (by norm_num) w k)) * ∑ β : Fin 8 → Bool,
        (-(P.N : ℝ) ^ 2) ^ (Finset.univ.filter fun k => β k = true).card *
          ((JoinElimination.condProbGauss P.modulus P.ell 8 (2 * P.kh) plen pre
            (consOf P α (fun k => cellOf (by norm_num) w k) β)).1 : ℝ) := by
  unfold condSum
  simp_rw [colPot_expand, prod_yc_expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro α _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro β _
  have hcons : ∀ x ∈ consOf P α (fun k => cellOf (by norm_num) w k) β, x.1 < 2 ^ P.ell ∧ x.2 < 2 ^ (2 * P.kh) := by
    intro x hx
    unfold consOf at hx
    rw [List.mem_filterMap] at hx
    obtain ⟨k, _, hk⟩ := hx
    split_ifs at hk
    simp only [Option.some.injEq] at hk
    subst hk
    exact ⟨lt_of_lt_of_le (α k).isLt P.Q_le, ofVec_lt _⟩
  rw [condProbGauss_eq_brute P.modulus P.ell 8 (2 * P.kh) plen pre _ P.cert.2.1 P.one_le_ell P.k_le hplen hcons,
    condProbBrute_fst, Finset.natCast_card_filter, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  congr 2
  by_cases h : ∀ k, β k = true → P.pos (decodeNat P (completion plen pre r)) (α k) = cellOf (by norm_num) w k
  · rw [if_pos h, if_pos ((consOk_iff P plen pre α _ β r).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((consOk_iff P plen pre α _ β r).mp h'))]

/-! ## Nonnegativity, the bound `J₀`, integrality, and the children -/

theorem colPot_nonneg {T : Type} [Fintype T] (Dz : T → Cell P.N → ℝ) (σ : ℕ) : 0 ≤ colPot P Dz σ :=
  Finset.sum_nonneg fun _ _ => trace_pow4_nonneg _

theorem condSum_nonneg {T : Type} [Fintype T] (Dz : T → Cell P.N → ℝ) (plen pre : ℕ) : 0 ≤ condSum P Dz plen pre :=
  Finset.sum_nonneg fun _ _ => colPot_nonneg P Dz _

theorem abs_yc_le {N : ℕ} (hN : 1 ≤ N) (s c : Cell N) : |yc N s c| ≤ (N : ℝ) ^ 2 := by
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast Nat.one_le_pow _ _ hN
  unfold yc
  split_ifs
  · rw [mul_one, abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · rw [mul_zero, sub_zero, abs_one]; exact hN2

theorem abs_errMatrix_le {N Q : ℕ} (hN : 1 ≤ N) (D : Cell N → ℝ) (hD : ∀ c, |D c| ≤ 1) (S : Fin Q → Cell N)
    (u v : Fin N) : |errMatrix D S u v| ≤ (Q : ℝ) * (N : ℝ) ^ 2 := by
  unfold errMatrix Ecell
  rw [abs_mul]
  calc |D (u, v)| * |∑ j, yc N (S j) (u, v)| ≤ 1 * ∑ _j : Fin Q, (N : ℝ) ^ 2 := by
        apply mul_le_mul (hD _) ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => abs_yc_le hN _ _)) (abs_nonneg _) (by norm_num)
    _ = (Q : ℝ) * (N : ℝ) ^ 2 := by simp

/-- The trace moment's unconditional bound: `tr((EEᵀ)⁴) ≤ N⁸(QN²)⁸` (P3:2960-2961). -/
theorem trace_le {N Q : ℕ} (hN : 1 ≤ N) (D : Cell N → ℝ) (hD : ∀ c, |D c| ≤ 1) (S : Fin Q → Cell N) :
    Matrix.trace ((errMatrix D S * (errMatrix D S).transpose) ^ 4) ≤ (N : ℝ) ^ 8 * ((Q : ℝ) * (N : ℝ) ^ 2) ^ 8 := by
  rw [← walkMoment_eq_trace]
  unfold walkMoment
  calc ∑ w : Fin 8 → Fin N, ∏ k, Ecell D S (cellOf (by norm_num) w k)
      ≤ ∑ _w : Fin 8 → Fin N, ((Q : ℝ) * (N : ℝ) ^ 2) ^ 8 := by
        apply Finset.sum_le_sum; intro w _
        refine (le_abs_self _).trans ?_
        rw [Finset.abs_prod]
        calc ∏ k, |Ecell D S (cellOf (by norm_num) w k)| ≤ ∏ _k : Fin 8, (Q : ℝ) * (N : ℝ) ^ 2 :=
              Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun k _ =>
                abs_errMatrix_le hN D hD S (cellOf (by norm_num) w k).1 (cellOf (by norm_num) w k).2
          _ = ((Q : ℝ) * (N : ℝ) ^ 2) ^ 8 := by simp
    _ = (N : ℝ) ^ 8 * ((Q : ℝ) * (N : ℝ) ^ 2) ^ 8 := by simp

/-- **The bound `J₀`** (samp:range, P3:2919-2921): the sum over the `2^{S−plen}` completions is at most
`2^{S−plen}·|T|·N⁸(QN²)⁸`, so `V_p(z) = 2^{plen}·condSum ≤ J₀ = 2^S·|T|·N⁸(QN²)⁸`. -/
theorem condSum_le {T : Type} [Fintype T] (Dz : T → Cell P.N → ℝ) (hD : ∀ t c, |Dz t c| ≤ 1) (plen pre : ℕ) :
    condSum P Dz plen pre ≤
      (2 : ℝ) ^ (8 * P.ell - plen) * (Fintype.card T * ((P.N : ℝ) ^ 8 * ((P.Q : ℝ) * (P.N : ℝ) ^ 2) ^ 8)) := by
  have hN : 1 ≤ P.N := Nat.one_le_two_pow
  unfold condSum
  calc ∑ r ∈ Finset.range (2 ^ (8 * P.ell - plen)), colPot P Dz (completion plen pre r)
      ≤ ∑ _r ∈ Finset.range (2 ^ (8 * P.ell - plen)),
          (Fintype.card T * ((P.N : ℝ) ^ 8 * ((P.Q : ℝ) * (P.N : ℝ) ^ 2) ^ 8)) := by
        apply Finset.sum_le_sum; intro r _
        unfold colPot
        calc ∑ t, Matrix.trace _ ≤ ∑ _t : T, (P.N : ℝ) ^ 8 * ((P.Q : ℝ) * (P.N : ℝ) ^ 2) ^ 8 :=
              Finset.sum_le_sum fun t _ => trace_le hN (Dz t) (hD t) _
          _ = _ := by simp
    _ = _ := by simp

/-! ## The greedy seed -/

/-- The seed number of a bit seed. -/
noncomputable def ofBits {m : ℕ} (s : Fin m → Bool) : ℕ := ofVec fun j => bitF (s j)

theorem testBit_ofBits {m : ℕ} (s : Fin m → Bool) (j : ℕ) (hj : j < m) : (ofBits s).testBit j = s ⟨j, hj⟩ := by
  unfold ofBits
  rw [testBit_ofVec]
  cases h : s ⟨j, hj⟩
  · have : ¬ ∃ h' : j < m, bitF (s ⟨j, h'⟩) ≠ 0 := fun ⟨_, h'⟩ => h' (by rw [h]; rfl)
    simp [this]
  · have : ∃ h' : j < m, bitF (s ⟨j, h'⟩) ≠ 0 := ⟨hj, by rw [h]; decide⟩
    simp [this]

/-- The polynomial seed of a bit seed. -/
noncomputable def seedOfBits (s : Fin (8 * P.ell) → Bool) : P.Seed := decodeNat P (ofBits s)

theorem seedOfBits_injective : Function.Injective (seedOfBits P) := by
  intro s s' h
  funext j
  have hj := j.isLt
  have hi : (j : ℕ) / P.ell < 8 := by
    rw [Nat.div_lt_iff_lt_mul (by have := P.one_le_ell; omega)]; linarith [j.isLt]
  have ht : (j : ℕ) % P.ell < P.ell := Nat.mod_lt _ (by have := P.one_le_ell; omega)
  have hc := congrFun h ⟨(j : ℕ) / P.ell, hi⟩
  unfold seedOfBits decodeNat at hc
  have hcoef := rep_injOn P.modulus P.ell _ _ P.cert.2.1 (seedCoeff_lt _ _ _) (seedCoeff_lt _ _ _) hc
  have hbit := congrArg (fun x => x.testBit ((j : ℕ) % P.ell)) hcoef
  simp only [testBit_seedCoeff _ _ _ _ ht] at hbit
  rw [Nat.div_add_mod' (j : ℕ) P.ell] at hbit
  rw [testBit_ofBits s j hj, testBit_ofBits s' j hj] at hbit
  exact hbit

theorem seedOfBits_bijective : Function.Bijective (seedOfBits P) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨seedOfBits_injective P, ?_⟩
  rw [SeedParams.card_seed, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **The bit average is the seed average.** -/
theorem uMean_bits {Z T : Type} [Fintype Z] [Fintype T] (D : Z → T → Cell P.N → ℝ) :
    uMean (fun s : Fin (8 * P.ell) → Bool => potential D (P.pos (seedOfBits P s))) =
      uMean (fun c : P.Seed => potential D (P.pos c)) := by
  unfold uMean
  rw [Fintype.card_congr (Equiv.ofBijective _ (seedOfBits_bijective P))]
  congr 1
  exact Function.Bijective.sum_comp (seedOfBits_bijective P) (fun c => potential D (P.pos c))

end NearCubicWires.WireExponent3_5.Sampler
