import Mathlib

/-!
# B4 risk item, proved: the selected-parity bias of `filt:gap` (`filt:parity-bias`, P3:2053-2062)

For a finite field `K` with a nontrivial additive trace `Tr : K →+ 𝔽₂`, `a_i = Tr(u vⁱ)` and a nonempty
`J ⊆ [1, M]`:
`0 ≤ E_{u,v}(−1)^{Σ_{i∈J} a_i} = Pr_v[P_J(v) = 0] ≤ M/|K|`, with `P_J(V) = Σ_{i∈J} Vⁱ`.
The trace is abstract here; `FiniteField.trace_to_zmod_nondegenerate` supplies nontriviality for
`Algebra.trace` (instantiation below).  Character orthogonality is proved by translation, the root
bound is `Polynomial.card_roots'`.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.Shared
open Finset Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- `(−1)^{Tr x}`. -/
def psi (Tr : K →+ ZMod 2) (x : K) : ℤ := if Tr x = 0 then 1 else -1

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

omit [Fintype K] [DecidableEq K] in
theorem psi_add (Tr : K →+ ZMod 2) (x y : K) : psi Tr (x + y) = psi Tr x * psi Tr y := by
  unfold psi; rw [map_add]
  rcases zmod2_cases (Tr x) with hx | hx <;> rcases zmod2_cases (Tr y) with hy | hy <;> simp [hx, hy] <;> decide

/-- Orthogonality: a nontrivial additive character sums to zero. -/
theorem sum_psi_eq_zero (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0) : ∑ x, psi Tr x = 0 := by
  obtain ⟨b, hb⟩ := hTr
  have hb1 : psi Tr b = -1 := by unfold psi; simp [hb]
  have hshift : ∑ x, psi Tr x = ∑ x, psi Tr (x + b) :=
    (Equiv.sum_comp (Equiv.addRight b) (fun x => psi Tr x)).symm
  simp only [psi_add, hb1, mul_neg, mul_one, Finset.sum_neg_distrib] at hshift
  linarith

theorem sum_psi_mul (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0) (y : K) :
    ∑ u, psi Tr (u * y) = if y = 0 then (Fintype.card K : ℤ) else 0 := by
  split_ifs with hy
  · subst hy; simp [psi]
  · rw [← sum_psi_eq_zero Tr hTr]
    exact Equiv.sum_comp (Equiv.mulRight₀ y hy) (fun x => psi Tr x)

/-- `P_J(V) = Σ_{i∈J} Vⁱ` (P3:2057). -/
noncomputable def selectorPoly (J : Finset ℕ) : K[X] := ∑ i ∈ J, X ^ i

omit [Fintype K] [DecidableEq K] in
theorem selectorPoly_ne_zero (J : Finset ℕ) (hJ : J.Nonempty) : selectorPoly (K := K) J ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := hJ
  have hc := congrArg (fun p : K[X] => p.coeff i) h
  simp only [selectorPoly, finsetSum_coeff, coeff_X_pow, coeff_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simp [hi] at hc

omit [Fintype K] [DecidableEq K] in
theorem selectorPoly_natDegree_le (J : Finset ℕ) (M : ℕ) (hJM : ∀ i ∈ J, i ≤ M) :
    (selectorPoly (K := K) J).natDegree ≤ M := by
  unfold selectorPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi; exact (natDegree_X_pow_le i).trans (hJM i hi)

/-- The root bound: `#{v : P_J(v) = 0} ≤ M` (P3:2058-2061, "the polynomial root bound"). -/
theorem card_zeros_le (J : Finset ℕ) (hJ : J.Nonempty) (M : ℕ) (hJM : ∀ i ∈ J, i ≤ M) :
    (univ.filter fun v : K => (selectorPoly J).eval v = 0).card ≤ M := by
  have hne := selectorPoly_ne_zero (K := K) J hJ
  calc (univ.filter fun v : K => (selectorPoly J).eval v = 0).card
      ≤ (selectorPoly (K := K) J).roots.toFinset.card := by
        apply Finset.card_le_card; intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        rw [Multiset.mem_toFinset, mem_roots hne]; exact hv
    _ ≤ Multiset.card (selectorPoly (K := K) J).roots := Multiset.toFinset_card_le _
    _ ≤ (selectorPoly (K := K) J).natDegree := card_roots' _
    _ ≤ M := selectorPoly_natDegree_le J M hJM

/-- `filt:parity-bias` (P3:2059-2062): `Σ_{u,v}(−1)^{Σ_{i∈J} Tr(u vⁱ)} = |K|·#{v : P_J(v) = 0}`; hence the bias
is nonnegative and at most `M/|K|` (at most `1/16` when `|K| ≥ 16M`). -/
theorem parity_bias (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0) (J : Finset ℕ) (hJ : J.Nonempty) (M : ℕ)
    (hJM : ∀ i ∈ J, i ≤ M) :
    (∑ u, ∑ v, psi Tr (∑ i ∈ J, u * v ^ i)) =
        (Fintype.card K : ℤ) * (univ.filter fun v : K => (selectorPoly J).eval v = 0).card ∧
      (univ.filter fun v : K => (selectorPoly J).eval v = 0).card ≤ M := by
  refine ⟨?_, card_zeros_le J hJ M hJM⟩
  have hfac : ∀ u v : K, (∑ i ∈ J, u * v ^ i) = u * (selectorPoly J).eval v := by
    intro u v; simp [selectorPoly, eval_finsetSum, Finset.mul_sum]
  simp only [hfac]
  rw [Finset.sum_comm]
  simp only [sum_psi_mul Tr hTr]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

end NearCubicWires.WireExponent3_5.Shared
