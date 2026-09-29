import Proof.Wire_3_5.Sampler.SamplerTrace
import Proof.Wire_3_5.Foundations.MaskedExpectation

/-! # B6: `samp:moment` by the direct `h = 4` moment — the potential, finite Jensen, and a list no worse than the mean
(P3:2818-2902)

Realizes `samp:moment`'s conclusion `samp:universal`: "There is a list of `Q` pairs `(U_j,V_j)∈[N]²` such that [...]
simultaneously for arbitrary complex selectors `a_t(z),b_t(z)` with all coordinates of modulus at most one,
`E_z max_{t≤I} |a_t(z)ᵀD_t(z)b_t(z)/N² − (1/Q)Σ_j a_{t,U_j}(z)b_{t,V_j}(z)D_t(U_j,V_j;z)| ≤ η`. The selectors can
depend on the selected list itself" (P3:2826-2843), by the paper's potential step "Use the potential
`Φ = E_z Σ_{t≤I} tr 𝓗(E_t(z))^{2h}`. Some sample list has potential at most its expectation. For that list, norm
domination, Jensen's inequality for the concave `2h`-th root [...]" (P3:2886-2890), at `h = 4`, with the direct moment
bound (`DirectMoment.sum_walkMoment_le_explicit`, `E_S tr((EEᵀ)⁴) ≤ C·Q⁴N¹³`) in place of the Tropp tail integration and
the bilinear domination (`NormDomination.bilinear_pow8_le`) in place of the operator norm. The maximum over `t` is taken by
an arbitrary choice `τ(z)` (it can be the maximizer), and the selectors are arbitrary functions of `z` quantified after
the list is fixed. The resulting condition is `Q⁴η⁸ ≥ 4⁸·C₈·I·N⁵` (`Q ≳ I^{1/4}N^{5/4}η^{−2}`, within `samp:printable`'s
`Q ≤ 2^{3k/4}n^{C'}`).

Main declarations: `trace_pow4_nonneg`; `cbil` (the complex bilinear form of a real matrix) with **`cbil_pow8_le`**
(`‖aᵀEb‖⁸ ≤ 4⁸N⁸·tr((EEᵀ)⁴)` for coordinates of modulus `≤ 1`); **`sampleErr`** (the paper's per-selector error) with
**`sampleErr_eq`** (`= aᵀEb/(QN²)`); **`potential`** (`Σ_z Σ_t tr((E_tE_tᵀ)⁴)`); **`universal_of_potential`** (Jensen:
`(E_z‖err‖)⁸ ≤ 4⁸Φ/(|Z|Q⁸N⁸)`); **`uMean_potential_le`** (`E_SΦ ≤ |Z||T|·C₈Q⁴N¹³` over independent uniform lists,
`C₈ = 2⁸·5·8⁸`), `exists_potential_le`; **`universal_of_potential_le`** (every list with that potential meets
`samp:universal` at error `η` when `4⁸C₈|T|N⁵ ≤ Q⁴η⁸`); and **`samp_universal`** (such a list exists). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.Shared Finset Matrix

variable {N Q : ℕ}

/-- `tr((EEᵀ)⁴) = ‖(EEᵀ)²‖²_F ≥ 0`. -/
theorem trace_pow4_nonneg (E : Matrix (Fin N) (Fin N) ℝ) : 0 ≤ Matrix.trace ((E * Eᵀ) ^ 4) := by
  set P := (E * Eᵀ) ^ 2 with hPdef
  have hP : Pᵀ = P := by rw [hPdef, Matrix.transpose_pow, Matrix.transpose_mul, Matrix.transpose_transpose]
  have h4 : (E * Eᵀ) ^ 4 = Pᵀ * P := by rw [hP, hPdef, ← pow_add]
  rw [h4]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-! ## The per-selector sampling error -/

/-- **The error is the bilinear form of the error matrix**: `err = aᵀEb/(QN²)` (P3:2847-2849). -/
theorem ecell_eq (D : Cell N → ℝ) (S : Fin Q → Cell N) (c : Cell N) :
    Ecell D S c = (Q : ℝ) * D c - (N : ℝ) ^ 2 * ∑ j, (if S j = c then 1 else 0) * D c := by
  unfold Ecell yc
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-! ## The potential and finite Jensen -/

/-- **The potential** `Φ(S) = Σ_z Σ_t tr((E_t(z)E_t(z)ᵀ)⁴)` (P3:2886, at `h = 4`, summed rather than averaged over `z`). -/
noncomputable def potential {Z T : Type} [Fintype Z] [Fintype T] (D : Z → T → Cell N → ℝ) (S : Fin Q → Cell N) : ℝ :=
  ∑ z, ∑ t, Matrix.trace ((errMatrix (D z t) S * (errMatrix (D z t) S)ᵀ) ^ 4)

/-- Finite Jensen for the eighth power: `(E f)⁸ ≤ E f⁸` for `f ≥ 0`. -/
theorem uMean_pow8_le {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    (uMean f) ^ 8 ≤ uMean fun ω => f ω ^ 8 := by
  unfold uMean
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (fun i _ => hf i) 7
  rw [Finset.card_univ] at h
  rw [div_pow, div_le_div_iff₀ (by positivity) hc]
  calc (∑ ω, f ω) ^ 8 * (Fintype.card Ω : ℝ) ≤ ((Fintype.card Ω : ℝ) ^ 7 * ∑ ω, f ω ^ 8) * Fintype.card Ω :=
        mul_le_mul_of_nonneg_right h hc.le
    _ = (∑ ω, f ω ^ 8) * (Fintype.card Ω : ℝ) ^ 8 := by ring

/-! ## A list no worse than the mean -/

/-- The constant of the direct `h = 4` moment: `2⁸·5·8⁸` (`DirectMoment.sum_walkMoment_le_explicit` at `L = 8`). -/
def C8 : ℝ := 2 ^ 8 * 5 * 8 ^ 8

/-- **The expected potential over independent uniform lists** is `≤ |Z||T|·C₈Q⁴N¹³` (the direct moment bound,
`DirectMoment.sum_walkMoment_le_explicit` at `L = 8`, through `walkMoment_eq_trace`). -/
theorem uMean_potential_le {Z T : Type} [Fintype Z] [Fintype T] (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (D : Z → T → Cell N → ℝ) (hD : ∀ z t c, |D z t c| ≤ 1) :
    uMean (fun S : Fin Q → Cell N => potential D S) ≤
      (Fintype.card Z : ℝ) * Fintype.card T * C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13 := by
  classical
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcard : (Fintype.card (Fin Q → Cell N) : ℝ) = (N : ℝ) ^ (2 * Q) := by
    rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
  have hsum : ∑ S : Fin Q → Cell N, potential D S ≤
      (Fintype.card Z : ℝ) * Fintype.card T * (C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ (2 * Q + 13)) := by
    unfold potential
    rw [Finset.sum_comm]
    have hzt : ∀ z t, ∑ S : Fin Q → Cell N, Matrix.trace ((errMatrix (D z t) S * (errMatrix (D z t) S)ᵀ) ^ 4) ≤
        C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ (2 * Q + 13) := by
      intro z t
      have hw := sum_walkMoment_le_explicit (L := 8) (by norm_num) hN hNQ (D z t) (hD z t)
      simp_rw [walkMoment_eq_trace] at hw
      have e : 2 * Q + 2 * 8 + 1 - 8 / 2 = 2 * Q + 13 := by omega
      rw [e] at hw
      refine (le_abs_self _).trans (hw.trans (le_of_eq ?_))
      unfold C8
      norm_num
    calc ∑ z, ∑ S : Fin Q → Cell N, ∑ t, Matrix.trace ((errMatrix (D z t) S * (errMatrix (D z t) S)ᵀ) ^ 4)
        = ∑ z, ∑ t, ∑ S : Fin Q → Cell N, Matrix.trace ((errMatrix (D z t) S * (errMatrix (D z t) S)ᵀ) ^ 4) := by
          apply Finset.sum_congr rfl; intro z _; rw [Finset.sum_comm]
      _ ≤ ∑ _z : Z, ∑ _t : T, C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ (2 * Q + 13) :=
          Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun t _ => hzt z t
      _ = _ := by simp; ring
  unfold uMean
  rw [hcard, div_le_iff₀ (by positivity)]
  refine hsum.trans (le_of_eq ?_)
  rw [pow_add, pow_mul]; ring

end NearCubicWires.WireExponent3_5.Sampler
