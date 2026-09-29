import Proof.Wire_3_5.Sampler.SamplerUniform

/-! # Rows: the finite Fourier expansions and the sampler interface (P3:2504-2539, 2627-2645, 2721-2775)

Realizes the analysis identities of the row construction and the interface lemma `row:sampler-interface`
(P3:2721-2757): "There is a fixed polynomial bound `𝔐` such that replacing each live-pair average by this common sample
changes the average filtered reported observable by at most `𝔐η` [...] For any complex vectors `a,b` with entries of
modulus at most one [...] `|aᵀDb/N² − (1/Q)Σ_ℓ a_{U_ℓ}b_{V_ℓ}D[U_ℓ,V_ℓ]| ≤ ‖E_D‖_op/(QN)` [...] Apply this bound to the
Fourier expansions (row:fourier) and (row:modular-fourier), and sum absolute coefficient weights, then states."

The Fourier identities (P3:2518-2529, 2633-2638): "`f_j(s) = Σ_{ℓ} f̂_j(ℓ)ω_j^{ℓs}`" and
"`1[A_z(u)+B_z(v)+s ≡ 0 (mod p)] = (1/p)Σ_ℓ ω^{ℓs}ω^{ℓA_z(u)}ω^{ℓB_z(v)}`", with the mass bound `|f̂_j(ℓ)| ≤ 1` in place of
Parseval (F5: the per-state mass is `P_j`, not `√P_j`, still polynomial).

Main quantities: the character `chi` (`ω^x` on `ZMod P`), `fourierCoeff` (`f̂`), and a separable row `Σ_t H_t(u,v)·Σ_λ
c(t,λ)a_λ(u)b_λ(v)`. Results: `fourier_inversion`, `norm_fourierCoeff_le`, `indicator_eq_sum` (the modular indicator),
and **`separable_sample_error`**: for every sample list and every family of bounded selectors, the sampled average of
a separable filtered row errs by at most `(Σ_t Σ_λ |c(t,λ)|)·max_t ‖E_{D_t}‖/(QN)` with `D_t = G·H_t` (`𝔐` is the total
coefficient mass). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.Shared ZMod Finset Matrix
open scoped Matrix.Norms.L2Operator

section Fourier
variable {P : ℕ} [NeZero P]

/-- The additive character `x ↦ ω^x = exp(2πix/P)` on `ZMod P`. -/
noncomputable def chi (x : ZMod P) : ℂ := stdAddChar x

theorem norm_chi (x : ZMod P) : ‖chi x‖ = 1 := by simp [chi]

theorem chi_add (x y : ZMod P) : chi (x + y) = chi x * chi y := by
  simp only [chi]; exact AddChar.map_add_eq_mul _ x y

theorem chi_zero : chi (0 : ZMod P) = 1 := by simp [chi]

/-- The Fourier coefficient `f̂(ℓ) = (1/P)Σ_t f(t)ω^{−ℓt}` (P3:2514-2516). -/
noncomputable def fourierCoeff (f : ZMod P → ℂ) (ℓ : ZMod P) : ℂ :=
  (P : ℂ)⁻¹ * ∑ t : ZMod P, chi (-(t * ℓ)) * f t

/-- **Fourier inversion** (P3:2518-2520): `f(s) = Σ_ℓ f̂(ℓ)ω^{ℓs}`. -/
theorem fourier_inversion (f : ZMod P → ℂ) (s : ZMod P) : f s = ∑ ℓ : ZMod P, fourierCoeff f ℓ * chi (ℓ * s) := by
  have h := congrFun (LinearEquiv.symm_apply_apply (dft (N := P) (E := ℂ)) f) s
  rw [invDFT_apply] at h
  rw [← h, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [dft_apply]
  simp only [fourierCoeff, chi, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- **The coefficient bound** (F5): a function bounded by one has Fourier coefficients bounded by one, so the
total mass is at most `P`. -/
theorem norm_fourierCoeff_le (f : ZMod P → ℂ) (hf : ∀ t, ‖f t‖ ≤ 1) (ℓ : ZMod P) : ‖fourierCoeff f ℓ‖ ≤ 1 := by
  unfold fourierCoeff
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hP : (0 : ℝ) < P := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne P))
  rw [inv_mul_le_iff₀ hP, mul_one]
  calc ‖∑ t : ZMod P, chi (-(t * ℓ)) * f t‖ ≤ ∑ t : ZMod P, ‖chi (-(t * ℓ)) * f t‖ := norm_sum_le _ _
    _ ≤ ∑ _t : ZMod P, (1 : ℝ) := Finset.sum_le_sum fun t _ => by rw [norm_mul, norm_chi, one_mul]; exact hf t
    _ = P := by simp [ZMod.card]

/-- **The modular indicator** (P3:2633-2638): `1[m = 0] = (1/P)Σ_ℓ ω^{ℓm}` on `ZMod P`. -/
theorem indicator_eq_sum (m : ZMod P) : (if m = 0 then (1 : ℂ) else 0) = (P : ℂ)⁻¹ * ∑ ℓ : ZMod P, chi (ℓ * m) := by
  have hP : (P : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne P
  split_ifs with hm
  · subst hm
    simp only [mul_zero, chi_zero, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    field_simp
  · have hprim := isPrimitive_stdAddChar P
    have hne : (stdAddChar (N := P)).mulShift m ≠ 1 := hprim hm
    have hsum : ∑ ℓ : ZMod P, (stdAddChar (N := P)).mulShift m ℓ = 0 := AddChar.sum_eq_zero_of_ne_one hne
    simp only [AddChar.mulShift_apply] at hsum
    simp only [chi, mul_comm _ m]
    rw [hsum, mul_zero]

end Fourier

/-! ## The sampler interface for separable rows (P3:2721-2757) -/

section Interface
variable {N Q : ℕ} {T Λ : Type} [Fintype T] [Fintype Λ]

/-- The filtered state matrices `D_t = G·H_t` (`row:matrix`, P3:2658-2660). -/
def stateMatrix (G : Fin N → Fin N → ℂ) (H : T → Fin N → Fin N → ℂ) (t : T) : Fin N → Fin N → ℂ :=
  fun u v => G u v * H t u v

/-- A separable filtered row: `G(u,v)·Σ_t H_t(u,v)·Σ_λ c(t,λ)a_λ(u)b_λ(v)` (the reported row after its Fourier
expansion, P3:2492-2494, 2632-2638). -/
def separableRow (G : Fin N → Fin N → ℂ) (H : T → Fin N → Fin N → ℂ) (c : T → Λ → ℂ) (a b : Λ → Fin N → ℂ)
    (u v : Fin N) : ℂ :=
  G u v * ∑ t, H t u v * ∑ lam, c t lam * a lam u * b lam v

/-- The live-pair sum of a separable row, per state and frequency: `Σ_t Σ_λ c(t,λ)·aᵀD_tb`. -/
theorem live_sum_eq (G : Fin N → Fin N → ℂ) (H : T → Fin N → Fin N → ℂ) (c : T → Λ → ℂ)
    (a b : Λ → Fin N → ℂ) :
    (∑ u, ∑ v, separableRow G H c a b u v) =
      ∑ t, ∑ lam, c t lam * ∑ u, a lam u * (Matrix.of (stateMatrix G H t) *ᵥ b lam) u := by
  have hL : ∀ u v, separableRow G H c a b u v =
      ∑ t, ∑ lam, c t lam * (a lam u * (G u v * H t u v * b lam v)) := by
    intro u v
    simp only [separableRow, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun lam _ => by ring
  have hR : ∀ t lam, c t lam * ∑ u, a lam u * (Matrix.of (stateMatrix G H t) *ᵥ b lam) u =
      ∑ u, ∑ v, c t lam * (a lam u * (G u v * H t u v * b lam v)) := by
    intro t lam
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, stateMatrix, Finset.mul_sum]
  simp only [hL, hR]
  calc ∑ u, ∑ v, ∑ t, ∑ lam, c t lam * (a lam u * (G u v * H t u v * b lam v))
      = ∑ u, ∑ t, ∑ v, ∑ lam, c t lam * (a lam u * (G u v * H t u v * b lam v)) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ t, ∑ u, ∑ v, ∑ lam, c t lam * (a lam u * (G u v * H t u v * b lam v)) := Finset.sum_comm
    _ = ∑ t, ∑ u, ∑ lam, ∑ v, c t lam * (a lam u * (G u v * H t u v * b lam v)) :=
        Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ t, ∑ lam, ∑ u, ∑ v, c t lam * (a lam u * (G u v * H t u v * b lam v)) :=
        Finset.sum_congr rfl fun t _ => Finset.sum_comm

/-- The sampled sum of a separable row, per state and frequency. -/
theorem sample_sum_eq (G : Fin N → Fin N → ℂ) (H : T → Fin N → Fin N → ℂ) (c : T → Λ → ℂ)
    (a b : Λ → Fin N → ℂ) (S : Fin Q → Fin N × Fin N) :
    (∑ j, separableRow G H c a b (S j).1 (S j).2) =
      ∑ t, ∑ lam, c t lam * ∑ j, a lam (S j).1 * b lam (S j).2 * stateMatrix G H t (S j).1 (S j).2 := by
  simp only [separableRow, stateMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun lam _ => Finset.sum_congr rfl fun j _ => by ring

/-- **`row:sampler-interface`** (P3:2721-2757): for every sample list `S` and all selectors bounded by one (chosen
before or after the sample), the sampled average of a separable filtered row differs from its live-pair average by at
most `𝔐·max_t‖E_{D_t}‖/(QN)`, with `𝔐 = Σ_t Σ_λ |c(t,λ)|`. -/
theorem separable_sample_error (hN : 0 < N) (hQ : 0 < Q) (G : Fin N → Fin N → ℂ) (H : T → Fin N → Fin N → ℂ)
    (c : T → Λ → ℂ) (a b : Λ → Fin N → ℂ) (ha : ∀ lam i, ‖a lam i‖ ≤ 1) (hb : ∀ lam i, ‖b lam i‖ ≤ 1)
    (S : Fin Q → Fin N × Fin N) (η : ℝ) (hη : ∀ t, ‖sampleError (stateMatrix G H t) S‖ / (Q * N) ≤ η) :
    ‖(∑ u, ∑ v, separableRow G H c a b u v) / (N : ℂ) ^ 2 -
        (∑ j, separableRow G H c a b (S j).1 (S j).2) / (Q : ℂ)‖ ≤
      (∑ t, ∑ lam, ‖c t lam‖) * η := by
  rw [live_sum_eq, sample_sum_eq, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun lam _ => ?_
  have herr := sample_estimate_error hN hQ (stateMatrix G H t) S (a lam) (b lam) (ha lam) (hb lam)
  have heq : c t lam * (∑ u, a lam u * (Matrix.of (stateMatrix G H t) *ᵥ b lam) u) / (N : ℂ) ^ 2 -
      c t lam * (∑ j, a lam (S j).1 * b lam (S j).2 * stateMatrix G H t (S j).1 (S j).2) / (Q : ℂ) =
      c t lam * ((∑ u, a lam u * (Matrix.of (stateMatrix G H t) *ᵥ b lam) u) / (N : ℂ) ^ 2 -
        (∑ j, a lam (S j).1 * b lam (S j).2 * stateMatrix G H t (S j).1 (S j).2) / (Q : ℂ)) := by ring
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_left (herr.trans (hη t)) (norm_nonneg _)

end Interface

end NearCubicWires.WireExponent3_5.Rows
