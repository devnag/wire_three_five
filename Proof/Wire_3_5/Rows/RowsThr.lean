import Proof.Foundations.SupplierPipeline
import Proof.Wire_3_5.Rows.RowsSym
import Proof.Wire_3_5.Foundations.MaskedExpectation

/-! # Rows: threshold tops — modular rows, radix states at reported counts, and the full error (P3:2543-2719)

Realizes the threshold-top rows (P3:2543-2645) at the level of reported counts, and `row:full-error` (P3:2698-2719).

* `row:threshold-rows` (P3:2543-2561): "`C(x)=Σ_{g∈𝒢}1[L_g(x)=0]` pointwise [...] the Boolean modular rows
  `R_{g,p}=1[L_g ≡ 0 (mod p)]` satisfy `0 ≤ Σ_{g,p}(1/|𝒫|)R_{g,p}(x)−C(x) ≤ n^{−D}`." Here in abstract form: exact
  equation indicators summing to `C`, and prime rows whose per-equation passing fraction exceeds the exact indicator by at
  most `ε` (Theorem 2.5's `PrimeSurrogateCertificate` supplies `ε`; the child sum is `ThresholdRows.selection_sum`).
* The radix (P3:2589-2622): "`a_i=Σ_{d<τ_0}v_{i,d}b_0^d` [...] For each digit and each sign, give residual `Z_i^±` exactly
  `v_{i,d}` labelled copies"; the reported residue `s = Σ_d b_0^d(t_d^+−t_d^−) (mod p)` of the digit lists' reported
  counts; "It agrees with `R_{g,p}` whenever its digit lists are correct" (`thrRow_eq_of_correct`, through the exact
  radix identity `radix_signed_eq`).
* `row:thr-reported`, `row:modular-fourier` (P3:2624-2645): "`R̂_{g,p}=Σ_sH_{g,p,s}1[A_z(u)+B_z(v)+s≡0 (mod p)]`" and
  "`1[A_z(u)+B_z(v)+s≡0 (mod p)] = (1/p)Σ_ℓω^{ℓs}ω^{ℓA_z(u)}ω^{ℓB_z(v)}`. Thus there are `p` rank-one terms per state, with
  coefficient mass exactly one" (`thrReported_separable`, `thrCoeff_mass`).
* `row:full-error` (P3:2713-2719): "the error between its filtered truth expectation and the average of its filtered
  reported rows is at most `n^{−D}+|𝒢|(δ+jξ_reg)`" (`thr_full_error`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.Shared ZMod Finset

/-! ## The modular row at a reported residue -/

section Modular
variable {p : ℕ} [NeZero p]

/-- The reported modular row at the reported residue `s`: `1[A + B + s ≡ 0 (mod p)]` (P3:2626-2629). -/
def thrReported (A B : ℤ) (s : ZMod p) : Bool := decide ((A : ZMod p) + B + s = 0)

/-- **`row:modular-fourier`**: `1[A + B + s ≡ 0] = Σ_ℓ ((1/p)ω^{ℓs})·ω^{ℓA}·ω^{ℓB}`. -/
theorem thrReported_separable (A B : ℤ) (s : ZMod p) :
    bitC (thrReported A B s) = ∑ ℓ : ZMod p, ((p : ℂ)⁻¹ * chi (ℓ * s)) * chi (ℓ * (A : ZMod p)) * chi (ℓ * (B : ZMod p)) := by
  have h := indicator_eq_sum ((A : ZMod p) + (B : ZMod p) + s)
  unfold thrReported bitC
  rw [show (if decide ((A : ZMod p) + (B : ZMod p) + s = 0) = true then (1 : ℂ) else 0) =
    if (A : ZMod p) + (B : ZMod p) + s = 0 then 1 else 0 by simp, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [show ℓ * ((A : ZMod p) + (B : ZMod p) + s) = ℓ * s + ℓ * (A : ZMod p) + ℓ * (B : ZMod p) by ring, chi_add,
    chi_add]
  ring

/-- "coefficient mass exactly one" per state (P3:2639-2640). -/
theorem thrCoeff_mass (s : ZMod p) : ∑ ℓ : ZMod p, ‖(p : ℂ)⁻¹ * chi (ℓ * s)‖ = 1 := by
  simp only [norm_mul, norm_chi, mul_one, norm_inv, Complex.norm_natCast, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  have : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp

end Modular

/-! ## The radix at reported digit states (P3:2589-2622) -/

section Radix
variable {ι : Type} [Fintype ι] {τ₀ K : ℕ}

/-- The signed digit populations `T_d^± = Σ_i v_{i,d}Z_i^±` (each residual has `v_{i,d}` labelled copies, P3:2596-2599). -/
def digitCount (v : ι → Fin τ₀ → ℕ) (Z : ι → Bool) (d : Fin τ₀) : ℕ := ∑ i, v i d * (Z i).toNat

/-- **The exact signed radix identity**: `Σ_i a_i(Z_i^+ − Z_i^−) = Σ_d b_0^d(T_d^+ − T_d^−)` when `a_i = Σ_d v_{i,d}b_0^d`. -/
theorem radix_signed_eq (b0 : ℕ) (a : ι → ℕ) (v : ι → Fin τ₀ → ℕ) (ha : ∀ i, a i = ∑ d, v i d * b0 ^ (d : ℕ))
    (Zp Zm : ι → Bool) :
    (∑ i, (a i : ℤ) * (((Zp i).toNat : ℤ) - (Zm i).toNat)) =
      ∑ d : Fin τ₀, (b0 : ℤ) ^ (d : ℕ) * ((digitCount v Zp d : ℤ) - digitCount v Zm d) := by
  calc (∑ i, (a i : ℤ) * (((Zp i).toNat : ℤ) - (Zm i).toNat))
      = ∑ i, ∑ d : Fin τ₀, (v i d : ℤ) * (b0 : ℤ) ^ (d : ℕ) * (((Zp i).toNat : ℤ) - (Zm i).toNat) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ha i]; push_cast; rw [Finset.sum_mul]
    _ = ∑ d : Fin τ₀, ∑ i, (v i d : ℤ) * (b0 : ℤ) ^ (d : ℕ) * (((Zp i).toNat : ℤ) - (Zm i).toNat) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun d _ => ?_
        simp only [digitCount]
        push_cast
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The residue `Σ_d b_0^d(t_d^+ − t_d^−) (mod p)` of a signed digit tuple. -/
def tupleResidue (p b0 : ℕ) (tp tm : Fin τ₀ → ℕ) : ZMod p :=
  ((∑ d : Fin τ₀, (b0 : ℤ) ^ (d : ℕ) * ((tp d : ℤ) - tm d) : ℤ) : ZMod p)

/-- **`radixStates`, (row:radix)** (P3:2608-2614): from the repaired digit state indicators `P_{d,±,t}`,
`H_{g,p,s} = Σ_{(t_d^+,t_d^−) : Σ_d b_0^d(t_d^+−t_d^−) ≡ s} Π_d P_{d,+,t_d^+}P_{d,−,t_d^−}`, an integer sum. -/
def radixState (p b0 : ℕ) (Pp Pm : Fin τ₀ → Fin (K + 1) → Bool) (s : ZMod p) : ℕ :=
  ∑ tup : Fin τ₀ → Fin (K + 1) × Fin (K + 1),
    if tupleResidue p b0 (fun d => ((tup d).1 : ℕ)) (fun d => ((tup d).2 : ℕ)) = s then
      ∏ d, (Pp d (tup d).1).toNat * (Pm d (tup d).2).toNat
    else 0

/-- "Precisely one digit tuple is active, even when it is incorrect" (P3:2615-2617): when every digit list is one-hot
at its reported state `(t_d^+, t_d^−)`, `H_{g,p,s} = 1[s = Σ_d b_0^d(t_d^+ − t_d^−)]`. -/
theorem radixState_of_oneHot (p b0 : ℕ) (Pp Pm : Fin τ₀ → Fin (K + 1) → Bool) (tp tm : Fin τ₀ → Fin (K + 1))
    (hp : ∀ d t, Pp d t = decide (t = tp d)) (hm : ∀ d t, Pm d t = decide (t = tm d)) (s : ZMod p) :
    radixState p b0 Pp Pm s =
      if tupleResidue p b0 (fun d => (tp d : ℕ)) (fun d => (tm d : ℕ)) = s then 1 else 0 := by
  unfold radixState
  rw [Finset.sum_eq_single (fun d => (tp d, tm d))]
  · simp [hp, hm]
  · intro tup _ hne
    obtain ⟨d, hd⟩ : ∃ d, tup d ≠ (tp d, tm d) := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hz : (Pp d (tup d).1).toNat * (Pm d (tup d).2).toNat = 0 := by
      rw [hp, hm]
      by_cases h1 : (tup d).1 = tp d
      · have h2 : (tup d).2 ≠ tm d := fun h2 => hd (Prod.ext h1 h2)
        simp [h2]
      · simp [h1]
    split_ifs
    · exact Finset.prod_eq_zero (Finset.mem_univ d) hz
    · rfl
  · simp

end Radix

/-! ## Means -/

section Means
variable {Ω : Type} [Fintype Ω]

theorem uMean_sub' (f g : Ω → ℝ) : uMean (fun x => f x - g x) = uMean f - uMean g := by
  unfold uMean; rw [Finset.sum_sub_distrib, sub_div]

theorem uMean_const_mul (c : ℝ) (f : Ω → ℝ) : uMean (fun x => c * f x) = c * uMean f := by
  unfold uMean; rw [← Finset.mul_sum, mul_div_assoc]

theorem uMean_finsum {G : Type} [Fintype G] (f : G → Ω → ℝ) :
    uMean (fun x => ∑ g, f g x) = ∑ g, uMean (f g) := by
  unfold uMean; rw [Finset.sum_comm, Finset.sum_div]

theorem abs_uMean_le (f : Ω → ℝ) : |uMean f| ≤ uMean (fun x => |f x|) := by
  unfold uMean
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

theorem uMean_le_const (f : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c) (hf : ∀ x, f x ≤ c) : uMean f ≤ c := by
  unfold uMean
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]; exact hc
  · rw [div_le_iff₀ (Nat.cast_pos.mpr hpos)]
    calc ∑ x, f x ≤ ∑ _x : Ω, c := Finset.sum_le_sum fun x _ => hf x
      _ = c * Fintype.card Ω := by simp [mul_comm]

theorem uMean_swap' {Pr : Type} [Fintype Pr] (f : Pr → Ω → ℝ) :
    uMean (fun p => uMean (f p)) = uMean (fun x => uMean (fun p => f p x)) := by
  unfold uMean
  rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm, div_div, div_div, mul_comm (Fintype.card Ω : ℝ)]

end Means

/-! ## The prime rows by reuse (P3:2543-2585) -/

section Prime
open NearCubicWires.SupplierPipeline

end Prime

/-! ## `row:masked-error` and `row:full-error` (P3:2680-2719) -/

section MaskedError

end MaskedError

section FullError
variable {Ω G Pr : Type} [Fintype Ω] [Fintype G] [Fintype Pr]

/-- **`row:full-error`** (P3:2713-2719, proof P3:2711-2719): prime rows `R_{g,p}` with the pointwise prime error
`0 ≤ Σ_{g,p}(1/|𝒫|)R_{g,p} − C ≤ ε` (row:prime-error), and reported rows `R̂_{g,p}` with masked error at most `δ'`
against `R_{g,p}`, give `|E[M·C] − Σ_g E_p E[M·R̂_{g,p}]| ≤ ε + |𝒢|·δ'` for every mask `M` ("add the pointwise prime
error and sum the row errors with coefficients `1/|𝒫|`. Their total mass is `|𝒢|`"). -/
theorem thr_full_error (M C : Ω → Bool) (R Rhat : G → Pr → Ω → Bool) (ε δ' : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ')
    (hprime : ∀ x, bitR (C x) ≤ ∑ g, uMean (fun p => bitR (R g p x)) ∧
      ∑ g, uMean (fun p => bitR (R g p x)) ≤ bitR (C x) + ε)
    (hrow : ∀ g p, uMean (fun x => bitR (M x) * |bitR (Rhat g p x) - bitR (R g p x)|) ≤ δ') :
    |maskedMean M (fun x => bitR (C x)) -
        ∑ g, uMean (fun p => maskedMean M (fun x => bitR (Rhat g p x)))| ≤ ε + Fintype.card G * δ' := by
  set Bv := ∑ g, uMean (fun p => maskedMean M (fun x => bitR (R g p x)))
  have hBv : Bv = uMean (fun x => bitR (M x) * ∑ g, uMean (fun p => bitR (R g p x))) := by
    simp only [Bv, maskedMean, Finset.mul_sum]
    rw [uMean_finsum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [uMean_swap' (fun p x => bitR (M x) * bitR (R g p x))]
    congr 1; funext x; rw [uMean_const_mul]
  have hAB : |maskedMean M (fun x => bitR (C x)) - Bv| ≤ ε := by
    rw [hBv]
    unfold maskedMean
    rw [← uMean_sub']
    refine (abs_uMean_le _).trans (uMean_le_const _ ε hε fun x => ?_)
    have hm0 := bitR_nonneg (M x)
    have hm1 := bitR_le_one (M x)
    obtain ⟨h1, h2⟩ := hprime x
    rw [← mul_sub, abs_mul, abs_of_nonneg hm0, abs_sub_comm, abs_of_nonneg (by linarith)]
    nlinarith
  have hBC : |Bv - ∑ g, uMean (fun p => maskedMean M (fun x => bitR (Rhat g p x)))| ≤ Fintype.card G * δ' := by
    simp only [Bv]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ g, |uMean (fun p => maskedMean M (fun x => bitR (R g p x))) -
          uMean (fun p => maskedMean M (fun x => bitR (Rhat g p x)))| ≤ ∑ _g : G, δ' := by
          refine Finset.sum_le_sum fun g _ => ?_
          rw [← uMean_sub']
          refine (abs_uMean_le _).trans (uMean_le_const _ δ' hδ fun p => ?_)
          unfold maskedMean
          rw [← uMean_sub']
          refine (abs_uMean_le _).trans ((le_of_eq ?_).trans (hrow g p))
          congr 1; funext x
          rw [← mul_sub, abs_mul, abs_of_nonneg (bitR_nonneg _), abs_sub_comm]
      _ = Fintype.card G * δ' := by simp
  calc _ = |(maskedMean M (fun x => bitR (C x)) - Bv) +
          (Bv - ∑ g, uMean (fun p => maskedMean M (fun x => bitR (Rhat g p x))))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε + Fintype.card G * δ' := add_le_add hAB hBC

end FullError

end NearCubicWires.WireExponent3_5.Rows
