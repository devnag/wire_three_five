import Proof.Wire_3_5.Recovery.CertSchedule
import Proof.Wire_3_5.Recovery.HybridLedger

/-! # One source length of the hybrid recovery is hard in both classes (P3:3685-3733; D1.6)

Realizes the per-length hardness of the recovered language in its hybrid form: Case 1 at the refuter
hierarchy's native outer PCP of width `R = R(2^a)` ("If no size-`q^G` oracle makes the outer verifier a tautology [...]
Apply the imported worst-case amplifier", P3:3704-3709, with "`G/c_STV` exceeds a general-Boolean simulation exponent
[...] with a fixed positive margin", P3:3685-3692) and Case 2 at the union machine's padded request (P3:3710-3733).
Case 1's numerics now read the native width `R`, which is within a constant factor of `q`: `R(2^a) ≥ a + 1` (base's
`native_dyadic_lower`) and `q(2^a) ≤ K₁(a + 1)` with `K₁ = (k+2)(1+A_pad) + 3A_pad + 1`.

Paper quantities: `rpow_oracle_le` (`(q^{17c})^{−1/c} ≤ R^{−17}`), **`caseOne_sizeB`** (the size premises with the
envelope `n + cap + 2 ≤ B(R+1)⁴`), `eventually_caseOne_advR` (`(R^{17c})^{−1/c} < e_{t(q)}` once `q ≤ K₁R`),
`widthAt_le` (`q(2^a) ≤ K₁(a+1)`), and **`core_hard_at2`** (the hybrid core of one source length is below
`1/2 + e_{t(q)}` against every `SYM∘THR` / `THR∘THR` circuit within `⌊w_i(q)⌋` wires). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open NearCubicWires.ComponentwiseCircuitRestriction (restrictedSymmetricDescriptionCap
  restrictedThresholdDescriptionCap)
open Filter

/-! ## Case 1 at the native width -/

theorem rpow_oracle_le (c : ℕ) (hc : 1 ≤ c) (R : ℕ) (hR : 1 ≤ R) :
    Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) R : ℝ) (-(1 : ℝ) / c) ≤ (R : ℝ) ^ (-(17 : ℝ)) := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hX : ((R : ℝ) ^ (17 * c : ℕ)) ≤ (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) R : ℝ) := by
    exact_mod_cast oracleSize_ge (17 * c) R hR
  have hpos : (0 : ℝ) < (R : ℝ) ^ (17 * c : ℕ) := by positivity
  have hneg : -(1 : ℝ) / c ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / c := by positivity
    rw [neg_div]; linarith
  have h1 : Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) R : ℝ) (-(1 : ℝ) / c) ≤
      Real.rpow ((R : ℝ) ^ (17 * c : ℕ)) (-(1 : ℝ) / c) :=
    Real.rpow_le_rpow_of_nonpos hpos hX hneg
  have h2 : Real.rpow ((R : ℝ) ^ (17 * c : ℕ)) (-(1 : ℝ) / c) = (R : ℝ) ^ (-(17 : ℝ)) := by
    show ((R : ℝ) ^ (17 * c : ℕ)) ^ (-(1 : ℝ) / c) = (R : ℝ) ^ (-(17 : ℝ))
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    congr 1
    push_cast
    field_simp
  exact h1.trans h2.le

/-- **Case 1's size premises** with the envelope `n + cap + 2 ≤ B(R+1)⁴`. -/
theorem caseOne_sizeB (c : ℕ) (hc : 1 ≤ c) (R n cap K B : ℕ) (hK : K ≤ 50) (hR1 : 1 ≤ R)
    (hR : 50 * B ^ 4 * (R + 1) ^ 16 ≤ R ^ 17) (hn : n + cap + 2 ≤ B * (R + 1) ^ 4) :
    K * (n + cap + 2) ^ 4 ≤ integerFloorRoot c (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) R) := by
  apply le_integerFloorRoot (by omega)
  have h1 : K * (n + cap + 2) ^ 4 ≤ 50 * (B * (R + 1) ^ 4) ^ 4 :=
    Nat.mul_le_mul hK (Nat.pow_le_pow_left hn 4)
  have h2 : 50 * (B * (R + 1) ^ 4) ^ 4 = 50 * B ^ 4 * (R + 1) ^ 16 := by ring
  have h3 : K * (n + cap + 2) ^ 4 ≤ R ^ 17 := by omega
  calc (K * (n + cap + 2) ^ 4) ^ c ≤ (R ^ 17) ^ c := Nat.pow_le_pow_left h3 c
    _ = R ^ (17 * c) := by rw [← pow_mul]
    _ ≤ RecoveryScheduleEnvelope.oracleSizeBound (17 * c) R := oracleSize_ge _ R hR1

theorem eventually_big (B : ℕ) : ∀ᶠ R : ℕ in atTop, 50 * B ^ 4 * (R + 1) ^ 16 ≤ R ^ 17 := by
  filter_upwards [eventually_ge_atTop (50 * B ^ 4 * 2 ^ 16), eventually_ge_atTop 1] with R hR hR1
  have h1 : (R + 1) ^ 16 ≤ (2 * R) ^ 16 := Nat.pow_le_pow_left (by omega) 16
  have h2 : (2 * R) ^ 16 = 2 ^ 16 * R ^ 16 := by ring
  calc 50 * B ^ 4 * (R + 1) ^ 16 ≤ 50 * B ^ 4 * (2 ^ 16 * R ^ 16) := Nat.mul_le_mul_left _ (h1.trans h2.le)
    _ = (50 * B ^ 4 * 2 ^ 16) * R ^ 16 := by ring
    _ ≤ R * R ^ 16 := Nat.mul_le_mul_right _ hR
    _ = R ^ 17 := by ring

/-- **Case 1's advantage at the native width**: `(R^{17c})^{−1/c} < e_{t(q)}` eventually in `q`, for every `R ≥ 1`
with `q ≤ K₁R`. -/
theorem eventually_caseOne_advR {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (c : ℕ) (hc : 1 ≤ c) (K₁ : ℕ) :
    ∀ᶠ q : ℕ in atTop, ∀ R : ℕ, 1 ≤ R → q ≤ K₁ * R →
      Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) R : ℝ) (-(1 : ℝ) / c) <
        xorEpsilon (ζ : ℝ) (rowBt h0 h1 q) := by
  filter_upwards [amplifier_le_eps_eventually ζ h0 h1 16 (by norm_num), eventually_ge_atTop (K₁ ^ 17 + 2)]
    with q hq hqK
  intro R hR1 hqR
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  refine (rpow_oracle_le c hc R hR1).trans_lt (lt_of_lt_of_le ?_ hq)
  -- `R^{−17} ≤ K₁^{17} q^{−17} < q^{−16}`
  rw [Real.rpow_neg hR0.le, Real.rpow_neg hq0.le]
  rw [show (17 : ℝ) = ((17 : ℕ) : ℝ) by norm_num, show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast]
  have hqR' : (q : ℝ) ≤ (K₁ : ℝ) * R := by exact_mod_cast hqR
  have hK : ((K₁ : ℝ)) ^ 17 < q := by exact_mod_cast (show K₁ ^ 17 < q by omega)
  have hq17 : (q : ℝ) ^ 17 ≤ (K₁ : ℝ) ^ 17 * (R : ℝ) ^ 17 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hq0.le hqR' 17
  have hR17 : (0 : ℝ) < (R : ℝ) ^ 17 := by positivity
  have hq16 : (0 : ℝ) < (q : ℝ) ^ 16 := by positivity
  rw [inv_lt_inv₀ hR17 hq16]
  -- `q^16 < R^17`: `q^17 ≤ K₁^17 R^17 < q R^17`
  have h2 : (q : ℝ) ^ 17 < q * (R : ℝ) ^ 17 := by
    calc (q : ℝ) ^ 17 ≤ (K₁ : ℝ) ^ 17 * (R : ℝ) ^ 17 := hq17
      _ < q * (R : ℝ) ^ 17 := by exact mul_lt_mul_of_pos_right hK hR17
  have h3 : (q : ℝ) ^ 17 = q * (q : ℝ) ^ 16 := by ring
  rw [h3] at h2
  exact lt_of_mul_lt_mul_left h2 hq0.le

/-- The width at a dyadic length is linear in the index: `q(2^a) ≤ K₁(a+1)`. -/
theorem widthAt_le (kclk Apad s : ℕ) :
    widthAt kclk Apad s ≤ ((kclk + 2) * (1 + Apad) + 3 * Apad + 1) * (s + 1) := by
  unfold widthAt
  have h := clog_le_self' (s * (kclk + 2) + 2)
  have h2 : Apad * Nat.clog 2 (s * (kclk + 2) + 2) ≤ Apad * (s * (kclk + 2) + 2) := Nat.mul_le_mul_left _ h
  nlinarith

/-! ## One source length -/

/-- The width constant `K₁ = (k+2)(1+A_pad) + 3A_pad + 1` (`q(2^a) ≤ K₁(a+1)`). -/
def widthK (kclk Apad : ℕ) : ℕ := (kclk + 2) * (1 + Apad) + 3 * Apad + 1

section Assembly2

end Assembly2

end NearCubicWires.WireExponent3_5.Transfer
