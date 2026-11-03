import Proof.Wire_3_5.Recovery.RecoveryBudgetBase
import Proof.Wire_3_5.Transfer.TransferTargets

/-! # Case 1's numeric conditions at the oracle degree `17·c_STV` (P3:3704-3709, 3685-3692, 3839-3840; D1.4)

Realizes the choice of the oracle degree for Case 1: "If no size-`q^G` oracle makes the outer verifier a tautology, any
honest outer oracle is worst-case hard for that general-circuit bound. Apply the imported worst-case amplifier. The
resulting function on at most `c_amp q` bits has the requisite hardness against both class simulations" (P3:3704-3709),
with "choose `G` large enough that `G/c_STV` exceeds a general-Boolean simulation exponent for both target classes and
the desired polynomial advantage exponent, with a fixed positive margin" (P3:3685-3692), and "The Case-1 amplifier
threshold is even smaller by the choice of `G`" (P3:3839-3840).

Paper quantities: at `G = 17c` (`c = c_STV`), base `core_hardness`'s size premises
`40(n+cap+2)⁴, 50(n+cap+2)⁴ ≤ ⌊(q^G)^{1/c}⌋` once `n + cap + 2 ≤ 4(q+1)⁴` and `12800(q+1)^{16} ≤ q^{17}`
(**`caseOne_size`**), and its advantage premise `(q^G)^{−1/c} < e_{t(q)}` eventually (**`eventually_caseOne_adv`**). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule
open Filter Topology

theorem oracleSize_ge (G q : ℕ) (hq : 1 ≤ q) : q ^ G ≤ RecoveryScheduleEnvelope.oracleSizeBound G q :=
  (Nat.pow_le_pow_right hq (RecoveryScheduleEnvelope.requiredDegree_le_oracleDegree G)).trans
    (PolynomialClock.pow_twoPow_le_pairClock _ q)

/-- `12800(q+1)^{16} ≤ q^{17}` eventually. -/
theorem eventually_12800 : ∀ᶠ q : ℕ in atTop, 12800 * (q + 1) ^ 16 ≤ q ^ 17 := by
  filter_upwards [eventually_ge_atTop (12800 * 2 ^ 16)] with q hq
  have h1 : (q + 1) ^ 16 ≤ (2 * q) ^ 16 := Nat.pow_le_pow_left (by omega) 16
  have h2 : (2 * q) ^ 16 = 2 ^ 16 * q ^ 16 := by ring
  have h3 : q ^ 17 = q * q ^ 16 := by ring
  calc 12800 * (q + 1) ^ 16 ≤ 12800 * (2 ^ 16 * q ^ 16) := Nat.mul_le_mul_left _ (h1.trans h2.le)
    _ = (12800 * 2 ^ 16) * q ^ 16 := by ring
    _ ≤ q * q ^ 16 := Nat.mul_le_mul_right _ hq
    _ = q ^ 17 := h3.symm

/-- **Case 1's advantage premise** eventually: `(q^{17c})^{−1/c} < e_{t(q)}`. -/
theorem eventually_caseOne_adv {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (c : ℕ) (hc : 1 ≤ c) :
    ∀ᶠ q : ℕ in atTop,
      Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) q : ℝ) (-(1 : ℝ) / c) <
        xorEpsilon (ζ : ℝ) (rowBt h0 h1 q) := by
  filter_upwards [amplifier_le_eps_eventually ζ h0 h1 16 (by norm_num), eventually_ge_atTop 2] with q hq hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hX : ((q : ℝ) ^ (17 * c : ℕ)) ≤ (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) q : ℝ) := by
    exact_mod_cast oracleSize_ge (17 * c) q (by omega)
  have hpos : (0 : ℝ) < (q : ℝ) ^ (17 * c : ℕ) := by positivity
  have hneg : -(1 : ℝ) / c ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / c := by positivity
    rw [neg_div]; linarith
  -- `X^{−1/c} ≤ (q^{17c})^{−1/c} = q^{−17}`
  have h1' : Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) q : ℝ) (-(1 : ℝ) / c) ≤
      Real.rpow ((q : ℝ) ^ (17 * c : ℕ)) (-(1 : ℝ) / c) :=
    Real.rpow_le_rpow_of_nonpos hpos hX hneg
  have h2 : Real.rpow ((q : ℝ) ^ (17 * c : ℕ)) (-(1 : ℝ) / c) = (q : ℝ) ^ (-(17 : ℝ)) := by
    show ((q : ℝ) ^ (17 * c : ℕ)) ^ (-(1 : ℝ) / c) = (q : ℝ) ^ (-(17 : ℝ))
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    push_cast
    field_simp
  have h3 : (q : ℝ) ^ (-(17 : ℝ)) < (q : ℝ) ^ (-(16 : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt hq1 (by norm_num)
  have h4 : (q : ℝ) ^ (-(16 : ℝ)) ≤ xorEpsilon (ζ : ℝ) (rowBt h0 h1 q) := hq
  calc Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) q : ℝ) (-(1 : ℝ) / c)
      ≤ (q : ℝ) ^ (-(17 : ℝ)) := h1'.trans h2.le
    _ < (q : ℝ) ^ (-(16 : ℝ)) := h3
    _ ≤ xorEpsilon (ζ : ℝ) (rowBt h0 h1 q) := h4

end NearCubicWires.WireExponent3_5.Transfer
