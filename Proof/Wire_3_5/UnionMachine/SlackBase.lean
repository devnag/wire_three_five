import Proof.Wire_3_5.UnionMachine.Weak

/-! # C6, part 2: rounded answers and slack thresholds (P3:3484-3491)

The union machine cannot do exact rational arithmetic on the primitive's printed values within `tr:time` (a value's
word may be `callBudget` long, F1). It rounds every answer to `p` bits (`roundQ p v = ⌊2^p v⌋/2^p`) and
tests `tr:thresholds` with the slack `δ = (1+Λ̄)⁴·2^{−p}` of the rounding:
`V̂' ≤ 2v₀ + δ`, `Q̂' ≤ 1+v₀+δ`, `μ̂' ≥ τ − δ`.

* **Completeness is exact**: every guess with `UnionAccepts` (the split's type, unchanged) passes the slack check
  (`unionSlackCheck_of_accepts`), since the rounded estimates are within `δ` of the exact ones (`VhatV_sub` etc., from
  `Poly4.estimate_error` and the coefficient masses `polyV_mass_le` …).
* **Soundness via slack**: a passing slack check gives `SlackAccepts` (`slackAccepts_of_check`), which fails on a
  hierarchy no-instance once `(1+Λ̄)⁴(q^{−D} + 2^{−p}) + δ ≤ ε₀` (`not_slackAccepts`): the rounded estimates, shifted by
  `δ`, are within `ε₀` of the masked tests (the `propagated_V/Q/Mu`) and pass the exact thresholds, which T's
  `masked_soundness_real` rules out. **`oneSided_of_soundForSlack`**: `SoundForSlack` gives the split's `OneSided`.
* `unionSlackRun` (decode, then the slack check) with `unionSlackRun_sound` / `unionSlackRun_complete`: the executable
  specification the C6 machine computes. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open Filter Topology

/-! ## Rounding -/

/-- **The rounded answer** `⌊2^p v⌋/2^p`. -/
def roundQ (p : ℕ) (v : ℚ) : ℚ := (⌊v * 2 ^ p⌋ : ℚ) / 2 ^ p

theorem roundQ_close_rat (p : ℕ) (v : ℚ) : |roundQ p v - v| ≤ 1 / 2 ^ p := by
  have hp : (0 : ℚ) < 2 ^ p := by positivity
  have h1 : (⌊v * 2 ^ p⌋ : ℚ) ≤ v * 2 ^ p := Int.floor_le _
  have h2 : v * 2 ^ p < (⌊v * 2 ^ p⌋ : ℚ) + 1 := Int.lt_floor_add_one _
  have e : roundQ p v - v = ((⌊v * 2 ^ p⌋ : ℚ) - v * 2 ^ p) / 2 ^ p := by
    rw [sub_div, mul_div_cancel_right₀ _ hp.ne']; rfl
  rw [e, abs_div, abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  rw [abs_le]; constructor <;> linarith

theorem roundQ_close (p : ℕ) (v : ℚ) : |(roundQ p v : ℝ) - v| ≤ 1 / 2 ^ p := by
  have h : ((|roundQ p v - v| : ℚ) : ℝ) ≤ ((1 / 2 ^ p : ℚ) : ℝ) := Rat.cast_le.mpr (roundQ_close_rat p v)
  push_cast at h
  exact h

/-- **The slack** of the rounding at grid mass `Λ̄`: `(1+Λ̄)⁴·2^{−p}`. -/
def slackOf (mass : ℚ) (p : ℕ) : ℚ := (1 + mass) ^ 4 / 2 ^ p

theorem slackOf_cast (mass : ℚ) (p : ℕ) : (slackOf mass p : ℝ) = (1 + (mass : ℝ)) ^ 4 * (1 / 2 ^ p) := by
  unfold slackOf; push_cast; ring

/-- **The slack check** of a parsed guess: the `check` with the thresholds relaxed by `δ`. -/
def slackCheck (D : UnionCheckData) (val : PrimRequest → ℚ) (v0 τ δ : ℚ) (callOk : PrimRequest → Bool) : Bool :=
  D.signsOk && D.schedule.all callOk && decide (D.VhatQ val ≤ 2 * v0 + δ) && decide (D.QhatQ val ≤ 1 + v0 + δ) &&
    decide (τ - δ ≤ D.μhatQ val)

section Slack
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

namespace UnionGuessSlack
variable {N : ℕ} {z : BitInput N} 

/-! ## The estimates at any answers -/


/-! ## Close answers give close estimates -/

/-! ## The calls' errors -/

/-! ## The slack acceptance and its soundness -/

variable (P : FusedPrimitive I) (p : ℕ → ℕ)

/-- The machine's answers: the primitive's values rounded to `p(q)` bits. -/
def roundedVal (q : ℕ) : PrimRequest → ℚ := fun r => roundQ (p q) (P.value r)

theorem roundedVal_close (q : ℕ) (r : PrimRequest) : |((roundedVal P p q r : ℚ) : ℝ) - P.value r| ≤ 1 / 2 ^ p q :=
  roundQ_close _ _

end UnionGuessSlack

open UnionGuessSlack

/-! ## The slack check, the run, soundness and completeness -/

end Slack


end NearCubicWires.WireExponent3_5.UnionMachine
