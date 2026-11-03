import Proof.CaseAnalysis.FinalSupplierWidth
import Proof.CaseAnalysis.FinalFamilyMass

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierAccuracyChain

open NearCubicWires
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Section 1 The two witnesses, at the consumer's own field types -/

/-- **`S.failure`.**  The supplier's per-call point error under S-W's uniform
denominator: the rows' requested reciprocal accuracy `1 / (target q + 1)` plus
one ulp of the floor division. -/
noncomputable def failureOf (target arity scale : ℕ → ℕ) :
    (n : ℕ) → BitInput n → List Bool →
      RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → ℝ :=
  fun n _ _ _ =>
    (1 : ℝ) / ((target (arity n) + 1 : ℕ) : ℝ)
      + 1 / ((C10SupplierWidth.denominator (arity n) (scale n) : ℕ) : ℝ)

noncomputable def massOf (limits : ℕ → CanonicalWitnessCodec.LegalSumLimits) :
    (n : ℕ) → BitInput n → List Bool →
      RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → ℝ :=
  fun n _ _ ph => C10FamilyMass.massBound (limits n) ph

/-! ## Section 2 `hpoint` from the row supplier, through the floor division -/

/-! ## Section 3 `hmass` at the decoded family -/

/-! ## Section 4 `haccuracy` — the product bound, and the constraint it forces

The budget is `estimationTolerance constants (zeta constants)` and the failure
has two terms, so each term is allotted half of it.  `accuracyTarget` is the
least reciprocal accuracy that pays one term; the two inequalities of
`haccuracy_of_bounds` say that `target` and the uniform denominator both clear
it. -/

/-- Pure arithmetic: a reciprocal weight times a mass is at most half a budget
as soon as twice the mass fits under the weight's own denominator.  No sign
hypothesis on the mass is needed: at `d = 0` the weight is `0`. -/
theorem recip_mul_le_half {epsilon mass d : ℝ} (hepsilon : 0 < epsilon)
    (hd0 : 0 ≤ d) (hd : 2 * mass ≤ d * epsilon) :
    1 / d * mass ≤ epsilon / 2 := by
  rcases eq_or_lt_of_le hd0 with hzero | hpos
  · rw [← hzero]
    simp only [div_zero, zero_mul]
    linarith
  · have hrewrite : 1 / d * mass = mass / d := by
      rw [div_mul_eq_mul_div, one_mul]
    rw [hrewrite, div_le_iff₀ hpos]
    nlinarith [hd]

noncomputable def accuracyTarget {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) : ℕ :=
  ⌈2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
      / estimationTolerance constants (zeta constants)⌉₊

theorem accuracyTarget_spec {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) (d : ℕ)
    (hd : accuracyTarget constants limits ph ≤ d) :
    2 * ((C10FamilyMass.siteMassBound limits.coefficientMassCap ph : ℚ) : ℝ)
      ≤ (d : ℝ) * ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  have hpos : 0 < estimationTolerance constants (zeta constants) :=
    (full_error_budget constants).1
  have hceil : 2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
        / estimationTolerance constants (zeta constants)
      ≤ ((⌈2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
            / estimationTolerance constants (zeta constants)⌉₊ : ℕ) : ℚ) :=
    Nat.le_ceil _
  have hunfold : accuracyTarget constants limits ph
      = ⌈2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
          / estimationTolerance constants (zeta constants)⌉₊ := rfl
  rw [hunfold] at hd
  have hdQ : ((⌈2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
        / estimationTolerance constants (zeta constants)⌉₊ : ℕ) : ℚ) ≤ (d : ℚ) := by
    exact_mod_cast hd
  have hle := hceil.trans hdQ
  rw [div_le_iff₀ hpos] at hle
  have hkey : 2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
      ≤ (d : ℚ) * estimationTolerance constants (zeta constants) := by linarith
  exact_mod_cast hkey

/-! ## Section 5 The constraint in closed form, for S0 / S1 / S-W's consumers -/

/-- One number per input length: the max of `accuracyTarget` over the three
phases of `CloseoutRowsOriginalSchedule`. -/
noncomputable def accuracyTargetAll {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits) : ℕ :=
  max
    (max (accuracyTarget constants limits
        RepairOrdinary.CloseoutRowsOriginalSchedule.Phase.penalty)
      (accuracyTarget constants limits
        RepairOrdinary.CloseoutRowsOriginalSchedule.Phase.moment))
    (accuracyTarget constants limits
      RepairOrdinary.CloseoutRowsOriginalSchedule.Phase.clause)

theorem accuracyTarget_le_all {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) :
    accuracyTarget constants limits ph ≤ accuracyTargetAll constants limits := by
  cases ph with
  | penalty => exact le_trans (le_max_left _ _) (le_max_left _ _)
  | moment => exact le_trans (le_max_right _ _) (le_max_left _ _)
  | clause => exact le_max_right _ _

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierAccuracyChain
