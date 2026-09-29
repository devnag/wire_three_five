import Proof.Foundations.AsymptoticAdapters
import Proof.Foundations.CircuitRestriction

/-!
# Physical wire-cap transfer across scheduled padding

The schedule keeps the selected core within a factor three of the target.
Shrinking a source cap coefficient by `27 = 3^3` therefore pays the entire
cubic arity change; monotonicity of `logScale` only improves the comparison.
-/

namespace NearCubicWires.WireScaleTransfer

open NearCubicWires
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.RecoveryPipeline

theorem logScale_mono {core target : ℕ} (hcore : core ≤ target) :
    logScale core ≤ logScale target := by
  apply Nat.clog_mono_right 2
  omega

theorem cube_le_factor_cube
    (factor : ℕ) {core target : ℕ}
    (hratio : target ≤ factor * core) :
    target ^ 3 ≤ factor ^ 3 * core ^ 3 := by
  calc
    target ^ 3 ≤ (factor * core) ^ 3 :=
      Nat.pow_le_pow_left hratio 3
    _ = factor ^ 3 * core ^ 3 := by ring

/-- Padding through any proved constant-factor arity comparison costs exactly
the cube of that factor.  This is used when a tight source reindexing first
pads a raw recovery core to the linear selector schedule. -/
theorem wireScale_shrink_cube
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient)
    (factor logExponent : ℕ) (hfactor : 0 < factor)
    {core target : ℕ}
    (hcore : core ≤ target) (hratio : target ≤ factor * core) :
    wireScale (coefficient / (factor : ℝ) ^ 3) logExponent target ≤
      wireScale coefficient logExponent core := by
  have hcubeNat := cube_le_factor_cube factor hratio
  have hcubeReal :
      (target : ℝ) ^ 3 ≤ (factor : ℝ) ^ 3 * (core : ℝ) ^ 3 := by
    exact_mod_cast hcubeNat
  have hfactorReal : (0 : ℝ) < factor := by exact_mod_cast hfactor
  have hnumerator :
      coefficient / (factor : ℝ) ^ 3 * (target : ℝ) ^ 3 ≤
        coefficient * (core : ℝ) ^ 3 := by
    calc
      coefficient / (factor : ℝ) ^ 3 * (target : ℝ) ^ 3 ≤
          coefficient / (factor : ℝ) ^ 3 *
            ((factor : ℝ) ^ 3 * (core : ℝ) ^ 3) := by
        gcongr
      _ = coefficient * (core : ℝ) ^ 3 := by
        field_simp
  have hlog := logScale_mono hcore
  have hlogPower :
      (logScale core : ℝ) ^ logExponent ≤
        (logScale target : ℝ) ^ logExponent := by
    gcongr
  have hcoreDenominator :
      0 < (logScale core : ℝ) ^ logExponent := by
    have : (0 : ℝ) < logScale core := by
      exact_mod_cast logScale_pos core
    positivity
  unfold wireScale
  calc
    coefficient / (factor : ℝ) ^ 3 * (target : ℝ) ^ 3 /
          (logScale target : ℝ) ^ logExponent ≤
        coefficient / (factor : ℝ) ^ 3 * (target : ℝ) ^ 3 /
          (logScale core : ℝ) ^ logExponent := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg
          (div_nonneg hcoefficient (by positivity))
          (by positivity))
        hcoreDenominator hlogPower
    _ ≤ coefficient * (core : ℝ) ^ 3 /
          (logScale core : ℝ) ^ logExponent := by
      exact div_le_div_of_nonneg_right hnumerator hcoreDenominator.le

end NearCubicWires.WireScaleTransfer
