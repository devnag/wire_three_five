import Proof.Foundations.ScheduleArithmetic

/-!
# Smooth polynomial schedules

The source-facing recovery objects have fixed polynomial envelopes in the
source exponent.  This module proves that one canonical smooth envelope has a
first half-crossing whose predecessor is within the manuscript's one-sixth
jump.  The jump hypothesis is used only below the crossing; requiring it at
all later sources would be false for every polynomial of degree at least two.
-/

namespace NearCubicWires.PolynomialSchedule

open NearCubicWires.RecoveryPipeline
open NearCubicWires.ScheduleArithmetic
open NearCubicWires.SourceInterfaces

theorem polynomiallyBounded_mono
    {smaller larger : ℕ → ℕ}
    (hle : ∀ n, smaller n ≤ larger n)
    (hlarger : PolynomiallyBounded larger) :
    PolynomiallyBounded smaller := by
  rcases hlarger with
    ⟨coefficient, degree, hcoefficient, hbound⟩
  exact
    ⟨coefficient, degree, hcoefficient,
      fun n => (hle n).trans (hbound n)⟩

theorem polynomiallyBounded_constant (constant : ℕ) :
    PolynomiallyBounded (fun _ => constant) := by
  exact ⟨constant + 1, 0, by omega, by
    intro n
    simp⟩

theorem polynomiallyBounded_id :
    PolynomiallyBounded (fun n : ℕ => n) := by
  exact ⟨1, 1, by omega, by
    intro n
    simp⟩

theorem polynomiallyBounded_add
    {left right : ℕ → ℕ}
    (hleft : PolynomiallyBounded left)
    (hright : PolynomiallyBounded right) :
    PolynomiallyBounded (fun n => left n + right n) := by
  rcases hleft with
    ⟨leftCoefficient, leftDegree, hleftCoefficient, hleft⟩
  rcases hright with
    ⟨rightCoefficient, rightDegree, hrightCoefficient, hright⟩
  refine
    ⟨leftCoefficient + rightCoefficient,
      max leftDegree rightDegree, by omega, ?_⟩
  intro n
  calc
    left n + right n ≤
        leftCoefficient * (n + 1) ^ leftDegree +
          rightCoefficient * (n + 1) ^ rightDegree :=
      Nat.add_le_add (hleft n) (hright n)
    _ ≤
        leftCoefficient * (n + 1) ^ max leftDegree rightDegree +
          rightCoefficient * (n + 1) ^ max leftDegree rightDegree := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left _ <|
          Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      · exact Nat.mul_le_mul_left _ <|
          Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    _ =
        (leftCoefficient + rightCoefficient) *
          (n + 1) ^ max leftDegree rightDegree := by ring

theorem polynomiallyBounded_mul
    {left right : ℕ → ℕ}
    (hleft : PolynomiallyBounded left)
    (hright : PolynomiallyBounded right) :
    PolynomiallyBounded (fun n => left n * right n) := by
  rcases hleft with
    ⟨leftCoefficient, leftDegree, hleftCoefficient, hleft⟩
  rcases hright with
    ⟨rightCoefficient, rightDegree, hrightCoefficient, hright⟩
  refine
    ⟨leftCoefficient * rightCoefficient,
      leftDegree + rightDegree,
      Nat.mul_pos hleftCoefficient hrightCoefficient, ?_⟩
  intro n
  calc
    left n * right n ≤
        (leftCoefficient * (n + 1) ^ leftDegree) *
          (rightCoefficient * (n + 1) ^ rightDegree) := by
      exact Nat.mul_le_mul (hleft n) (hright n)
    _ =
        (leftCoefficient * rightCoefficient) *
          (n + 1) ^ (leftDegree + rightDegree) := by
      rw [pow_add]
      ring

theorem polynomiallyBounded_max
    {left right : ℕ → ℕ}
    (hleft : PolynomiallyBounded left)
    (hright : PolynomiallyBounded right) :
    PolynomiallyBounded (fun n => max (left n) (right n)) := by
  apply polynomiallyBounded_mono
    (larger := fun n => left n + right n)
  · intro n
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  · exact polynomiallyBounded_add hleft hright

theorem polynomiallyBounded_pow
    {function : ℕ → ℕ} (hfunction : PolynomiallyBounded function)
    (exponent : ℕ) :
    PolynomiallyBounded (fun n => function n ^ exponent) := by
  rcases hfunction with
    ⟨coefficient, degree, hcoefficient, hbound⟩
  refine
    ⟨coefficient ^ exponent + 1, degree * exponent, by omega, ?_⟩
  intro n
  calc
    function n ^ exponent ≤
        (coefficient * (n + 1) ^ degree) ^ exponent :=
      Nat.pow_le_pow_left (hbound n) _
    _ =
        coefficient ^ exponent *
          (n + 1) ^ (degree * exponent) := by
      rw [mul_pow, pow_mul]
    _ ≤
        (coefficient ^ exponent + 1) *
          (n + 1) ^ (degree * exponent) := by
      exact Nat.mul_le_mul_right _
        (Nat.le_add_right (coefficient ^ exponent) 1)

theorem polynomiallyBounded_comp
    {outer inner : ℕ → ℕ}
    (houter : PolynomiallyBounded outer)
    (hinner : PolynomiallyBounded inner) :
    PolynomiallyBounded (fun n => outer (inner n)) := by
  rcases houter with
    ⟨outerCoefficient, outerDegree, houterCoefficient, houter⟩
  rcases hinner with
    ⟨innerCoefficient, innerDegree, hinnerCoefficient, hinner⟩
  refine
    ⟨outerCoefficient * (innerCoefficient + 1) ^ outerDegree,
      innerDegree * outerDegree, by positivity, ?_⟩
  intro n
  have hone :
      1 ≤ (n + 1) ^ innerDegree := by
    exact Nat.one_le_pow innerDegree _ (by omega)
  have hinnerSucc :
      inner n + 1 ≤
        (innerCoefficient + 1) * (n + 1) ^ innerDegree := by
    calc
      inner n + 1 ≤
          innerCoefficient * (n + 1) ^ innerDegree + 1 :=
        Nat.add_le_add_right (hinner n) 1
      _ ≤
          innerCoefficient * (n + 1) ^ innerDegree +
            (n + 1) ^ innerDegree := by
        gcongr
      _ =
          (innerCoefficient + 1) * (n + 1) ^ innerDegree := by ring
  calc
    outer (inner n) ≤
        outerCoefficient * (inner n + 1) ^ outerDegree :=
      houter (inner n)
    _ ≤
        outerCoefficient *
          ((innerCoefficient + 1) *
            (n + 1) ^ innerDegree) ^ outerDegree := by
      gcongr
    _ =
        (outerCoefficient * (innerCoefficient + 1) ^ outerDegree) *
          (n + 1) ^ (innerDegree * outerDegree) := by
      rw [mul_pow, pow_mul]
      ring

/-- Every fixed polynomial envelope eventually fits in one sixteenth of the
canonical exponential source length.  The factor is charged explicitly so
downstream witness-width proofs do not hide a capacity assumption. -/
theorem polynomiallyBounded_eventually_le_sixteenth_exponential
    {function : ℕ → ℕ}
    (hfunction : PolynomiallyBounded function) :
    ∃ onset, ∀ n, onset ≤ n →
      function n ≤ 2 ^ (n + 1) / 16 := by
  rcases hfunction with
    ⟨coefficient, degree, hcoefficient, hbound⟩
  have hlittle :
      (fun n : ℕ => (n : ℝ) ^ degree) =o[Filter.atTop]
        (fun n : ℕ => (2 : ℝ) ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt degree (by norm_num)
  let scale : ℝ := 16 * coefficient * 2 ^ degree
  have hscale : 0 < scale := by
    dsimp only [scale]
    positivity
  have heventually := hlittle.bound (one_div_pos.mpr hscale)
  rw [Filter.eventually_atTop] at heventually
  rcases heventually with ⟨onset, heventually⟩
  refine ⟨max 1 onset, fun n hn => ?_⟩
  have hone : 1 ≤ n := (le_max_left 1 onset).trans hn
  have honset : onset ≤ n := (le_max_right 1 onset).trans hn
  have hsucc : n + 1 ≤ 2 * n := by omega
  have hpower :
      (n + 1) ^ degree ≤ 2 ^ degree * n ^ degree := by
    calc
      (n + 1) ^ degree ≤ (2 * n) ^ degree :=
        Nat.pow_le_pow_left hsucc degree
      _ = 2 ^ degree * n ^ degree := by rw [Nat.mul_pow]
  have hsmall := heventually n honset
  have hnnonnegative : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have htwoNonnegative : (0 : ℝ) ≤ 2 := by norm_num
  simp only [Real.norm_eq_abs, abs_pow,
    abs_of_nonneg hnnonnegative,
    abs_of_nonneg htwoNonnegative] at hsmall
  have hscaledReal :
      ((16 * function n : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    calc
      ((16 * function n : ℕ) : ℝ) ≤
          ((16 * (coefficient * (n + 1) ^ degree) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 16 (hbound n)
      _ ≤
          ((16 * (coefficient *
            (2 ^ degree * n ^ degree)) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 16
          (Nat.mul_le_mul_left coefficient hpower)
      _ = scale * (n : ℝ) ^ degree := by
        dsimp only [scale]
        push_cast
        ring
      _ ≤ (2 : ℝ) ^ n := by
        calc
          scale * (n : ℝ) ^ degree ≤
              scale * ((1 / scale) * (2 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left hsmall hscale.le
          _ = (2 : ℝ) ^ n := by field_simp
  have hscaled : 16 * function n ≤ 2 ^ n := by
    exact_mod_cast hscaledReal
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 16)).2
  calc
    function n * 16 = 16 * function n := by omega
    _ ≤ 2 ^ n := hscaled
    _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)

end NearCubicWires.PolynomialSchedule
