import Proof.Foundations.SupplierPipeline

/-!
# Zero-advice pairwise-hash concentration

This module proves the algebraic and probabilistic core of the pointwise list
construction.  A single affine-hash seed is fixed independently of the input:
distinct labels give exactly uniform, independent field values.  Centered
per-label contributions therefore have no cross terms, yielding the finite
second-moment and Chebyshev bounds used by the nested list.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierList

open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

noncomputable def realMean {Sample : Type} [Fintype Sample]
    (value : Sample → ℝ) : ℝ :=
  (∑ sample, value sample) / Fintype.card Sample

theorem bitAsReal_abs_gt_le_square
    (value threshold : ℝ) (hthreshold : 0 < threshold) :
    bitAsReal (decide (threshold < |value|)) ≤
      value ^ 2 / threshold ^ 2 := by
  by_cases hlarge : threshold < |value|
  · have hdecision : decide (threshold < |value|) = true := by
      simp [hlarge]
    simp only [hdecision, bitAsReal, if_true]
    rw [one_le_div (by positivity : 0 < threshold ^ 2)]
    calc
      threshold ^ 2 ≤ |value| ^ 2 :=
        (sq_le_sq₀ hthreshold.le (abs_nonneg value)).2 hlarge.le
      _ = value ^ 2 := sq_abs value
  · have hdecision : decide (threshold < |value|) = false := by
      simp [hlarge]
    simp only [hdecision, bitAsReal]
    positivity

/-- Finite Chebyshev inequality in exactly the `booleanMean` convention used
by the supplier contracts. -/
theorem booleanMean_abs_gt_le
    {Sample : Type} [Fintype Sample] [Nonempty Sample]
    (value : Sample → ℝ) (threshold variance : ℝ)
    (hthreshold : 0 < threshold)
    (hsecond :
      realMean (fun sample => value sample ^ 2) ≤ variance) :
    booleanMean (fun sample => decide (threshold < |value sample|)) ≤
      variance / threshold ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card Sample := by
    exact_mod_cast Fintype.card_pos
  have hsecondRaw :
      (∑ sample, value sample ^ 2) / Fintype.card Sample ≤ variance := by
    simpa [realMean] using hsecond
  unfold booleanMean
  calc
    (∑ sample, bitAsReal (decide (threshold < |value sample|))) /
          Fintype.card Sample ≤
        (∑ sample, value sample ^ 2 / threshold ^ 2) /
          Fintype.card Sample := by
      apply div_le_div_of_nonneg_right _ hcard.le
      exact Finset.sum_le_sum fun sample _ =>
        bitAsReal_abs_gt_le_square (value sample) threshold hthreshold
    _ = ((∑ sample, value sample ^ 2) / Fintype.card Sample) /
          threshold ^ 2 := by
      rw [← Finset.sum_div]
      ring
    _ ≤ variance / threshold ^ 2 := by
      exact div_le_div_of_nonneg_right hsecondRaw (sq_nonneg threshold)

def signedSlice {𝔽 : Type} [DecidableEq 𝔽]
    (positive negative : Finset 𝔽) (output : 𝔽) : ℝ :=
  if output ∈ positive then 1
  else if output ∈ negative then -1
  else 0

theorem sum_signedSlice
    {𝔽 : Type} [Fintype 𝔽] [DecidableEq 𝔽]
    (positive negative : Finset 𝔽)
    (hdisjoint : Disjoint positive negative) :
    ∑ output, signedSlice positive negative output =
      positive.card - negative.card := by
  have hpointwise : ∀ output : 𝔽,
      signedSlice positive negative output =
        (if output ∈ positive then 1 else 0) -
          if output ∈ negative then 1 else 0 := by
    intro output
    by_cases hpositive : output ∈ positive
    · have hnegative : output ∉ negative :=
        Finset.disjoint_left.mp hdisjoint hpositive
      simp [signedSlice, hpositive, hnegative]
    · by_cases hnegative : output ∈ negative
      · simp [signedSlice, hpositive, hnegative]
      · simp [signedSlice, hpositive, hnegative]
  simp_rw [hpointwise, Finset.sum_sub_distrib]
  simp

theorem sum_signedSlice_sq
    {𝔽 : Type} [Fintype 𝔽] [DecidableEq 𝔽]
    (positive negative : Finset 𝔽)
    (hdisjoint : Disjoint positive negative) :
    ∑ output, signedSlice positive negative output ^ 2 =
      positive.card + negative.card := by
  have hpointwise : ∀ output : 𝔽,
      signedSlice positive negative output ^ 2 =
        (if output ∈ positive then 1 else 0) +
          if output ∈ negative then 1 else 0 := by
    intro output
    by_cases hpositive : output ∈ positive
    · have hnegative : output ∉ negative :=
        Finset.disjoint_left.mp hdisjoint hpositive
      simp [signedSlice, hpositive, hnegative]
    · by_cases hnegative : output ∈ negative
      · simp [signedSlice, hpositive, hnegative]
      · simp [signedSlice, hpositive, hnegative]
  simp_rw [hpointwise, Finset.sum_add_distrib]
  simp

theorem realMean_signedSlice_sq
    {𝔽 : Type} [Fintype 𝔽] [DecidableEq 𝔽]
    (positive negative : Finset 𝔽)
    (hdisjoint : Disjoint positive negative) :
    realMean (fun output : 𝔽 =>
      signedSlice positive negative output ^ 2) =
      (positive.card + negative.card) / Fintype.card 𝔽 := by
  simp [realMean, sum_signedSlice_sq positive negative hdisjoint]

/-! ## Exact downward reconstruction -/

/-! ## Finite union and terminal-count bounds -/

theorem bitAsReal_nonnegative (value : Bool) :
    0 ≤ bitAsReal value := by
  cases value <;> simp [bitAsReal]

theorem booleanMean_exists_le_sum
    {Sample Level : Type} [Fintype Sample] [Nonempty Sample] [Fintype Level]
    (event : Level → Sample → Bool) :
    booleanMean (fun sample => decide (∃ level, event level sample = true)) ≤
      ∑ level, booleanMean (event level) := by
  have hpointwise : ∀ sample,
      bitAsReal (decide (∃ level, event level sample = true)) ≤
        ∑ level, bitAsReal (event level sample) := by
    intro sample
    by_cases hexists : ∃ level, event level sample = true
    · obtain ⟨level, hlevel⟩ := hexists
      have hsingle :
          bitAsReal (event level sample) ≤
            ∑ candidate, bitAsReal (event candidate sample) := by
        exact Finset.single_le_sum
          (fun candidate _ => bitAsReal_nonnegative (event candidate sample))
          (Finset.mem_univ level)
      have hleft :
          bitAsReal (decide (∃ level, event level sample = true)) = 1 := by
        have hexistsAgain : ∃ candidate, event candidate sample = true :=
          ⟨level, hlevel⟩
        simp [hexistsAgain, bitAsReal]
      have hselected : bitAsReal (event level sample) = 1 := by
        simp [hlevel, bitAsReal]
      rw [hleft, ← hselected]
      exact hsingle
    · have hleft :
          bitAsReal (decide (∃ level, event level sample = true)) = 0 := by
        simp [hexists, bitAsReal]
      rw [hleft]
      exact Finset.sum_nonneg fun level _ =>
        bitAsReal_nonnegative (event level sample)
  unfold booleanMean
  calc
    (∑ sample,
        bitAsReal (decide (∃ level, event level sample = true))) /
          Fintype.card Sample ≤
        (∑ sample, ∑ level, bitAsReal (event level sample)) /
          Fintype.card Sample := by
      apply div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun sample _ => hpointwise sample)
      positivity
    _ = ∑ level,
        (∑ sample, bitAsReal (event level sample)) /
          Fintype.card Sample := by
      rw [Finset.sum_comm, Finset.sum_div]

/-- A failure covered by the terminal overflow or one bad level pays exactly
the terminal first moment plus the sum of level errors. -/
theorem nestedFailure_unionBound
    {Sample Level : Type} [Fintype Sample] [Nonempty Sample] [Fintype Level]
    (failure terminalBad : Sample → Bool)
    (levelBad : Level → Sample → Bool)
    (hcovered : ∀ sample, failure sample = true →
      terminalBad sample = true ∨
        ∃ level, levelBad level sample = true) :
    booleanMean failure ≤
      booleanMean terminalBad + ∑ level, booleanMean (levelBad level) := by
  have hpointwise : ∀ sample,
      bitAsReal (failure sample) ≤
        bitAsReal (terminalBad sample) +
          bitAsReal (decide (∃ level, levelBad level sample = true)) := by
    intro sample
    by_cases hfailure : failure sample = true
    · rcases hcovered sample hfailure with hterminal | hlevel
      · have hfailureReal : bitAsReal (failure sample) = 1 := by
          simp [hfailure, bitAsReal]
        have hterminalReal : bitAsReal (terminalBad sample) = 1 := by
          simp [hterminal, bitAsReal]
        rw [hfailureReal, hterminalReal]
        exact le_add_of_nonneg_right
          (bitAsReal_nonnegative
            (decide (∃ level, levelBad level sample = true)))
      · have hexists : ∃ level, levelBad level sample = true := hlevel
        have hfailureReal : bitAsReal (failure sample) = 1 := by
          simp [hfailure, bitAsReal]
        have hexistsReal :
            bitAsReal
              (decide (∃ level, levelBad level sample = true)) = 1 := by
          simp [hexists, bitAsReal]
        rw [hfailureReal, hexistsReal]
        exact le_add_of_nonneg_left
          (bitAsReal_nonnegative (terminalBad sample))
    · have hfailureFalse : failure sample = false := Bool.eq_false_of_not_eq_true hfailure
      have hfailureReal : bitAsReal (failure sample) = 0 := by
        simp [hfailureFalse, bitAsReal]
      rw [hfailureReal]
      exact add_nonneg
        (bitAsReal_nonnegative (terminalBad sample))
        (bitAsReal_nonnegative
          (decide (∃ level, levelBad level sample = true)))
  have hcard : (0 : ℝ) ≤ Fintype.card Sample := by positivity
  calc
    booleanMean failure ≤
        booleanMean terminalBad +
          booleanMean
            (fun sample =>
              decide (∃ level, levelBad level sample = true)) := by
      unfold booleanMean
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hcard
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun sample _ => hpointwise sample
    _ ≤ booleanMean terminalBad +
        ∑ level, booleanMean (levelBad level) := by
      gcongr
      exact booleanMean_exists_le_sum levelBad

theorem bitAsReal_eq_toNat (value : Bool) :
    bitAsReal value = value.toNat := by
  cases value <;> simp [bitAsReal]

end NearCubicWires.SupplierList
