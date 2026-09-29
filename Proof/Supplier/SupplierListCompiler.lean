import Proof.Supplier.SupplierToeplitz
import Proof.Supplier.SupplierWindow

/-!
# Executable-seed list reconstruction

This module connects the production Toeplitz cells to the exact downward
one-hot recurrence.  Counts and differences are concrete functions of the
seed; no good-seed assumption is needed for the algebraic reconstruction.
Window bounds are used later only to certify that the corresponding
polynomial branch was printed.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierListCompiler

open NearCubicWires.SupplierList
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierToeplitz
open NearCubicWires.SupplierToeplitzCore

def prefixCount
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ) : ℕ :=
  toeplitzCellCount active label (zeroPrefixCell rank level) seed

def prefixDelta
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ) : ℤ :=
  (prefixCount active label seed level : ℤ) -
    2 * (prefixCount active label seed (level + 1) : ℤ)

theorem prefixCount_relation
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ) :
    (prefixCount active label seed level : ℤ) =
      2 * (prefixCount active label seed (level + 1) : ℤ) +
        prefixDelta active label seed level := by
  simp [prefixDelta]

theorem toeplitzCellCount_le_active_card
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (cell : Finset (BinaryVector rank))
    (seed : ToeplitzSeed rank) :
    toeplitzCellCount active label cell seed ≤ active.card := by
  unfold toeplitzCellCount
  calc
    (∑ index ∈ active,
        (decide
          (toeplitzHash (label index) seed ∈ cell) : Bool).toNat) ≤
        ∑ _index ∈ active, 1 := by
      apply Finset.sum_le_sum
      intro index _
      cases decide
        (toeplitzHash (label index) seed ∈ cell) <;> simp
    _ = active.card := by simp

theorem prefixCount_le_active_card
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ) :
    prefixCount active label seed level ≤ active.card :=
  toeplitzCellCount_le_active_card active label
    (zeroPrefixCell rank level) seed

theorem toeplitzAggregate_signedSlice_eq_cellCounts
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (positive negative : Finset (BinaryVector rank))
    (hdisjoint : Disjoint positive negative) :
    toeplitzAggregate active label
        (fun _index => signedSlice positive negative) seed =
      (toeplitzCellCount active label positive seed : ℝ) -
        (toeplitzCellCount active label negative seed : ℝ) := by
  have hpointwise : ∀ output : BinaryVector rank,
      signedSlice positive negative output =
        ((decide (output ∈ positive) : Bool).toNat : ℝ) -
          ((decide (output ∈ negative) : Bool).toNat : ℝ) := by
    intro output
    by_cases hpositive : output ∈ positive
    · have hnegative : output ∉ negative :=
        Finset.disjoint_left.mp hdisjoint hpositive
      simp [signedSlice, hpositive, hnegative]
    · by_cases hnegative : output ∈ negative
      · simp [signedSlice, hpositive, hnegative]
      · simp [signedSlice, hpositive, hnegative]
  unfold toeplitzAggregate toeplitzCellCount
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _
  exact hpointwise (toeplitzHash (label index) seed)

theorem prefixDelta_cast_eq_signedAggregate
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ) :
    (prefixDelta active label seed level : ℝ) =
      toeplitzAggregate active label
        (fun _index =>
          signedSlice (siblingPrefixCell rank level)
            (zeroPrefixCell rank (level + 1))) seed := by
  rw [toeplitzAggregate_signedSlice_eq_cellCounts
    active label seed
    (siblingPrefixCell rank level)
    (zeroPrefixCell rank (level + 1))
    siblingPrefixCell_disjoint]
  have hadd :=
    toeplitzPrefixCount_add (level := level) active label seed
  have hinteger :
      prefixDelta active label seed level =
        (toeplitzCellCount active label
            (siblingPrefixCell rank level) seed : ℤ) -
          (toeplitzCellCount active label
            (zeroPrefixCell rank (level + 1)) seed : ℤ) := by
    unfold prefixDelta prefixCount
    rw [hadd]
    omega
  exact_mod_cast hinteger

theorem prefixDelta_bad_eq_signedAggregate_bad
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level window : ℕ) :
    decide ((window : ℤ) <
        |prefixDelta active label seed level|) =
      decide ((window : ℝ) <
        |toeplitzAggregate active label
          (fun _index =>
            signedSlice (siblingPrefixCell rank level)
              (zeroPrefixCell rank (level + 1))) seed|) := by
  apply decide_eq_decide.mpr
  rw [← prefixDelta_cast_eq_signedAggregate]
  norm_cast

theorem prefixDelta_chebyshev
    {Index : Type} [DecidableEq Index]
    {rank level : ℕ} (hlevel : level < rank)
    (active : Finset Index) (label : Index → BinaryVector rank)
    (activeBound window : ℕ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hactive : active.card ≤ activeBound)
    (hwindow : 0 < window) :
    booleanMean (fun seed : ToeplitzSeed rank =>
      decide ((window : ℤ) <
        |prefixDelta active label seed level|)) ≤
      ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level)) /
        (window : ℝ) ^ 2 := by
  simp_rw [prefixDelta_bad_eq_signedAggregate_bad
    active label]
  exact toeplitzPrefixSlice_chebyshev hlevel active label
    activeBound window hlabels hactive (by exact_mod_cast hwindow)

theorem bitAsReal_nat_gt_le_div
    (threshold value : ℕ) :
    bitAsReal (decide (threshold < value)) ≤
      (value : ℝ) / (threshold + 1 : ℕ) := by
  by_cases hlarge : threshold < value
  · have hdenominator : (0 : ℝ) < (threshold + 1 : ℕ) := by
      positivity
    simp only [hlarge, decide_true, bitAsReal, if_true]
    rw [le_div_iff₀ hdenominator]
    simp only [one_mul]
    exact_mod_cast (Nat.succ_le_iff.mpr hlarge)
  · have hdecision :
        decide (threshold < value) = false := by
      exact decide_eq_false hlarge
    simp only [hdecision, bitAsReal, Bool.false_eq_true,
      ↓reduceIte]
    positivity

theorem booleanMean_nat_gt_le_realMean_div
    {Sample : Type} [Fintype Sample] [Nonempty Sample]
    (value : Sample → ℕ) (threshold : ℕ) :
    booleanMean (fun sample => decide (threshold < value sample)) ≤
      realMean (fun sample => (value sample : ℝ)) /
        (threshold + 1 : ℕ) := by
  have hsampleCard : (0 : ℝ) < Fintype.card Sample := by
    exact_mod_cast Fintype.card_pos
  have hthreshold : (0 : ℝ) < (threshold + 1 : ℕ) := by
    positivity
  unfold booleanMean realMean
  calc
    (∑ sample,
        bitAsReal (decide (threshold < value sample))) /
          Fintype.card Sample ≤
        (∑ sample,
          (value sample : ℝ) / (threshold + 1 : ℕ)) /
            Fintype.card Sample := by
      apply div_le_div_of_nonneg_right _ hsampleCard.le
      exact Finset.sum_le_sum fun sample _ =>
        bitAsReal_nat_gt_le_div threshold (value sample)
    _ = ((∑ sample, (value sample : ℝ)) /
          Fintype.card Sample) /
        (threshold + 1 : ℕ) := by
      rw [← Finset.sum_div]
      ring

theorem terminalPrefix_windowBound
    {Index : Type} [DecidableEq Index]
    {rank level : ℕ} (hlevel : level ≤ rank)
    (active : Finset Index) (label : Index → BinaryVector rank)
    (activeBound terminalWindow : ℕ)
    (hactive : active.card ≤ activeBound) :
    booleanMean (fun seed : ToeplitzSeed rank =>
      decide (terminalWindow <
        prefixCount active label seed level)) ≤
      ((activeBound : ℝ) / (2 : ℝ) ^ level) /
        (terminalWindow + 1 : ℕ) := by
  letI : Nonempty (ToeplitzSeed rank) := ⟨(0, 0)⟩
  calc
    booleanMean (fun seed : ToeplitzSeed rank =>
        decide (terminalWindow <
          prefixCount active label seed level)) ≤
        realMean (fun seed : ToeplitzSeed rank =>
          (prefixCount active label seed level : ℝ)) /
            (terminalWindow + 1 : ℕ) :=
      booleanMean_nat_gt_le_realMean_div
        (fun seed =>
          prefixCount active label seed level) terminalWindow
    _ ≤ ((activeBound : ℝ) / (2 : ℝ) ^ level) /
          (terminalWindow + 1 : ℕ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [show
        realMean (fun seed : ToeplitzSeed rank =>
            (prefixCount active label seed level : ℝ)) =
          active.card *
            (((zeroPrefixCell rank level).card : ℝ) /
              Fintype.card (BinaryVector rank)) by
        exact realMean_toeplitzCellCount active label
          (zeroPrefixCell rank level)]
      rw [terminalPrefix_density hlevel]
      calc
        (active.card : ℝ) * (1 / (2 : ℝ) ^ level) ≤
            (activeBound : ℝ) * (1 / (2 : ℝ) ^ level) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hactive
          · positivity
        _ = (activeBound : ℝ) / (2 : ℝ) ^ level := by
          ring

def prefixLevelBad
    {Index : Type} [DecidableEq Index]
    {rank depth : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (window : Fin depth → ℕ)
    (level : Fin depth) (seed : ToeplitzSeed rank) : Bool :=
  decide ((window level : ℤ) <
    |prefixDelta active label seed level.val|)

def prefixTerminalBad
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (depth terminalWindow : ℕ)
    (seed : ToeplitzSeed rank) : Bool :=
  decide (terminalWindow <
    prefixCount active label seed depth)

def prefixListBad
    {Index : Type} [DecidableEq Index]
    {rank depth : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (seed : ToeplitzSeed rank) : Bool :=
  decide (
    terminalWindow < prefixCount active label seed depth ∨
      ∃ level : Fin depth,
        (window level : ℤ) <
          |prefixDelta active label seed level.val|)

theorem prefixListBad_unionBound
    {Index : Type} [DecidableEq Index]
    {rank depth : ℕ} (hdepth : depth ≤ rank)
    (active : Finset Index) (label : Index → BinaryVector rank)
    (activeBound : ℕ) (window : Fin depth → ℕ)
    (terminalWindow : ℕ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hactive : active.card ≤ activeBound)
    (hwindow : ∀ level, 0 < window level) :
    booleanMean (prefixListBad active label window terminalWindow) ≤
      ((activeBound : ℝ) / (2 : ℝ) ^ depth) /
          (terminalWindow + 1 : ℕ) +
        ∑ level : Fin depth,
          (((activeBound : ℝ) *
              (1 / (2 : ℝ) ^ level.val)) /
            (window level : ℝ) ^ 2) := by
  let terminalBad : ToeplitzSeed rank → Bool :=
    prefixTerminalBad active label depth terminalWindow
  let levelBad : Fin depth → ToeplitzSeed rank → Bool :=
    prefixLevelBad active label window
  have hcovered : ∀ seed,
      prefixListBad active label window terminalWindow seed = true →
        terminalBad seed = true ∨
          ∃ level, levelBad level seed = true := by
    intro seed hfailure
    have hfailureProp :
        terminalWindow < prefixCount active label seed depth ∨
          ∃ level : Fin depth,
            (window level : ℤ) <
              |prefixDelta active label seed level.val| :=
      of_decide_eq_true hfailure
    rcases hfailureProp with hterminal | hlevel
    · left
      unfold terminalBad prefixTerminalBad
      exact decide_eq_true hterminal
    · right
      rcases hlevel with ⟨level, hlevel⟩
      refine ⟨level, ?_⟩
      unfold levelBad prefixLevelBad
      exact decide_eq_true hlevel
  have hunion :=
    nestedFailure_unionBound
      (prefixListBad active label window terminalWindow)
      terminalBad levelBad hcovered
  calc
    booleanMean
        (prefixListBad active label window terminalWindow) ≤
      booleanMean terminalBad +
        ∑ level : Fin depth, booleanMean (levelBad level) :=
      hunion
    _ ≤ ((activeBound : ℝ) / (2 : ℝ) ^ depth) /
          (terminalWindow + 1 : ℕ) +
        ∑ level : Fin depth,
          (((activeBound : ℝ) *
              (1 / (2 : ℝ) ^ level.val)) /
            (window level : ℝ) ^ 2) := by
      apply add_le_add
      · exact terminalPrefix_windowBound hdepth active label
          activeBound terminalWindow hactive
      · apply Finset.sum_le_sum
        intro level _
        exact prefixDelta_chebyshev
          (lt_of_lt_of_le level.isLt hdepth)
          active label activeBound (window level)
          hlabels hactive (hwindow level)

end NearCubicWires.SupplierListCompiler
