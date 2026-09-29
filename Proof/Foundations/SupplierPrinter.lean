import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.MvPolynomial.Eval
import Proof.Foundations.SupplierPrime

/-!
# Exact signed-score printer algebra

This module proves the local, representation-sensitive part of Appendix B:
finite binary reconstruction, signed-by-Boolean multiplication using positive
and negative bit planes, equality as two consecutive weak cuts, and the
dominance reduction.  It also connects each bit-plane call to the executable
Williams contract.  Constructing one fixed interpreter program that performs
the preprocessing, all calls, and output encoding still requires a verified
program-composition interface; no uncharged semantic runner is introduced
here.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierPrinter

open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces
open NearCubicWires.ThresholdCompiler

/-! ## Exact signed binary slicing -/

theorem testBit_sum_eq {value width : ℕ} (hvalue : value < 2 ^ width) :
    (∑ bit : Fin width, if value.testBit bit.val then 2 ^ bit.val else 0) =
      value := by
  simpa only [encodeBitInput] using
    NearCubicWires.encodeBitInput_testBit hvalue

theorem testBit_toNat_sum_eq {value width : ℕ}
    (hvalue : value < 2 ^ width) :
    (∑ bit : Fin width, (value.testBit bit.val).toNat * 2 ^ bit.val) =
      value := by
  calc
    (∑ bit : Fin width, (value.testBit bit.val).toNat * 2 ^ bit.val) =
        ∑ bit : Fin width,
          if value.testBit bit.val then 2 ^ bit.val else 0 := by
      apply Finset.sum_congr rfl
      intro bit _
      cases value.testBit bit.val <;> simp
    _ = value := testBit_sum_eq hvalue

def positiveMagnitudeBit (value : ℤ) (bit : ℕ) : Bool :=
  if 0 ≤ value then value.natAbs.testBit bit else false

def negativeMagnitudeBit (value : ℤ) (bit : ℕ) : Bool :=
  if value < 0 then value.natAbs.testBit bit else false

theorem signed_binary_reconstruction {value : ℤ} {width : ℕ}
    (hvalue : value.natAbs < 2 ^ width) :
    value =
      ((∑ bit : Fin width,
        (positiveMagnitudeBit value bit.val).toNat * 2 ^ bit.val : ℕ) : ℤ) -
      ((∑ bit : Fin width,
        (negativeMagnitudeBit value bit.val).toNat * 2 ^ bit.val : ℕ) : ℤ) := by
  by_cases hnonnegative : 0 ≤ value
  · have hsum := testBit_toNat_sum_eq hvalue
    simp [positiveMagnitudeBit, negativeMagnitudeBit, hnonnegative,
      not_lt.mpr hnonnegative, hsum, Int.natAbs_of_nonneg hnonnegative]
  · have hnegative : value < 0 := lt_of_not_ge hnonnegative
    have hsum := testBit_toNat_sum_eq hvalue
    simp [positiveMagnitudeBit, negativeMagnitudeBit, hnegative,
      hnonnegative, hsum]
    simp [abs_of_neg hnegative]

theorem signed_binary_reconstruction_sum {value : ℤ} {width : ℕ}
    (hvalue : value.natAbs < 2 ^ width) :
    value = ∑ bit : Fin width, (2 ^ bit.val : ℤ) *
      (((positiveMagnitudeBit value bit.val).toNat : ℤ) -
        ((negativeMagnitudeBit value bit.val).toNat : ℤ)) := by
  calc
    value =
        ((∑ bit : Fin width,
          (positiveMagnitudeBit value bit.val).toNat * 2 ^ bit.val : ℕ) : ℤ) -
        ((∑ bit : Fin width,
          (negativeMagnitudeBit value bit.val).toNat * 2 ^ bit.val : ℕ) : ℤ) :=
      signed_binary_reconstruction hvalue
    _ = ∑ bit : Fin width, (2 ^ bit.val : ℤ) *
        (((positiveMagnitudeBit value bit.val).toNat : ℤ) -
          ((negativeMagnitudeBit value bit.val).toNat : ℤ)) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro bit _
      ring

/-! ## Signed-by-Boolean matrix multiplication -/

abbrev IntMatrix (rows columns : ℕ) :=
  Fin rows → Fin columns → ℤ

def signedBooleanProduct {rows inner columns : ℕ}
    (left : IntMatrix rows inner) (right : BitMatrix inner columns) :
    IntMatrix rows columns :=
  fun row column =>
    ∑ index, left row index * (right index column).toNat

def positiveBitPlane {rows columns : ℕ}
    (matrix : IntMatrix rows columns) (bit : ℕ) :
    BitMatrix rows columns :=
  fun row column => positiveMagnitudeBit (matrix row column) bit

def negativeBitPlane {rows columns : ℕ}
    (matrix : IntMatrix rows columns) (bit : ℕ) :
    BitMatrix rows columns :=
  fun row column => negativeMagnitudeBit (matrix row column) bit

def recombinedSignedProduct {rows inner columns width : ℕ}
    (left : IntMatrix rows inner) (right : BitMatrix inner columns) :
    IntMatrix rows columns :=
  fun row column =>
    ∑ bit : Fin width, (2 ^ bit.val : ℤ) *
      (((integerMatrixProduct (positiveBitPlane left bit.val) right
          row column : ℕ) : ℤ) -
        ((integerMatrixProduct (negativeBitPlane left bit.val) right
          row column : ℕ) : ℤ))

theorem integerMatrixProduct_cast {rows inner columns : ℕ}
    (left : BitMatrix rows inner) (right : BitMatrix inner columns)
    (row : Fin rows) (column : Fin columns) :
    ((integerMatrixProduct left right row column : ℕ) : ℤ) =
      ∑ index,
        ((left row index).toNat : ℤ) *
          ((right index column).toNat : ℤ) := by
  rw [integerMatrixProduct]
  push_cast
  apply Finset.sum_congr rfl
  intro index _
  cases left row index <;> cases right index column <;> rfl

theorem recombinedSignedProduct_eq {rows inner columns width : ℕ}
    (left : IntMatrix rows inner) (right : BitMatrix inner columns)
    (hmagnitude : ∀ row index, (left row index).natAbs < 2 ^ width) :
    recombinedSignedProduct (width := width) left right =
      signedBooleanProduct left right := by
  funext row column
  simp only [recombinedSignedProduct, signedBooleanProduct]
  simp_rw [integerMatrixProduct_cast]
  simp only [positiveBitPlane, negativeBitPlane]
  calc
    (∑ bit : Fin width, (2 ^ bit.val : ℤ) *
        ((∑ index,
          ((positiveMagnitudeBit (left row index) bit.val).toNat : ℤ) *
            ((right index column).toNat : ℤ)) -
        ∑ index,
          ((negativeMagnitudeBit (left row index) bit.val).toNat : ℤ) *
            ((right index column).toNat : ℤ))) =
      ∑ bit : Fin width, ∑ index : Fin inner,
        (2 ^ bit.val : ℤ) *
          ((((positiveMagnitudeBit (left row index) bit.val).toNat : ℤ) -
            ((negativeMagnitudeBit (left row index) bit.val).toNat : ℤ)) *
            ((right index column).toNat : ℤ)) := by
      apply Finset.sum_congr rfl
      intro bit _
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ = ∑ index : Fin inner, ∑ bit : Fin width,
        (2 ^ bit.val : ℤ) *
          ((((positiveMagnitudeBit (left row index) bit.val).toNat : ℤ) -
            ((negativeMagnitudeBit (left row index) bit.val).toNat : ℤ)) *
            ((right index column).toNat : ℤ)) := Finset.sum_comm
    _ = ∑ index, left row index * (right index column).toNat := by
      apply Finset.sum_congr rfl
      intro index _
      have hreconstruction :=
        signed_binary_reconstruction_sum (hmagnitude row index)
      calc
        (∑ bit : Fin width, (2 ^ bit.val : ℤ) *
            ((((positiveMagnitudeBit (left row index) bit.val).toNat : ℤ) -
              ((negativeMagnitudeBit (left row index) bit.val).toNat : ℤ)) *
              ((right index column).toNat : ℤ))) =
            (∑ bit : Fin width, (2 ^ bit.val : ℤ) *
              (((positiveMagnitudeBit (left row index) bit.val).toNat : ℤ) -
                ((negativeMagnitudeBit (left row index) bit.val).toNat : ℤ))) *
              ((right index column).toNat : ℤ) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro bit _
          ring
        _ = left row index * (right index column).toNat :=
          congrArg
            (fun value : ℤ =>
              value * ((right index column).toNat : ℤ))
            hreconstruction.symm

/-! ## Connection to the executable rectangular-product contract -/

/-! ## Equality cuts and weighted dominance -/

def weakCut (threshold score : ℤ) : Bool :=
  decide (threshold ≤ score)

def exactCut (threshold score : ℤ) : Bool :=
  decide (threshold = score)

theorem exactCut_eq_successiveCuts (threshold score : ℤ) :
    ((exactCut threshold score).toNat : ℤ) =
      (weakCut threshold score).toNat -
        (weakCut (threshold + 1) score).toNat := by
  unfold exactCut weakCut
  by_cases hequal : threshold = score
  · subst score
    simp
  · by_cases hbelow : score < threshold
    · have hnotThreshold : ¬threshold ≤ score := by omega
      have hnotSuccessor : ¬threshold + 1 ≤ score := by omega
      simp [hequal, hnotThreshold, hnotSuccessor]
    · have habove : threshold + 1 ≤ score := by omega
      have hthreshold : threshold ≤ score := by omega
      simp [hequal, hthreshold, habove]

theorem threshold_split_as_dominance
    (threshold leftScore rightScore : ℤ) :
    weakCut threshold (leftScore + rightScore) =
      decide (threshold - leftScore ≤ rightScore) := by
  unfold weakCut
  by_cases hleft : threshold ≤ leftScore + rightScore
  · have hright : threshold - leftScore ≤ rightScore := by omega
    simp [hleft, hright]
  · have hright : ¬threshold - leftScore ≤ rightScore := by omega
    simp [hleft, hright]

def weightedDominance {Rows Gates Columns : ℕ}
    (left : IntMatrix Rows Gates) (right : IntMatrix Gates Columns)
    (weight : Fin Gates → ℤ) : IntMatrix Rows Columns :=
  fun row column =>
    ∑ gate, weight gate *
      ((decide (left row gate ≤ right gate column) : Bool).toNat : ℤ)

/-! ## Exact same-bucket/cross-bucket dominance split -/

/-- Semantic certificate produced by a stable joint sort.  Left copies precede
right copies on ties, so cross-bucket comparisons are strict in bucket index
and only same-bucket pairs require a local scan. -/
structure BucketedDominanceLayout
    (Rows Gates Columns : Type) [Fintype Gates] (Buckets : ℕ) where
  leftScore : Rows → Gates → ℤ
  rightScore : Gates → Columns → ℤ
  leftBucket : Rows → Gates → Fin Buckets
  rightBucket : Gates → Columns → Fin Buckets
  comparison : ∀ row gate column,
    leftScore row gate ≤ rightScore gate column ↔
      leftBucket row gate < rightBucket gate column ∨
        (leftBucket row gate = rightBucket gate column ∧
          leftScore row gate ≤ rightScore gate column)

/-! ### Canonical stable joint-sort layout -/

/-- A stable-sort occurrence is either one left row or one right column.  The
sum-to-fin equivalence supplies the final deterministic tie breaker, after the
mandatory left-before-right tag used by the dominance reduction. -/
abbrev StableDominanceCopy (Rows Columns : ℕ) :=
  Fin Rows ⊕ Fin Columns

def stableDominanceCopyId {Rows Columns : ℕ} :
    StableDominanceCopy Rows Columns → Fin (Rows + Columns) :=
  finSumFinEquiv

def stableDominanceCopyScore {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) :
    StableDominanceCopy Rows Columns → ℤ
  | .inl row => leftScore row gate
  | .inr column => rightScore gate column

/-- Lexicographic sort key.  The occurrence id makes all keys distinct, while
`Fin.castAdd` places every left copy before every right copy on an exact tie. -/
def stableDominanceKey {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (copy : StableDominanceCopy Rows Columns) :
    ℤ ×ₗ Fin (Rows + Columns) :=
  toLex (stableDominanceCopyScore leftScore rightScore gate copy,
    stableDominanceCopyId copy)

theorem stableDominanceKey_injective {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) :
    Function.Injective (stableDominanceKey leftScore rightScore gate) := by
  intro left right hequal
  have hid :
      stableDominanceCopyId left = stableDominanceCopyId right :=
    congrArg (fun key : ℤ ×ₗ Fin (Rows + Columns) => (ofLex key).2)
      hequal
  exact finSumFinEquiv.injective hid

def stableDominanceKeys {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) : Finset (ℤ ×ₗ Fin (Rows + Columns)) :=
  Finset.univ.image (stableDominanceKey leftScore rightScore gate)

theorem stableDominanceKeys_card {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) :
    (stableDominanceKeys leftScore rightScore gate).card =
      Rows + Columns := by
  rw [stableDominanceKeys,
    Finset.card_image_of_injective _
      (stableDominanceKey_injective leftScore rightScore gate)]
  simp

def stableDominanceKeyMember {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (copy : StableDominanceCopy Rows Columns) :
    stableDominanceKeys leftScore rightScore gate :=
  ⟨stableDominanceKey leftScore rightScore gate copy, by
    simp [stableDominanceKeys]⟩

/-- Zero-based position of an occurrence in the stable joint sort.  Defining
the rank through Mathlib's finite order isomorphism makes uniqueness and total
ordering part of the construction instead of an extra layout hypothesis. -/
def stableDominanceRank {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (copy : StableDominanceCopy Rows Columns) :
    Fin (Rows + Columns) :=
  ((stableDominanceKeys leftScore rightScore gate).orderIsoOfFin
    (stableDominanceKeys_card leftScore rightScore gate)).symm
      (stableDominanceKeyMember leftScore rightScore gate copy)

theorem stableDominanceRank_lt_iff_key_lt {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (left right : StableDominanceCopy Rows Columns) :
    stableDominanceRank leftScore rightScore gate left <
        stableDominanceRank leftScore rightScore gate right ↔
      stableDominanceKey leftScore rightScore gate left <
        stableDominanceKey leftScore rightScore gate right := by
  let keys := stableDominanceKeys leftScore rightScore gate
  let cardProof : keys.card = Rows + Columns :=
    stableDominanceKeys_card leftScore rightScore gate
  let order := keys.orderIsoOfFin cardProof
  change order.symm
        (stableDominanceKeyMember leftScore rightScore gate left) <
      order.symm
        (stableDominanceKeyMember leftScore rightScore gate right) ↔ _
  rw [order.symm.lt_iff_lt]
  rfl

theorem stableDominanceKey_left_lt_right_iff {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (row : Fin Rows) (gate : Fin Gates) (column : Fin Columns) :
    stableDominanceKey leftScore rightScore gate (.inl row) <
        stableDominanceKey leftScore rightScore gate (.inr column) ↔
      leftScore row gate ≤ rightScore gate column := by
  unfold stableDominanceKey stableDominanceCopyScore
    stableDominanceCopyId
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (hscore | ⟨hscore, _⟩)
    · exact le_of_lt hscore
    · exact le_of_eq hscore
  · intro hscore
    by_cases hstrict : leftScore row gate < rightScore gate column
    · exact Or.inl hstrict
    · refine Or.inr ⟨le_antisymm hscore (le_of_not_gt hstrict), ?_⟩
      rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
      change row.val < Rows + column.val
      omega

theorem stableDominanceRank_left_lt_right_iff
    {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (row : Fin Rows) (gate : Fin Gates) (column : Fin Columns) :
    stableDominanceRank leftScore rightScore gate (.inl row) <
        stableDominanceRank leftScore rightScore gate (.inr column) ↔
      leftScore row gate ≤ rightScore gate column := by
  rw [stableDominanceRank_lt_iff_key_lt,
    stableDominanceKey_left_lt_right_iff]

/-- Number of blocks in the stable sort.  `bucketSize + 1` keeps the
construction total; callers pass the desired positive block width minus one. -/
def stableDominanceBucketCount
    (Rows Columns bucketSize : ℕ) : ℕ :=
  (Rows + Columns) / (bucketSize + 1) + 1

/-- Number of stable buckets that the rectangular backend can carry once one
gate coordinate is included.  The zero-gate case is kept total. -/
def stableCapacityBucketBudget (capacity gates : ℕ) : ℕ :=
  if gates = 0 then 1 else capacity / gates

/-- Canonical block size selected from the backend capacity.  When there is
only room for one bucket it uses the whole joint list; otherwise division by
`budget - 1` leaves one full bucket of rounding slack. -/
def stableCapacityBucketSize
    (Rows Columns capacity gates : ℕ) : ℕ :=
  let budget := stableCapacityBucketBudget capacity gates
  if budget ≤ 1 then Rows + Columns
  else (Rows + Columns) / (budget - 1)

theorem stableCapacityBucketCount_le_budget
    (Rows Columns capacity gates : ℕ)
    (_hgates : 0 < gates)
    (hbudget : 1 < stableCapacityBucketBudget capacity gates) :
    stableDominanceBucketCount Rows Columns
        (stableCapacityBucketSize Rows Columns capacity gates) ≤
      stableCapacityBucketBudget capacity gates := by
  let entries := Rows + Columns
  let budget := stableCapacityBucketBudget capacity gates
  have hdivisor : 0 < budget - 1 := Nat.sub_pos_of_lt hbudget
  have hwidth : 0 < entries / (budget - 1) + 1 := Nat.succ_pos _
  have hentries :
      entries < (budget - 1) * (entries / (budget - 1) + 1) :=
    Nat.lt_mul_div_succ entries hdivisor
  have hquotient :
      entries / (entries / (budget - 1) + 1) < budget - 1 := by
    exact (Nat.div_lt_iff_lt_mul hwidth).2 hentries
  unfold stableDominanceBucketCount stableCapacityBucketSize
  change
    entries /
          ((if budget ≤ 1 then entries else entries / (budget - 1)) + 1) +
        1 ≤
      budget
  rw [if_neg (not_le_of_gt hbudget)]
  omega

/-- The canonical stable layout always fits when the number of gate
coordinates squared fits the rectangular inner dimension.  This is the exact
finite form of the printer's strict exponent inequality. -/
theorem stableCapacityBucketDimension_le
    (Rows Columns capacity gates : ℕ)
    (hgateSquare : gates * gates ≤ capacity) :
    gates *
        stableDominanceBucketCount Rows Columns
          (stableCapacityBucketSize Rows Columns capacity gates) ≤
      capacity := by
  by_cases hgatesZero : gates = 0
  · simp [hgatesZero]
  have hgates : 0 < gates := Nat.pos_of_ne_zero hgatesZero
  let budget := stableCapacityBucketBudget capacity gates
  have hbudgetEq : budget = capacity / gates := by
    simp [budget, stableCapacityBucketBudget, hgatesZero]
  have hgatesLeBudget : gates ≤ budget := by
    rw [hbudgetEq]
    exact (Nat.le_div_iff_mul_le hgates).2 hgateSquare
  have hgateBudget : gates * budget ≤ capacity := by
    rw [hbudgetEq, Nat.mul_comm]
    exact Nat.div_mul_le_self capacity gates
  by_cases hbudgetLarge : 1 < budget
  · calc
      gates *
          stableDominanceBucketCount Rows Columns
            (stableCapacityBucketSize Rows Columns capacity gates) ≤
          gates * budget := by
            exact Nat.mul_le_mul_left gates
              (stableCapacityBucketCount_le_budget Rows Columns capacity gates
                hgates (by simpa [budget] using hbudgetLarge))
      _ ≤ capacity := hgateBudget
  · have hbudgetSmall : budget ≤ 1 := Nat.le_of_not_gt hbudgetLarge
    have hgatesEq : gates = 1 := by omega
    have hbudgetOne : budget = 1 := by omega
    subst gates
    have hcapacityEq : capacity = 1 := by
      change stableCapacityBucketBudget capacity 1 = 1 at hbudgetOne
      simpa [stableCapacityBucketBudget] using hbudgetOne
    subst capacity
    unfold stableDominanceBucketCount stableCapacityBucketSize
    simp only [stableCapacityBucketBudget, one_ne_zero, if_false,
      Nat.div_one, one_mul]
    rw [if_pos le_rfl]
    have hentries :
        Rows + Columns < Rows + Columns + 1 := Nat.lt_succ_self _
    rw [Nat.div_eq_of_lt hentries]

def stableDominanceBucket {Rows Columns bucketSize : ℕ}
    (rank : Fin (Rows + Columns)) :
    Fin (stableDominanceBucketCount Rows Columns bucketSize) :=
  ⟨rank.val / (bucketSize + 1), by
    unfold stableDominanceBucketCount
    have hrank : rank.val ≤ Rows + Columns := Nat.le_of_lt rank.isLt
    have hdiv :
        rank.val / (bucketSize + 1) ≤
          (Rows + Columns) / (bucketSize + 1) :=
      Nat.div_le_div_right hrank
    omega⟩

theorem stableDominanceBucket_lt_implies_rank_lt
    {Rows Columns bucketSize : ℕ}
    {left right : Fin (Rows + Columns)}
    (hbucket :
      stableDominanceBucket (bucketSize := bucketSize) left <
        stableDominanceBucket (bucketSize := bucketSize) right) :
    left < right := by
  by_contra hnot
  have hrank : right.val ≤ left.val := by
    exact le_of_not_gt hnot
  have hdiv :
      right.val / (bucketSize + 1) ≤
        left.val / (bucketSize + 1) :=
    Nat.div_le_div_right hrank
  exact (not_lt_of_ge hdiv) hbucket

theorem stableDominanceRank_lt_implies_bucket_le
    {Rows Columns bucketSize : ℕ}
    {left right : Fin (Rows + Columns)}
    (hrank : left < right) :
    stableDominanceBucket (bucketSize := bucketSize) left ≤
      stableDominanceBucket (bucketSize := bucketSize) right := by
  exact Nat.div_le_div_right (Nat.le_of_lt hrank)

/-- The production stable joint-sort constructor.  Bucketing is performed on
unique sorted occurrences, so equal scores retain the required left/right
ordering without assuming distinct weights or distinct rows. -/
def stableBucketedDominanceLayout {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (bucketSize : ℕ) :
    BucketedDominanceLayout (Fin Rows) (Fin Gates) (Fin Columns)
      (stableDominanceBucketCount Rows Columns bucketSize) where
  leftScore := leftScore
  rightScore := rightScore
  leftBucket := fun row gate =>
    stableDominanceBucket (bucketSize := bucketSize)
      (stableDominanceRank leftScore rightScore gate (.inl row))
  rightBucket := fun gate column =>
    stableDominanceBucket (bucketSize := bucketSize)
      (stableDominanceRank leftScore rightScore gate (.inr column))
  comparison := by
    intro row gate column
    have hrank :
        stableDominanceRank leftScore rightScore gate (.inl row) <
            stableDominanceRank leftScore rightScore gate (.inr column) ↔
          leftScore row gate ≤ rightScore gate column :=
      stableDominanceRank_left_lt_right_iff
        leftScore rightScore row gate column
    constructor
    · intro hscore
      have hrankLt := hrank.mpr hscore
      have hbucketLe :=
        stableDominanceRank_lt_implies_bucket_le
          (bucketSize := bucketSize) hrankLt
      rcases hbucketLe.lt_or_eq with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, hscore⟩
    · rintro (hbucket | ⟨_, hscore⟩)
      · exact hrank.mp
          (stableDominanceBucket_lt_implies_rank_lt hbucket)
      · exact hscore

def bucketedWeightedDominance
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) (row : Rows) (column : Columns) : ℤ :=
  ∑ gate, weight gate *
    ((decide
      (layout.leftScore row gate ≤ layout.rightScore gate column) :
        Bool).toNat : ℤ)

def sameBucketContribution
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) (row : Rows) (column : Columns) : ℤ :=
  ∑ gate, if
      layout.leftBucket row gate = layout.rightBucket gate column ∧
        layout.leftScore row gate ≤ layout.rightScore gate column
    then weight gate else 0

def laterBucketContribution
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) (row : Rows) (column : Columns) : ℤ :=
  ∑ gate, if
      layout.leftBucket row gate < layout.rightBucket gate column
    then weight gate else 0

/-- Equation (B.3) is exactly the sum of the local scan and the rectangular
cross-bucket product; ties are wholly contained in the local term. -/
theorem bucketedWeightedDominance_eq_same_add_later
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) (row : Rows) (column : Columns) :
    bucketedWeightedDominance layout weight row column =
      sameBucketContribution layout weight row column +
        laterBucketContribution layout weight row column := by
  unfold bucketedWeightedDominance sameBucketContribution
    laterBucketContribution
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro gate _
  by_cases hlater :
      layout.leftBucket row gate < layout.rightBucket gate column
  · have hcomparison :
        layout.leftScore row gate ≤ layout.rightScore gate column :=
      (layout.comparison row gate column).2 (Or.inl hlater)
    have hne :
        layout.leftBucket row gate ≠ layout.rightBucket gate column :=
      ne_of_lt hlater
    simp [hlater, hcomparison, hne]
  · by_cases hsame :
      layout.leftBucket row gate = layout.rightBucket gate column ∧
        layout.leftScore row gate ≤ layout.rightScore gate column
    · have hcomparison :
          layout.leftScore row gate ≤ layout.rightScore gate column :=
        (layout.comparison row gate column).2 (Or.inr hsame)
      simp [hsame]
    · have hcomparison :
          ¬layout.leftScore row gate ≤ layout.rightScore gate column := by
        intro hcomparison
        rcases (layout.comparison row gate column).1 hcomparison with
          hcross | hlocal
        · exact hlater hcross
        · exact hsame hlocal
      simp [hlater, hcomparison]

/-- Canonical B.3 decomposition with no caller-supplied layout certificate. -/
theorem weightedDominance_eq_stable_same_add_later
    {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (bucketSize : ℕ) (weight : Fin Gates → ℤ)
    (row : Fin Rows) (column : Fin Columns) :
    weightedDominance leftScore rightScore weight row column =
      sameBucketContribution
          (stableBucketedDominanceLayout
            leftScore rightScore bucketSize)
          weight row column +
        laterBucketContribution
          (stableBucketedDominanceLayout
            leftScore rightScore bucketSize)
          weight row column := by
  exact bucketedWeightedDominance_eq_same_add_later
    (stableBucketedDominanceLayout leftScore rightScore bucketSize)
    weight row column

/-- Signed left matrix of the cross-bucket product, indexed by the genuine
occurrence pair `(gate,bucket)`. -/
def laterBucketLeft
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) :
    Rows → Gates × Fin Buckets → ℤ :=
  fun row index =>
    if index.2 = layout.leftBucket row index.1
    then weight index.1 else 0

/-- Boolean right matrix selecting buckets strictly earlier than the right
copy's bucket. -/
def laterBucketRight
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets) :
    Gates × Fin Buckets → Columns → Bool :=
  fun index column =>
    decide (index.2 < layout.rightBucket index.1 column)

def finiteSignedBooleanProduct
    {Rows Inner Columns : Type} [Fintype Inner]
    (left : Rows → Inner → ℤ) (right : Inner → Columns → Bool)
    (row : Rows) (column : Columns) : ℤ :=
  ∑ index, left row index * (right index column).toNat

/-- The cross-bucket term is one signed-by-Boolean product.  Each gate has
exactly one nonzero left bucket coordinate, so no coefficient is duplicated. -/
theorem laterBucketProduct_eq
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) (row : Rows) (column : Columns) :
    finiteSignedBooleanProduct
        (laterBucketLeft layout weight) (laterBucketRight layout)
        row column =
      laterBucketContribution layout weight row column := by
  unfold finiteSignedBooleanProduct laterBucketLeft laterBucketRight
    laterBucketContribution
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro gate _
  rw [Finset.sum_eq_single (layout.leftBucket row gate)]
  · by_cases hlater :
      layout.leftBucket row gate < layout.rightBucket gate column
    · simp [hlater]
    · simp [hlater]
  · intro bucket _ hbucket
    simp [hbucket]
  · simp

/-- Reindex the genuine pair coordinates into the rectangular backend's
contiguous inner dimension. -/
def reindexedLaterBucketLeft
    {Rows Gates Columns Buckets : ℕ}
    (layout :
      BucketedDominanceLayout (Fin Rows) (Fin Gates) (Fin Columns) Buckets)
    (weight : Fin Gates → ℤ) : IntMatrix Rows (Gates * Buckets) :=
  fun row index =>
    laterBucketLeft layout weight row (finProdFinEquiv.symm index)

def reindexedLaterBucketRight
    {Rows Gates Columns Buckets : ℕ}
    (layout :
      BucketedDominanceLayout (Fin Rows) (Fin Gates) (Fin Columns) Buckets) :
    BitMatrix (Gates * Buckets) Columns :=
  fun index column =>
    laterBucketRight layout (finProdFinEquiv.symm index) column

theorem reindexedLaterBucketProduct_eq
    {Rows Gates Columns Buckets : ℕ}
    (layout :
      BucketedDominanceLayout (Fin Rows) (Fin Gates) (Fin Columns) Buckets)
    (weight : Fin Gates → ℤ) :
    signedBooleanProduct
        (reindexedLaterBucketLeft layout weight)
        (reindexedLaterBucketRight layout) =
      fun row column =>
        laterBucketContribution layout weight row column := by
  funext row column
  unfold signedBooleanProduct reindexedLaterBucketLeft
    reindexedLaterBucketRight
  calc
    (∑ index,
      laterBucketLeft layout weight row (finProdFinEquiv.symm index) *
        (laterBucketRight layout
          (finProdFinEquiv.symm index) column).toNat) =
        ∑ index : Fin Gates × Fin Buckets,
          laterBucketLeft layout weight row index *
            (laterBucketRight layout index column).toNat := by
      exact Equiv.sum_comp finProdFinEquiv.symm
        (fun index : Fin Gates × Fin Buckets =>
          laterBucketLeft layout weight row index *
            (laterBucketRight layout index column).toNat)
    _ = laterBucketContribution layout weight row column :=
      laterBucketProduct_eq layout weight row column

/-- Zero padding into the imported rectangular-product inner dimension. -/
def padSignedInner {Rows Used Capacity : ℕ}
    (left : IntMatrix Rows Used) : IntMatrix Rows Capacity :=
  fun row index =>
    if hindex : index.val < Used
    then left row ⟨index.val, hindex⟩ else 0

def padBooleanInner {Used Capacity Columns : ℕ}
    (right : BitMatrix Used Columns) : BitMatrix Capacity Columns :=
  fun index column =>
    if hindex : index.val < Used
    then right ⟨index.val, hindex⟩ column else false

theorem signedBooleanProduct_padInner_eq
    {Rows Used Capacity Columns : ℕ}
    (hcapacity : Used ≤ Capacity)
    (left : IntMatrix Rows Used) (right : BitMatrix Used Columns) :
    signedBooleanProduct
        (padSignedInner (Capacity := Capacity) left)
        (padBooleanInner (Capacity := Capacity) right) =
      signedBooleanProduct left right := by
  funext row column
  unfold signedBooleanProduct
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hcapacity
  induction extra with
  | zero =>
      apply Finset.sum_congr rfl
      intro index _
      simp [padSignedInner, padBooleanInner]
  | succ extra inductionHypothesis =>
      rw [show Used + (extra + 1) = (Used + extra) + 1 by omega]
      rw [Fin.sum_univ_castSucc]
      have hhead :
          (∑ index : Fin (Used + extra),
            padSignedInner (Capacity := (Used + extra) + 1) left row
                index.castSucc *
              (padBooleanInner (Capacity := (Used + extra) + 1) right
                index.castSucc column).toNat) =
            ∑ index : Fin (Used + extra),
              padSignedInner (Capacity := Used + extra) left row index *
                (padBooleanInner (Capacity := Used + extra) right
                  index column).toNat := by
        apply Finset.sum_congr rfl
        intro index _
        simp only [padSignedInner, padBooleanInner, Fin.val_castSucc]
      rw [hhead, inductionHypothesis (by omega)]
      simp [padSignedInner, padBooleanInner, Fin.val_last]

/-! ## Occurrence-sensitive exact batch evaluation -/

/-- A monomial is a list, rather than a set, because the canonical expansion
in A.12.1 is occurrence-sensitive.  Repeated equations therefore remain
distinct coordinates while evaluation is their ordinary conjunction. -/
def exactMonomialValue {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomial : List Equation) (row : Row) (column : Column) : Bool :=
  monomial.all fun equation => holds equation row column

/-- Number of true monomial occurrences at one point. -/
def polynomialOccurrenceCount {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) : ℕ :=
  (monomials.map fun monomial =>
    (exactMonomialValue holds monomial row column).toNat).sum

/-- Evaluation of an explicitly represented `𝔽₂` polynomial.  This is total
on every row and column, including malformed upstream representations. -/
def exactPolynomialValue {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) : Bool :=
  decide (Odd (polynomialOccurrenceCount holds monomials row column))

/-! ### Canonical `𝔽₂` polynomial rows -/

/-- Expand one formal monomial into its literal occurrences.  Exponents are
retained as repeated entries: Boolean evaluation is unchanged, while degree
and printer syntax cannot be understated by silently squarefree-reducing. -/
noncomputable def monomialVariableOccurrences {Variable : Type}
    [DecidableEq Variable] (monomial : Variable →₀ ℕ) : List Variable :=
  monomial.support.toList.flatMap fun coordinate =>
    List.replicate (monomial coordinate) coordinate

theorem exactMonomialValue_variableOccurrences
    {Variable Row Column : Type} [DecidableEq Variable]
    (holds : Variable → Row → Column → Bool)
    (monomial : Variable →₀ ℕ) (row : Row) (column : Column) :
    exactMonomialValue holds (monomialVariableOccurrences monomial) row column =
      monomial.support.toList.all fun coordinate =>
        holds coordinate row column := by
  unfold monomialVariableOccurrences exactMonomialValue
  simp only [List.all_flatMap, List.all_replicate]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro hall coordinate hcoordinate
    have hpositive : monomial coordinate ≠ 0 :=
      Finsupp.mem_support_iff.mp (Finset.mem_toList.mp hcoordinate)
    simpa [hpositive] using hall coordinate hcoordinate
  · intro hall coordinate hcoordinate
    have hpositive : monomial coordinate ≠ 0 :=
      Finsupp.mem_support_iff.mp (Finset.mem_toList.mp hcoordinate)
    simpa [hpositive] using hall coordinate hcoordinate

theorem monomial_eval_eq_exactMonomialValue
    {Variable Row Column : Type} [DecidableEq Variable]
    (holds : Variable → Row → Column → Bool)
    (monomial : Variable →₀ ℕ) (row : Row) (column : Column) :
    (∏ coordinate ∈ monomial.support,
        ((holds coordinate row column).toNat : ZMod 2) ^
          monomial coordinate) =
      ((exactMonomialValue holds
        (monomialVariableOccurrences monomial) row column).toNat :
          ZMod 2) := by
  have hfactor : ∀ coordinate ∈ monomial.support,
      ((holds coordinate row column).toNat : ZMod 2) ^
          monomial coordinate =
        if holds coordinate row column = true then 1 else 0 := by
    intro coordinate hcoordinate
    have hpositive : monomial coordinate ≠ 0 :=
      Finsupp.mem_support_iff.mp hcoordinate
    cases holds coordinate row column <;> simp [hpositive]
  calc
    (∏ coordinate ∈ monomial.support,
        ((holds coordinate row column).toNat : ZMod 2) ^
          monomial coordinate) =
        ∏ coordinate ∈ monomial.support,
          if holds coordinate row column = true then 1 else 0 := by
            apply Finset.prod_congr rfl
            intro coordinate hcoordinate
            exact hfactor coordinate hcoordinate
    _ = if ∀ coordinate ∈ monomial.support,
          holds coordinate row column = true then 1 else 0 :=
      Finset.prod_boole
    _ = ((exactMonomialValue holds
        (monomialVariableOccurrences monomial) row column).toNat :
          ZMod 2) := by
      rw [exactMonomialValue_variableOccurrences]
      by_cases hall : ∀ coordinate ∈ monomial.support,
          holds coordinate row column = true
      · have hallList :
            (monomial.support.toList.all fun coordinate =>
              holds coordinate row column) = true := by
          rw [List.all_eq_true]
          intro coordinate hcoordinate
          exact hall coordinate (Finset.mem_toList.mp hcoordinate)
        rw [if_pos hall, hallList]
        rfl
      · have hallList :
            (monomial.support.toList.all fun coordinate =>
              holds coordinate row column) = false := by
          apply Bool.eq_false_iff.mpr
          intro htrue
          apply hall
          rw [List.all_eq_true] at htrue
          intro coordinate hcoordinate
          exact htrue coordinate (Finset.mem_toList.mpr hcoordinate)
        rw [if_neg hall, hallList]
        rfl

/-- Canonical occurrence-sensitive expansion of a finite `𝔽₂` polynomial.
Support membership removes zero coefficients; every surviving coefficient is
one because the coefficient ring is `ZMod 2`. -/
noncomputable def polynomialMonomialOccurrences
    {Variable : Type} [DecidableEq Variable]
    (polynomial : MvPolynomial Variable (ZMod 2)) :
    List (List Variable) :=
  polynomial.support.toList.map monomialVariableOccurrences

theorem zmodTwo_coeff_eq_one_of_mem_support
    {Variable : Type}
    (polynomial : MvPolynomial Variable (ZMod 2))
    (monomial : Variable →₀ ℕ) (hmonomial : monomial ∈ polynomial.support) :
    polynomial.coeff monomial = 1 := by
  classical
  have hnonzero : polynomial.coeff monomial ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmonomial
  have hvalNonzero : (polynomial.coeff monomial).val ≠ 0 := by
    intro hzero
    exact hnonzero ((ZMod.val_eq_zero _).mp hzero)
  apply (ZMod.val_eq_one (by norm_num) _).mp
  have hlt := ZMod.val_lt (polynomial.coeff monomial)
  omega

theorem polynomialOccurrenceCount_variableOccurrences
    {Variable Row Column : Type} [DecidableEq Variable]
    (holds : Variable → Row → Column → Bool)
    (polynomial : MvPolynomial Variable (ZMod 2))
    (row : Row) (column : Column) :
    polynomialOccurrenceCount holds
        (polynomialMonomialOccurrences polynomial) row column =
      ∑ monomial ∈ polynomial.support,
        (exactMonomialValue holds
          (monomialVariableOccurrences monomial) row column).toNat := by
  unfold polynomialOccurrenceCount polynomialMonomialOccurrences
  simp [Function.comp_def, Finset.sum_map_toList]

theorem aeval_polynomial_eq_occurrenceCount
    {Variable Row Column : Type} [DecidableEq Variable]
    (holds : Variable → Row → Column → Bool)
    (polynomial : MvPolynomial Variable (ZMod 2))
    (row : Row) (column : Column) :
    MvPolynomial.aeval
        (fun coordinate =>
          ((holds coordinate row column).toNat : ZMod 2))
        polynomial =
      (polynomialOccurrenceCount holds
        (polynomialMonomialOccurrences polynomial) row column :
          ZMod 2) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
    polynomialOccurrenceCount_variableOccurrences]
  push_cast
  apply Finset.sum_congr rfl
  intro monomial hmonomial
  rw [zmodTwo_coeff_eq_one_of_mem_support polynomial monomial hmonomial,
    map_one, one_mul, monomial_eval_eq_exactMonomialValue]

/-- The generic row consumed by the exact-score printer is definitionally the
Boolean value of the source `𝔽₂` polynomial after canonical expansion. -/
theorem exactPolynomialValue_compiled
    {Variable Row Column : Type} [DecidableEq Variable]
    (holds : Variable → Row → Column → Bool)
    (polynomial : MvPolynomial Variable (ZMod 2))
    (row : Row) (column : Column) :
    exactPolynomialValue holds
        (polynomialMonomialOccurrences polynomial) row column =
      decide
        (MvPolynomial.aeval
          (fun coordinate =>
            ((holds coordinate row column).toNat : ZMod 2))
          polynomial = 1) := by
  unfold exactPolynomialValue
  rw [aeval_polynomial_eq_occurrenceCount]
  exact decide_eq_decide.mpr ZMod.natCast_eq_one_iff_odd.symm

/-- The desired exact Boolean column count. -/
def exactColumnCount {Row Column Equation : Type} [Fintype Row]
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (column : Column) : ℕ :=
  ∑ row, (exactPolynomialValue holds monomials row column).toNat

end NearCubicWires.SupplierPrinter
