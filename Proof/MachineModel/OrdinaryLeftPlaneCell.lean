import Proof.MachineModel.OrdinaryInterval

/-! The interval scan at the exact positive/negative coefficient bit of the
paper's left cross-bucket matrix. Boundary and coefficient-bit production
remain explicit caller operations. -/
namespace NearCubicWires.RepairOrdinary.LeftPlaneCell
open LocalBitMultitape SupplierPrinter SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficientBit (negative : Bool) (value : ℤ) (bit : ℕ) : Bool :=
  if negative then negativeMagnitudeBit value bit else positiveMagnitudeBit value bit

@[simp] theorem coefficient_zero (negative : Bool) (bit : ℕ) : coefficientBit negative 0 bit = false := by
  cases negative <;> simp [coefficientBit, negativeMagnitudeBit, positiveMagnitudeBit]

theorem left_bit {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ) (bucketSize : ℕ)
    (gate : Fin Gates) (bucket : Fin (stableDominanceBucketCount Rows Columns bucketSize))
    (row : Fin Rows) (negative : Bool) (bit : ℕ) :
    coefficientBit negative
        (laterBucketLeft (stableBucketedDominanceLayout leftScore rightScore bucketSize) weight row (gate, bucket)) bit =
      ((decide (bucket.val * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val) &&
        !decide ((bucket.val + 1) * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val)) &&
        coefficientBit negative (weight gate) bit) := by
  rw [BucketBoundary.left_cell]
  by_cases hlo : bucket.val * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val <;>
    by_cases hhi : (bucket.val + 1) * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val <;>
      simp [hlo, hhi]

end NearCubicWires.RepairOrdinary.LeftPlaneCell
