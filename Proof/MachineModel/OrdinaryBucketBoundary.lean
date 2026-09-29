import Proof.MachineModel.OrdinaryCompare

/-! Exact bucket predicates as rank-boundary comparisons. This retains the
existing bucket size and layout; no alternative partition is introduced.
The right cross-matrix cell is produced by an actual bounded-word scan. -/
namespace NearCubicWires.RepairOrdinary.BucketBoundary
open LocalBitMultitape SupplierPrinter SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem later (rank bucketSize bucket : ℕ) :
    bucket < rank / (bucketSize + 1) ↔ (bucket + 1) * (bucketSize + 1) ≤ rank := by
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le (Nat.succ_pos _)]

theorem same (rank bucketSize bucket : ℕ) :
    rank / (bucketSize + 1) = bucket ↔
      bucket * (bucketSize + 1) ≤ rank ∧ ¬(bucket + 1) * (bucketSize + 1) ≤ rank := by
  have hlo : bucket ≤ rank / (bucketSize + 1) ↔ bucket * (bucketSize + 1) ≤ rank :=
    Nat.le_div_iff_mul_le (Nat.succ_pos _)
  have hhi := later rank bucketSize bucket
  omega

theorem right_cell {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (bucketSize : ℕ) (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns bucketSize)) (column : Fin Columns) :
    laterBucketRight (stableBucketedDominanceLayout leftScore rightScore bucketSize) (gate, bucket) column =
      decide ((bucket.val + 1) * (bucketSize + 1) ≤
        (stableDominanceRank leftScore rightScore gate (.inr column)).val) := by
  simp only [laterBucketRight, stableBucketedDominanceLayout, Fin.lt_def, stableDominanceBucket, later]

theorem left_cell {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ) (bucketSize : ℕ) (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns bucketSize)) (row : Fin Rows) :
    laterBucketLeft (stableBucketedDominanceLayout leftScore rightScore bucketSize) weight row (gate, bucket) =
      if bucket.val * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val ∧
        ¬(bucket.val + 1) * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val
      then weight gate else 0 := by
  have he : bucket = (stableBucketedDominanceLayout leftScore rightScore bucketSize).leftBucket row gate ↔
      bucket.val * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val ∧
        ¬(bucket.val + 1) * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val := by
    rw [Fin.ext_iff]
    change bucket.val = (stableDominanceRank leftScore rightScore gate (.inl row)).val / (bucketSize + 1) ↔ _
    rw [eq_comm, same]
  simp only [laterBucketLeft, he]

end NearCubicWires.RepairOrdinary.BucketBoundary
