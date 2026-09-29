import Proof.MachineModel.OrdinaryMatrixRightInputs

/-! The paid right sorting/selection program at the paper's exact B.3
bucket layout. Rank-labelled generation and its outer handoff stay explicit. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightPaper
open LocalBitMultitape SupplierPrinter CoordinateKey
open WilliamsLoaderForms (rowMajorBitMatrix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def payload {U Gates : ℕ} (bucketSize : ℕ) (leftScore : IntMatrix U Gates) (rightScore : IntMatrix Gates U)
    (index : Fin (Gates*stableDominanceBucketCount U U bucketSize)) (id : Fin (U+U)) : Bool :=
  let p := finProdFinEquiv.symm index
  decide ((p.2.val+1)*(bucketSize+1) ≤
    (stableDominanceRank leftScore rightScore p.1 (finSumFinEquiv.symm id)).val)

theorem right_eq {U Gates : ℕ} (bucketSize : ℕ) (leftScore : IntMatrix U Gates) (rightScore : IntMatrix Gates U) :
    MatrixRightGrid.right (payload bucketSize leftScore rightScore)=
      reindexedLaterBucketRight (stableBucketedDominanceLayout leftScore rightScore bucketSize) := by
  funext index column
  simpa only [MatrixRightGrid.right,payload,reindexedLaterBucketRight,finSumFinEquiv_symm_apply_natAdd] using
    (BucketBoundary.right_cell leftScore rightScore bucketSize
      (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2 column).symm

end NearCubicWires.RepairOrdinary.MatrixRightPaper
