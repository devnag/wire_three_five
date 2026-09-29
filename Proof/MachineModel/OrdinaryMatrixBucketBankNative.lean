import Proof.MachineModel.OrdinaryMatrixBatchBucketBank
import Proof.MachineModel.OrdinaryKeyBuckets

/-! The produced scalar bank is exactly the ordinary bucket machine's
native entry storage, with finite paid zero padding on every work tape. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketBankNative
open LocalBitMultitape SignedSortKey MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pad_zeros (D n : ℕ) (hn : n ≤ D) :
    ZeroPadding.pad D (List.replicate n false)=List.replicate D false := by
  simp [ZeroPadding.pad,Nat.add_sub_of_le hn]

end NearCubicWires.RepairOrdinary.MatrixBucketBankNative
