import Proof.Supplier.SupplierWalkBridge
import Proof.MachineModel.OrdinarySignedSortKey

/-! Literal bit addresses of the original Toeplitz walk encoding. The padding
coordinate is the low part of finProdFinEquiv, so physical decoding must discard
its low bits before splitting lower/upper/translation fields. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Completion.ToeplitzSeedBits
open NearCubicWires NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary


theorem finEquiv_symm_val {n : Nat} [NeZero n] (x : ZMod n) :
    ((ZMod.finEquiv n).symm x).val=x.val := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n => rfl

end Completion.ToeplitzSeedBits
