import Proof.Supplier.RowCachedCoordinateBounds

/-! An ordered occurrence-index field is raw unary with a false delimiter.
Its reader physically writes the existing sentinel template, retaining the
source cursor and every occurrence. This is an internal controller stream. -/
namespace NearCubicWires.RepairOrdinary.RowIndexField
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (n : ℕ) := List.replicate n true++[false]
def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then
    some ⟨1,![none,some false],![.stay,.right]⟩
    else if q.val=1 then some (if bits 0 then
      ⟨1,![none,some true],![.right,.right]⟩
      else ⟨2,![none,some false],![.right,.left]⟩)
    else if q.val=2 then some (if bits 1 then
      ⟨2,fun _=>none,![.stay,.left]⟩ else ⟨3,fun _=>none,![.stay,.right]⟩)
    else none

end NearCubicWires.RepairOrdinary.RowIndexField
