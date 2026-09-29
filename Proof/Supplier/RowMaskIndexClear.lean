import Proof.Supplier.RowMaskPositionParts

/-! Erase the occurrence-index template using the retained mask-length
template. Both heads return to one and no fresh reset allocation is needed. -/
namespace NearCubicWires.RepairOrdinary.RowMaskIndexClear
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q bits=>if q.val=0 then some (if bits 1 then
    ⟨0,![some false,none],fun _=>.right⟩ else ⟨1,fun _=>none,fun _=>.left⟩)
    else if q.val=1 then some (if bits 1 then
      ⟨1,fun _=>none,fun _=>.left⟩ else ⟨2,fun _=>none,fun _=>.right⟩) else none

end NearCubicWires.RepairOrdinary.RowMaskIndexClear
