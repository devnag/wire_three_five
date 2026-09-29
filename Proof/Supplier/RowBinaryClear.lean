import Proof.Supplier.RowMaskMeaning

/-! Reset a short binary row cursor by real writes, preserving every frame
marker and reusing the same bounded reset log as counter advancement. -/
namespace NearCubicWires.RepairOrdinary.RowBinaryClear
open LocalBitMultitape RecoveryExecution RecoveryRootRound Streaming SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q bits=>if q.val=0 then some (if bits 0 then
    ⟨1,fun _=>none,fun _=>.right⟩ else ⟨2,fun _=>none,fun _=>.stay⟩)
    else if q.val=1 then some ⟨0,fun _=>some false,fun _=>.right⟩ else none


def machine := Rewind.machine raw

end NearCubicWires.RepairOrdinary.RowBinaryClear
