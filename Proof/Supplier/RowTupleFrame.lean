import Proof.Supplier.RowTupleCursorBody

/-! Consume the exact checked enumerator grammar. Each selected tuple has
its ordinary digit blocks followed by the extra zero bit and terminator;
the three corresponding physical cells are passed by paid transitions. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFrame
open LocalBitMultitape RecoveryExecution SignedSortKey RowTupleDigits
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def skip : Machine 48 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==3
  rule:=fun q _=>if h:q.val<3 then some
    ⟨⟨q.val+1,by omega⟩,fun _=>none,fun i=>if i=44 then .right else .stay⟩ else none

end NearCubicWires.RepairOrdinary.RowTupleFrame
