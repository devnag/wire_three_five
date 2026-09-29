import Proof.Supplier.RowFieldPaddingAppend

/-! The tuple enumerator advances a bounded binary cursor on four retained
tapes. A real transition clears the previous continuation flag before the
checked increment/comparison call. The enumeration count is never unary. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCounter
open LocalBitMultitape RecoveryExecution SignedSortKey
open WitnessCounterCheck (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clear : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,![none,none,some false,none],fun _=>.stay⟩ else none
def machine := Composition.machine clear WitnessCounterAdvance.machine

end NearCubicWires.RepairOrdinary.RowTupleCounter
