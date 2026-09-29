import Proof.Supplier.RowTupleEnumeration

/-! The enumerator allocates its short scratch tapes by real writes during
execution. Its initial workspace and flags are empty, and driver positioning
and true flags are supplied by one physical transition. -/
namespace NearCubicWires.RepairOrdinary.RowTupleColdLogs
open LocalBitMultitape RecoveryExecution RowTupleOutputParts RowTupleEnumeration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagMachine : Machine 18 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,
    fun i=>if i=9 ∨ i=15 then some true else none,
    fun i=>if i=2 ∨ i=12 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine flagMachine RowTupleOutputLoop.machine

end NearCubicWires.RepairOrdinary.RowTupleColdLogs
