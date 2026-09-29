import Proof.Supplier.RowTupleFilterReusable

/-! Each candidate begins with two physical flag writes, then runs the
reusable tuple filter. Neither its saved digits nor its work bank is rebuilt. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCandidate
open LocalBitMultitape RecoveryExecution RowTupleFilterParts RowTupleFilterBody
open RowTupleFilterMeaning RowTupleFilterReusable SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def startMachine : Machine 14 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,
    fun i=>if i=8 then some false else if i=9 then some true else none,fun _=>.stay⟩ else none
noncomputable def machine := Composition.machine startMachine RowTupleFilterReusable.machine

end NearCubicWires.RepairOrdinary.RowTupleCandidate
