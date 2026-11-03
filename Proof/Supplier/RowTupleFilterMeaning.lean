import Proof.Supplier.RowTupleFilterBody

/-! The accumulated flag of the physical digit body means exactly the
positional subset predicate used by the row expansion. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFilterMeaning
open RowTupleFilterParts RowTupleFilterBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def initial (source : List Bool) (M : ℕ) : Data :=
  ⟨source,0,M-1,0,false,false,false,true⟩

end NearCubicWires.RepairOrdinary.RowTupleFilterMeaning
