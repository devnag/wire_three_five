import Proof.Supplier.RowTupleOutputLoop

/-! The complete binary subset enumerator starts at zero and stops at the
first out-of-range counter. Its stream lists every selected occurrence once. -/
namespace NearCubicWires.RepairOrdinary.RowTupleEnumeration
open LocalBitMultitape RowTupleFilterParts RowTupleFilterMeaning RowTupleOutputParts
open RowTupleOutputBody RowTupleOutputMeaning RowTupleDigits RowTupleSubsets SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def start (w k M : ℕ) := initial (frame (binary (w*k+1) 0)) M

end NearCubicWires.RepairOrdinary.RowTupleEnumeration
