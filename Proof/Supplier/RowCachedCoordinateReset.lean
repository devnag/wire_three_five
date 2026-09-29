import Proof.Supplier.RowCachedCoordinateAppend

/-! Paid reset of the original cache cursor and the two positioner scratch
heads after a selected coordinate append. Existing width/selection drivers
and both live P/N append cursors are retained exactly. -/
namespace NearCubicWires.RepairOrdinary.RowCachedCoordinateReset
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 20) := decide (i=0 ∨ i=16 ∨ i=17)
noncomputable def machine := MaskedReset.machine RowCachedCoordinateAppend.machine selected


end NearCubicWires.RepairOrdinary.RowCachedCoordinateReset
