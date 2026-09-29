import Proof.Supplier.RowIndexField

/-! A physical ordered index field selects a coordinate from the retained
child cache and appends its signed radix block. The stream remains at the
next occurrence, including when adjacent indices are equal. -/
namespace NearCubicWires.RepairOrdinary.RowOccurrenceAppend
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2 → Fin 24 := ![23,19]
noncomputable def first := RecoveryFocus.machine slots RowIndexField.machine
noncomputable def last := TapeEmbedding.machine 1 RowCachedCoordinateReusable.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowOccurrenceAppend
