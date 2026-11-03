import Proof.Supplier.RowTupleFixedCapacity
import Proof.Supplier.RowTupleCursorReady

/-! The complete equation body consumes one tuple at its retained stream
cursor. Its exact final configuration exposes the ports needed to clear
only the per-tuple data before the next selected tuple. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCursorEquation
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := RecoveryFocus.machine tupleSlots RowTupleCursorReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots RowCommonCoordinateLoop.machine
noncomputable def machine := Composition.machine first last


end NearCubicWires.RepairOrdinary.RowTupleCursorEquation
