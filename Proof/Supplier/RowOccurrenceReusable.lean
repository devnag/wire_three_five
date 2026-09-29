import Proof.Supplier.RowOccurrenceAppend
import Proof.Supplier.RowOccurrenceClear

/-! Repeated occurrence call on the same24-tape bank. The child index is
physically cleared with the existing capacity driver, while the ordered
occurrence cursor and both coefficient append cursors remain advanced. -/
namespace NearCubicWires.RepairOrdinary.RowOccurrenceReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine RowOccurrenceAppend.machine RowOccurrenceClear.machine

end NearCubicWires.RepairOrdinary.RowOccurrenceReusable
