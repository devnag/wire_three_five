import Proof.Supplier.RowMaskPositionLoop
import Proof.Supplier.RowMaskConsume
import Proof.Supplier.RowMaskIndexClear

/-! The complete selected-mask lookup physically positions the retained
cache and appends the chosen native occurrences in its existing output bank. -/
namespace NearCubicWires.RepairOrdinary.RowMaskLookup
open LocalBitMultitape RecoveryExecution RowMaskPositionParts RowMaskConsume
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine RowMaskPositionLoop.machine RowMaskConsume.machine


end NearCubicWires.RepairOrdinary.RowMaskLookup
