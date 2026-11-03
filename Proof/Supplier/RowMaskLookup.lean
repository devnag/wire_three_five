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

def budget (N w d : ℕ) := d*(2*N+8*w+15)+8*w+14+N*(4*N+21)

end NearCubicWires.RepairOrdinary.RowMaskLookup
