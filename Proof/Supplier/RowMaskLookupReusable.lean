import Proof.Supplier.RowMaskLookup
import Proof.Supplier.RowMaskBankClear

/-! Reusable selected-mask lookup: actual positioning, occurrence emission,
local erasure, and a recorded return of only the cache cursor. -/
namespace NearCubicWires.RepairOrdinary.RowMaskLookupReusable
open LocalBitMultitape RecoveryExecution RowMaskPositionParts RowMaskConsume
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body := Composition.machine RowMaskLookup.machine RowMaskBankClear.machine
def selected (i : Fin 9) : Bool := decide (i=0)
noncomputable def machine := MaskedReset.machine body selected
def capacity (N w M : ℕ) := RowMaskLookup.budget N w M+2*N+4*w+8


end NearCubicWires.RepairOrdinary.RowMaskLookupReusable
