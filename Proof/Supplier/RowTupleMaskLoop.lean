import Proof.Supplier.RowTupleMaskBody

/-! The short degree driver executes every selected monomial lookup in
tuple order. The physical occurrence stream and count accumulate in place. -/
namespace NearCubicWires.RepairOrdinary.RowTupleMaskLoop
open LocalBitMultitape RecoveryExecution SignedSortKey RowMaskPositionParts
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine RowTupleMaskBody.machine (fun _ _=>true)

end NearCubicWires.RepairOrdinary.RowTupleMaskLoop
