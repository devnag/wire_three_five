import Proof.Supplier.RowTupleFilterMeaning

/-! The retained unary degree driver executes one checked digit body per
digit. Only the short degree is unary; the tuple enumeration count is binary. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFilterLoop
open LocalBitMultitape RecoveryExecution RowTupleFilterParts RowTupleFilterBody
open RowTupleFilterMeaning SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine RowTupleFilterBody.machine (fun _ _=>true)

end NearCubicWires.RepairOrdinary.RowTupleFilterLoop
