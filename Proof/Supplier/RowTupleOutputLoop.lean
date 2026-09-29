import Proof.Supplier.RowTupleOutputMeaning

/-! Exhaust the fixed-width binary cursor, emitting each selected positional
candidate exactly once. The exponential candidate count has no unary tape. -/
namespace NearCubicWires.RepairOrdinary.RowTupleOutputLoop
open LocalBitMultitape RecoveryExecution RowTupleFilterParts RowTupleOutputParts
open RowTupleOutputBody RowTupleOutputMeaning SignedSortKey
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := StreamController.machine RowTupleOutputBody.machine 15


end NearCubicWires.RepairOrdinary.RowTupleOutputLoop
