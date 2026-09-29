import Proof.Supplier.RowTupleCutAppend

/-! The actual selected tuple stream emits every complete signed cut,
reusing one cached coefficient and retaining the whole-row append cursor. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCutList
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding RowTupleCommonEquation
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.RowTupleCutList
