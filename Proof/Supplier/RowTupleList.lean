import Proof.Supplier.RowTupleFrame

/-! Execute every actual selected tuple frame, without a supplied unary
frame count. The physical stream marker controls entry and termination;
all equations append in the enumerator's exact occurrence order. -/
namespace NearCubicWires.RepairOrdinary.RowTupleList
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding RowTupleCommonEquation
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.RowTupleList
