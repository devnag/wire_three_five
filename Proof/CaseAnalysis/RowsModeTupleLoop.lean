import Proof.CaseAnalysis.RowsModeTupleDigit
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.Supplier.RowTupleFilterLoop

/-! The paid degree driver consumes the actual tuple digits and appends
their raw index blocks in order. The private binary copy is reused. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleLoop
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open RepairSource.VerifierDecoding
open CloseoutRowsModeTupleDigit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RepeatMachine.machine CloseoutRowsModeTupleDigit.machine (fun _ _=>true)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleLoop
