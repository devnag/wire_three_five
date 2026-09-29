import Proof.CaseAnalysis.RowsLoopLayout

/-! The accepted degree pass, four small updates and six metadata copies
return exactly the next pass's boundary, including the append cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsLoopBoundary
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutRowsLoopBoundary
