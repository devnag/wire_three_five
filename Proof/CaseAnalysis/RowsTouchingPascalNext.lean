import Proof.CaseAnalysis.RowsTouchingFrameStream
import Proof.CaseAnalysis.RowsTouchingPascalCell

/-! One complete Pascal transition copies its existing leading one and
runs the q exact additions. The input rows remain untouched, and the new
row appends to the same complete table prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalNext
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch SignedSortKey
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalNext
