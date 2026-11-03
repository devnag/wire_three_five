import Proof.CaseAnalysis.RowsRawAtomRound
import Proof.Amplification.RecoveryCursorCalls

/-! The actual source-produced child count controls the absolute-index
stream directly. It is not copied into an additional enumeration driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskBodyParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def indices (offset n : ℕ) : List (List ℕ):=(List.range' offset n).map (fun i=>[i])

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomLoop
