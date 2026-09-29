import Proof.CaseAnalysis.RowsModeHashCell
import Proof.CaseAnalysis.RowsModeHashReady

/-! A paid actual hash-cell scan returns the bitmap and original level
heads. Its three physical flags remain available to the literal Pair writer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashGuard
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsModeHashCell
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine:=MaskedReset.machine CloseoutRowsModeHashCell.machine (fun _=>true)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashGuard
