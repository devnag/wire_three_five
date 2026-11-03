import Proof.CaseAnalysis.RowsRawAtomCache

/-! Substitution reuses one actual atom cache. The existing paid masked
return restores its cursor; the variable and output cursors remain live. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomReusable
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawAtomSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine CloseoutRowsRawAtomRead.machine (fun i=>decide (i=1))

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomReusable
