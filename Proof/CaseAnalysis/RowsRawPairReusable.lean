import Proof.CaseAnalysis.RowsRawPairRead

/-! Universal substitution reuses the SAME adjacent X/C cache. The paid
masked return restores its cursor; the original occurrence index and output
cursors remain live. Its time depends on logical cache bytes, never padding. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPairReusable
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine CloseoutRowsRawPairRead.machine (fun i=>decide (i=1))


end NearCubicWires.RepairOrdinary.CloseoutRowsRawPairReusable
