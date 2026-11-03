import Proof.CaseAnalysis.RowsRawAtomReusable
import Proof.CaseAnalysis.RowsEstimatorSubstitutionFactorLayout

/-! The original family cache has one polynomial per sum. Its actual
reader returns both cache and appended atom cursors before multiplication. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalCache
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawAtomSeek CloseoutRowsEstimator
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := MaskedReset.machine CloseoutRowsRawAtomReusable.machine (fun i=>decide (i=2))

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalCache
