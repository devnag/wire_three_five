import Proof.CaseAnalysis.RowsDegreeClean
import Proof.CaseAnalysis.RowsCutMeaning

/-! Actual fixed-degree cut production followed by paid scratch reuse.
The native cache and the row append cursor survive; the next call reloads
only degree metadata into the erased work bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsReusableCuts
open LocalBitMultitape RecoveryExecution CloseoutRowsDegreeReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := CloseoutRowsDegreeClean.machine CloseoutRowsComputedCuts.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsReusableCuts
