import Proof.CaseAnalysis.RowsModeElementaryReuse

/-! One actual reusable elementary call reloads the four numeric fields,
executes the complete cold subset writer, returns its heads, and clears its
work bank. The same retained C driver pays all four phases. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReusable
open LocalBitMultitape
open CloseoutRowsModeElementaryLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine CloseoutRowsModeElementaryReload.machine
  CloseoutRowsModeElementaryReuse.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReusable
