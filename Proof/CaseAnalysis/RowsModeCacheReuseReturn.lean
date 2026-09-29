import Proof.CaseAnalysis.RowsModeCacheReuseClear

/-! One complete cache pass returns every head except the live append.
The paid recording capacity is separate from the hash workspace capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reuseSelected (i : Fin 25):=decide (i≠20)
noncomputable def reuseReturn (mode : Fin 3):=
  TapeEmbedding.machine 2 (MaskedReset.machine (sourceMachine mode) reuseSelected)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
