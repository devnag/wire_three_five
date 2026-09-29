import Proof.CaseAnalysis.RowsModeCacheReuseReturn

/-! Repeated physical cache production, including both ordered delta halves.
The preceding result's private backing is retired by the next actual call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def reuseMachine (mode : Fin 3):=Composition.machine reuseClear (reuseReturn mode)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
