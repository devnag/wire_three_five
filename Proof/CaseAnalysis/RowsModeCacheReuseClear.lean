import Proof.CaseAnalysis.RowsModeCacheReuseLayout

/-! One actual simultaneous erase prepares every private cache field.
Original inputs, the append output and the head-return log are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def reuseClear:=RecoveryFocus.machine reuseEraseSlots (RecoveryScratchErase.resetMachine 15)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
