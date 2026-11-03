import Proof.CaseAnalysis.RowsModeCacheHash
import Proof.CaseAnalysis.RowsTupleSeekDock

/-! The actual computed flags and live original mask cursor enter the
literal pair writer; the child count remains independent of the mask. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def selectMachine (mode : Fin 3):=RecoveryFocus.machine selectSlots (CloseoutRowsModeLiteralSelect.machine mode)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
