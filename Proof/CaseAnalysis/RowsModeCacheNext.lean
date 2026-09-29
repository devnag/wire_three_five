import Proof.CaseAnalysis.RowsModeCachePair

/-! The real binary label advances, then just the three private hash fields
are cleared from the paid original capacity. The next population body reuses
all original seed, mask, level, index and count fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def labelMachine:=RecoveryFocus.machine labelSlots (Rewind.machine BinaryIncrement.machine)
noncomputable def eraseMachine:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 3)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
