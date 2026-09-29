import Proof.CaseAnalysis.RowsModeCacheLayout

/-! The cache body computes the original seed hash and actual cell flags.
Only the fixed hash work bank and three singleton flags are touched. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def hashMachine:=TapeEmbedding.machine 13 CloseoutRowsModeHashReady.machine
noncomputable def guardMachine:=RecoveryFocus.machine guardSlots CloseoutRowsModeHashGuard.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
