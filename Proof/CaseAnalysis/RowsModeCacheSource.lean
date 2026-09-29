import Proof.CaseAnalysis.RowsModeCacheInit

/-! Whole actual cache population from original numeric/seed/mask fields,
including its own unary-index initialization and head-zero loop entry. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def sourceMachine (mode : Fin 3):=Composition.machine initMachine (machine mode)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
