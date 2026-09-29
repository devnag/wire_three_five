import Proof.CaseAnalysis.RowsModeCacheNext

/-! One whole actual original-seed occurrence pass computes the hash, reads
the same original mask, appends its exact literal pair, and returns its bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first:=Composition.machine hashMachine guardMachine
noncomputable def second (mode : Fin 3):=Composition.machine first (selectMachine mode)
noncomputable def third (mode : Fin 3):=Composition.machine (second mode) pairMachine
noncomputable def fourth (mode : Fin 3):=Composition.machine (third mode) cursorMachine
noncomputable def fifth (mode : Fin 3):=Composition.machine (fourth mode) labelMachine
noncomputable def body (mode : Fin 3):=Composition.machine (fifth mode) eraseMachine


end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
