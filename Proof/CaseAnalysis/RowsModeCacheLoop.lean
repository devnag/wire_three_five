import Proof.CaseAnalysis.RowsModeCacheBody

/-! The retained original population driver repeats the whole physical
cache body, preserving pair order, including an empty population. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (mode : Fin 3):=CloseoutRowsDegreeLoop.machine (body mode)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
