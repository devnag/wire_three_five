import Proof.CaseAnalysis.RowsOriginalBranches

/-! The finite source-test schedule uses six penalty slots, one left
second-moment slot, and three signed-clause slots. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTask
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsOriginalTemplates CloseoutRowsOriginalBranches
open CloseoutRowsOriginalMonomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

inductive Task where
  | penalty (side : Fin 2) (slot : Fin 3)
  | moment
  | clause (slot : Fin 3)

def row : Task→(Fin 4→Bool)→Row
  | .penalty side j,bits=>penaltySlot (bits (Fin.natAdd 2 side)) side j
  | .moment,_=>plain 1 [0,0]
  | .clause j,bits=>clauseSlot (bits 0) (bits 1) j

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTask
