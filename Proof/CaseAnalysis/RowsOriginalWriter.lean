import Proof.CaseAnalysis.RowsOriginalBlock
import Proof.CaseAnalysis.RowsEstimatorSubstitutionDock
import Proof.CaseAnalysis.RowsOriginalTemplates

/-! A fixed source-test template copies its runtime proof-coordinate
indices in order, including repeats, then writes the factor terminator. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalWriter
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsEstimator CloseoutRowsTupleSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (side : Fin 2) : Fin 3→Fin 4:=![side.castAdd 2,2,3]
noncomputable def one (side : Fin 2):=RecoveryFocus.machine (slots side) CloseoutRowsOriginalBlock.machine
def finishSlots : Fin 2→Fin 4:=![0,2]
noncomputable def finish:=RecoveryFocus.machine finishSlots (CloseoutRowsOriginalBlock.mark false)
noncomputable def program : List (Fin 2)→Σ s,Machine 4 s
  | []=>⟨_,finish⟩
  | side::rest=>⟨_,Composition.machine (one side) (program rest).2⟩
noncomputable def machine (factors : List (Fin 2)):= (program factors).2

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalWriter
