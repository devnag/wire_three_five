import Proof.CaseAnalysis.RowsOriginalProducer
import Proof.CaseAnalysis.RowsOriginalTemplateSlots
import Proof.CaseAnalysis.RowsOriginalSwitch

/-! Native sign and auxiliary flags select the exact fixed paper template.
All branches execute the same original-term product and metadata pipeline. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalBranches
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsOriginalTemplates CloseoutRowsRawAtomSeek
open CloseoutRowsOriginalMonomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body (r : Row):=TapeEmbedding.machine 4 (CloseoutRowsOriginalProducer.machine r)
noncomputable def penalty (side : Fin 2) (j : Fin 3):=CloseoutRowsOriginalSwitch.machine
  (body (penaltySlot true side j)) (body (penaltySlot false side j)) (Fin.natAdd 18 (Fin.natAdd 2 side))
noncomputable def signedRight (a : Bool) (j : Fin 3):=CloseoutRowsOriginalSwitch.machine
  (body (clauseSlot a true j)) (body (clauseSlot a false j)) 19
noncomputable def clause (j : Fin 3):=CloseoutRowsOriginalSwitch.machine (signedRight true j) (signedRight false j) 18

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalBranches
