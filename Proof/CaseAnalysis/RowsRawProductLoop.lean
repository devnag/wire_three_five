import Proof.CaseAnalysis.RowsRawProductBody

/-! The actual two raw polynomial streams determine the full Cartesian
product. The left and right stream loops create every original monomial
occurrence once, including empty inputs, before one final stream marker. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsRawProductBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 5 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
noncomputable def finish:=TapeEmbedding.machine 1 (CloseoutRowsRawProductFields.mark false false)
noncomputable def sizes : Fin 3→ℕ:=![1,2+(Fintype.card (RecoveryCalls.Control CloseoutRowsRawProductRow.sizes)+2)+3,2]
noncomputable def programs : (i : Fin 3)→Machine 5 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>CloseoutRowsRawProductBody.machine
  | ⟨2,_⟩=>finish
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (i : Fin 3) (_ : Fin (sizes i)) (bits : Fin 5→Bool) : Option (Fin 3):=
  if i=0 then some (if bits 0 then 1 else 2) else if i=1 then some 0 else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductLoop
