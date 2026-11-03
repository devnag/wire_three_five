import Proof.CaseAnalysis.RowsRawMonomialSkip

/-! One original left monomial emits its complete product row, returns
the right stream by the existing paid rewind, and advances the left stream.
Both rewind logs are retained for the next actual left monomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductBody
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advance : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,![.right,.stay,.stay,.stay,.stay]⟩ else none
noncomputable def row:=MaskedReset.machine CloseoutRowsRawProductRow.machine (fun i=>decide (i=1))
def skipSlots : Fin 1→Fin 5:=fun _=>0
noncomputable def skip:=RecoveryFocus.machine skipSlots CloseoutRowsRawMonomialSkip.machine
noncomputable def machine:=Composition.machine (Composition.machine advance row) skip

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductBody
