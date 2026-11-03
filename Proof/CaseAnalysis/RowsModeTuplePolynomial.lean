import Proof.CaseAnalysis.RowsModeTupleMonomial

/-! The actual selected-tuple frames drive the whole raw polynomial writer.
No count prepass or exponential unary driver is supplied to this loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeTuplePolynomial
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsModeTupleMonomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 7 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
noncomputable def body : Σ s,Machine 7 s:=⟨_,CloseoutRowsModeTupleMonomial.machine⟩
noncomputable def sizes : Fin 2→Nat:=![1,body.1]
noncomputable def programs : (i : Fin 2)→Machine 7 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>body.2
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (i : Fin 2) (_ : Fin (sizes i)) (bits : Fin 7→Bool) : Option (Fin 2):=
  if i=0 then if bits 0 then some 1 else none else some 0
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.CloseoutRowsModeTuplePolynomial
