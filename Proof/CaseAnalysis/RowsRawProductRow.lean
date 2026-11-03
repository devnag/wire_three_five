import Proof.CaseAnalysis.RowsRawProductPair

/-! A raw left monomial is multiplied by every original right monomial.
The actual right stream controls the loop; duplicates and empty polynomials
are retained with no separately supplied enumeration count. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductRow
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsRawProductFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 4 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes : Fin 2→ℕ:=![1,12]
noncomputable def programs : (i : Fin 2)→Machine 4 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>CloseoutRowsRawProductPair.machine
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (i : Fin 2) (_ : Fin (sizes i)) (bits : Fin 4→Bool) : Option (Fin 2):=
  if i=0 then if bits 1 then some 1 else none else some 0
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductRow
