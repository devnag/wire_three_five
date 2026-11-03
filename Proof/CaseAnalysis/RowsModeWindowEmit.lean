import Proof.CaseAnalysis.RowsModeWindowConstant

/-! A fixed three-call controller emits one guarded elementary summand.
Its zero-population branch physically writes the constant monomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowEmit
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsModeWindowLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body : Σ s,Machine 60 s:=⟨_,elementary⟩
noncomputable def sizes : Fin 3→Nat:=![5,body.1,3]
noncomputable def programs : (i : Fin 3)→Machine 60 (sizes i)
  | ⟨0,_⟩=>CloseoutRowsModeWindowSelect.machine
  | ⟨1,_⟩=>body.2
  | ⟨2,_⟩=>CloseoutRowsModeWindowConstant.machine
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (i : Fin 3) (q : Fin (sizes i)) (_ : Fin 60→Bool) : Option (Fin 3):=
  if i=0 then if q.val=3 then some 1 else if q.val=4 then some 2 else none else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowEmit
