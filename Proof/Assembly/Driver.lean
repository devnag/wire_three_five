import Proof.Assembly.FamilyInit
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryExecution RepairSource.VerifierDecoding
namespace PCJ34388a2fbfa9464b_
namespace Driver


variable {t : Nat}

def machine (src : Fin t) (p q z : Fin t → Option Bool) : Machine t 5 where
 descriptionBits:=0
 start:=0
 halted:=fun s=>s.val==4
 rule:=fun s bits=>
  if s.val=0 then
   if bits src then some ⟨1,p,fun i=>if i=src then .stay else match p i with | none=>.stay | some _=>.right⟩
   else some ⟨2,z,fun i=>if i=src then .left else .stay⟩
  else if s.val=1 then
   some ⟨0,q,fun i=>if i=src then .right else match q i with | none=>.stay | some _=>.right⟩
  else if s.val=2 then
   if bits src then some ⟨3,fun _=>none,fun i=>if i=src then .stay else match p i with | none=>.stay | some _=>.left⟩
   else some ⟨4,fun _=>none,fun i=>if i=src then .right else .stay⟩
  else if s.val=3 then
   some ⟨2,fun _=>none,fun i=>if i=src then .left else match q i with | none=>.stay | some _=>.left⟩
  else none


end Driver
end PCJ34388a2fbfa9464b_
