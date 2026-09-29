import Proof.CaseAnalysis.WitnessRationalGcd
import Proof.CaseAnalysis.WitnessRationalNormalize

/-! One total rational decision. Canonicality, positivity and original
payload lengths are tested before the cold gcd branch. Every raw word halts
under the same exact source cap; accepted coefficient fields stay retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalDecision
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 552) : Fin 568:=i.castAdd 16
def gcdSlots (i : Fin 18) : Fin 568:=
  if i.val=0 then 540 else if i.val=1 then 543 else ⟨550+i.val,by omega⟩
noncomputable def normal:=RecoveryFocus.machine old RationalNormalize.machine
noncomputable def gcd:=RecoveryFocus.machine gcdSlots RationalGcd.machine
def stateCount {t s : ℕ} (_ : Machine t s):=s
noncomputable def sizes : Fin 2→ℕ:=![stateCount normal,stateCount gcd]
noncomputable def programs : (j : Fin 2)→Machine 568 (sizes j)
  | ⟨0,_⟩=>normal
  | ⟨1,_⟩=>gcd
  | ⟨j+2,h⟩=>False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (scan : Fin 568→Bool) : Option (Fin 2):=
  if j.val=0 ∧ scan 551=true then some 1 else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next


end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalDecision
