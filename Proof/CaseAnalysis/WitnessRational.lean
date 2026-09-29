import Proof.CaseAnalysis.WitnessPairHeader
import Proof.CaseAnalysis.RowsIntegerGuard

/-! The same raw rational code reaches its exact tagged pair, canonical
signed numerator, and canonical denominator. The magnitude payloads remain
binary; the next consumer guards their widths before running gcd. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalCold
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots (i : Fin 149) : Fin 539:=i.castAdd 390
def integerSlots (i : Fin 212) : Fin 539:=if i.val=0 then 38 else ⟨149+i.val,by omega⟩
def naturalSlots (i : Fin 178) : Fin 539:=if i.val=0 then 78 else ⟨361+i.val,by omega⟩



def boot : Machine 539 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=0 then some false else none,fun _=>.stay⟩ else none
noncomputable def header:=RecoveryFocus.machine headerSlots PairHeader.machine
noncomputable def integer:=RecoveryFocus.machine integerSlots CloseoutRowsIntegerGuard.machine
noncomputable def natural:=RecoveryFocus.machine naturalSlots NatCold.machine
noncomputable def first:=Composition.machine boot header
noncomputable def second:=Composition.machine first integer
noncomputable def machine:=Composition.machine second natural


end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalCold
