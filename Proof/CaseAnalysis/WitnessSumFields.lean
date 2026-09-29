import Proof.CaseAnalysis.RowsCanonicalFlag
import Proof.CaseAnalysis.WitnessPairHeader

/-! The same sum's tagged pair, canonical arity and balanced term list are
read once. The field stream and actual count survive for the term loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumFields
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def headerSlots (i : Fin 149) : Fin 501:=i.castAdd 352
def aritySlots (i : Fin 178) : Fin 501:=
  ⟨if i.val=0 then 38 else 149+i.val,by split_ifs <;> omega⟩
def listSlots (i : Fin 174) : Fin 501:=
  ⟨if i.val=0 then 78 else 327+i.val,by split_ifs <;> omega⟩
def header:=RecoveryFocus.machine headerSlots PairHeader.machine
def arity:=RecoveryFocus.machine aritySlots NatCold.machine
def terms:=RecoveryFocus.machine listSlots CanonicalTest.machine
def prime : Machine 501 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=0 then some false else none,fun _=>.stay⟩ else none
def first:=Composition.machine prime header
def prefixMachine:=Composition.machine first arity
def machine:=Composition.machine prefixMachine terms
def arityCode (bits : List Bool):=PairHeader.codeWord bits 0
def listCode (bits : List Bool):=PairHeader.codeWord bits 1
def atoms (bits : List Bool):=(tree (value (listCode bits))).atoms
def count (bits : List Bool):=(atoms bits).length


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumFields
