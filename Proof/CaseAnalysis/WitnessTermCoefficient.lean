import Proof.CaseAnalysis.WitnessRationalDecision

/-! Each term's coefficient is validated once, with both original length
guards before gcd. Its same circuit payload and checked binary coefficient
remain available to the circuit worker and the mass accumulator. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCoefficient
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def printSlots : Fin 2→Fin 720:=![0,718]
def headerSlots (i : Fin 149) : Fin 720:=i.castAdd 571
def rationalSlots (i : Fin 568) : Fin 720:=
  ⟨if i.val=1 then 38 else if i.val=539 then 149 else 150+i.val,by split_ifs <;> omega⟩
def finishSlots : Fin 3→Fin 720:=![148,714,719]
def finishMachine : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun _ bits=>some ⟨1,![none,none,some (bits 0 && bits 1)],fun _=>.stay⟩
def print:=RecoveryFocus.machine printSlots (HierarchyFixedWord.machine [false])
def header:=RecoveryFocus.machine headerSlots PairHeader.machine
def coefficient:=RecoveryFocus.machine rationalSlots RationalDecision.machine
def finish:=RecoveryFocus.machine finishSlots finishMachine
def first:=Composition.machine print header
def second:=Composition.machine first coefficient
def machine:=Composition.machine second finish
def coefficientCode (bits : List Bool):=PairHeader.codeWord bits 0
def circuitCode (bits : List Bool):=PairHeader.codeWord bits 1


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCoefficient
