import Proof.CaseAnalysis.WitnessCountBound
import Proof.CaseAnalysis.WitnessSumFields

/-! The whole sum header guard compares its canonical arity with the same
produced source arity, and its actual term count with the paid exact cap.
Every raw sum has a complete run; term parsing starts only after this flag. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumGuard
open LocalBitMultitape RecoveryRootRound RadixSemantics
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 501) : Fin 510:=i.castAdd 9
def equalSlots : Fin 4→Fin 510:=![323,501,499,503]
def boundSlots : Fin 8→Fin 510:=![368,502,504,505,506,507,508,509]
def headerSlots : Fin 2→Fin 510:=![148,499]
def natSlots : Fin 2→Fin 510:=![324,499]
def countSlots : Fin 2→Fin 510:=![508,499]
def fields:=RecoveryFocus.machine old SumFields.machine
def equality:=RecoveryFocus.machine equalSlots NumericEquality.readyMachine
def bound:=RecoveryFocus.machine boundSlots CountBound.machine
def header:=RecoveryFocus.machine headerSlots NodeRound.flagMachine
def natural:=RecoveryFocus.machine natSlots NodeRound.flagMachine
def count:=RecoveryFocus.machine countSlots NodeRound.flagMachine
def first:=Composition.machine fields equality
def second:=Composition.machine first bound
def third:=Composition.machine second header
def fourth:=Composition.machine third natural
def machine:=Composition.machine fourth count
def Passes (bits arityBits : List Bool) (cap : ℕ):=PairHeader.valid bits ∧
  CanonicalBinary.decodeNat (value (SumFields.arityCode bits))=some (value arityBits) ∧
  (∃ codes,CanonicalBinary.encodeBalancedList codes=value (SumFields.listCode bits)) ∧
  SumFields.count bits ≤ cap


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumGuard
