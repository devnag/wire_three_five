import Proof.CaseAnalysis.WitnessTermCeil
import Proof.CaseAnalysis.CapacityPower

/-! The actual source clause exponent is expanded once and multiplied
by twice the exact XOR term ceiling. Here cb is source metadata; the
enclosing source bound pays 2^cb as a polynomial in the native width. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermMultiply
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def clauseSlots (i : Fin 17) : Fin 27:=i.castAdd 10
def templateSlots : Fin 3→Fin 27:=![17,18,19]
def doubleSlots : Fin 5→Fin 27:=![18,21,22,23,24]
def productSlots : Fin 4→Fin 27:=![23,13,25,26]
def clauses:=RecoveryFocus.machine clauseSlots CloseoutCapacity.Power.machine
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def double:=RecoveryFocus.machine doubleSlots (DimensionPower.machine 1 2)
def product:=RecoveryFocus.machine productSlots ClockUnaryProduct.machine
def first:=Composition.machine clauses template
def second:=Composition.machine first double
def machine:=Composition.machine second product
def budget (cb J : ℕ):=CloseoutCapacity.Power.budget cb+1+(2*J+8)+1+
  DimensionPower.cost 2 J 1+1+WilliamsUnaryProduct.budget (2*J) (2^cb)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermMultiply
