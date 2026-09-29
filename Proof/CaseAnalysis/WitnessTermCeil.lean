import Proof.CaseAnalysis.PolicyArithmetic

/-! Exact ceiling of the fixed rational XOR term multiplier, from the
actual raw q0 alone. The fixed offset and positive divisor are printed by
finite control; every product, sum, copy and quotient is paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCeil
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization
open CloseoutWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def templateSlots : Fin 3→Fin 16:=![0,1,2]
def powerSlots : Fin 5→Fin 16:=![1,4,5,6,7]
def offsetSlots : Fin 2→Fin 16:=![8,9]
def sumSlots : Fin 4→Fin 16:=![6,8,10,11]
def divisorSlots : Fin 2→Fin 16:=![12,13]
def divideSlots : Fin 4→Fin 16:=![10,12,14,15]
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def power (A : ℕ):=RecoveryFocus.machine powerSlots (DimensionPower.machine 1 A)
def offset (B : ℕ):=RecoveryFocus.machine offsetSlots
  (HierarchyFixedWord.machine (List.replicate (B-1) true))
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def divisor (B : ℕ):=RecoveryFocus.machine divisorSlots (HierarchyFixedWord.machine (UnaryTemplate.tape B))
def divide:=RecoveryFocus.machine divideSlots MatrixBucketDivide.machine
def first (A : ℕ):=Composition.machine template (power A)
def second (A B : ℕ):=Composition.machine (first A) (offset B)
def third (A B : ℕ):=Composition.machine (second A B) sum
def fourth (A B : ℕ):=Composition.machine (third A B) (divisor B)
def machine (A B : ℕ):=Composition.machine (fourth A B) divide
def numerator (A B n : ℕ):=A*n+(B-1)
def budget (A B n : ℕ):=(2*n+8)+1+DimensionPower.cost A n 1+1+(2*(B-1)+2)+1+
  (2*numerator A B n+6)+1+(2*(UnaryTemplate.tape B).length+2)+1+(8*numerator A B n+6)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCeil
