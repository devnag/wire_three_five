import Proof.CaseAnalysis.WitnessTermCeil

/-! The two fixed Horner stages used by the exact normalized-gate
description cap. A retained actual multiplier template is reused; the
constant is printed and every arithmetic pass is paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DescriptionHorner
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def productSlots : Fin 4→Fin 8:=![0,1,2,3]
def constantSlots : Fin 2→Fin 8:=![4,5]
def sumSlots : Fin 4→Fin 8:=![2,4,6,7]
def product:=RecoveryFocus.machine productSlots ClockUnaryProduct.machine
def constant (k : ℕ):=RecoveryFocus.machine constantSlots
  (HierarchyFixedWord.machine (List.replicate k true))
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def first (k : ℕ):=Composition.machine product (constant k)
def machine (k : ℕ):=Composition.machine (first k) sum
def budget (k x n : ℕ):=WilliamsUnaryProduct.budget x n+1+(2*k+2)+1+(2*(x*n+k)+6)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.DescriptionHorner
