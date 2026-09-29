import Proof.CaseAnalysis.WitnessMassTrace
import Proof.MachineModel.UWalkArithmetic

/-! One paid policy product supplies the common accumulator width for all
sums. Both exact policy inputs remain available; no per-sum multiplication. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassWidth
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def oneSlots : Fin 2→Fin 10:=![2,3]
def sumSlots : Fin 4→Fin 10:=![0,2,4,5]
def templateSlots : Fin 3→Fin 10:=![1,6,7]
def productSlots : Fin 4→Fin 10:=![4,6,8,9]
def one:=RecoveryFocus.machine oneSlots (HierarchyFixedWord.machine [true])
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine true)
def product:=RecoveryFocus.machine productSlots ClockUnaryProduct.machine
def first:=Composition.machine one sum
def second:=Composition.machine first template
def machine:=Composition.machine second product
def budget (T b : ℕ):=4+1+(2*(T+1)+6)+1+(2*b+8)+1+WilliamsUnaryProduct.budget (T+1) (b+1)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassWidth
