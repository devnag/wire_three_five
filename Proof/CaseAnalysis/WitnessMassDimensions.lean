import Proof.CaseAnalysis.WitnessMassWidth

/-! Produce the exact reusable scalar bank dimensions from the paid common
width. One successor template serves both fixed polynomial evaluations. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassDimensions
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def templateSlots : Fin 3→Fin 15:=![0,1,2]
def wideSlots : Fin 5→Fin 15:=![1,4,5,6,7]
def capacitySlots : Fin 7→Fin 15:=![1,9,10,11,12,13,14]
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine true)
def wide:=RecoveryFocus.machine wideSlots (DimensionPower.machine 1 2)
def capacity:=RecoveryFocus.machine capacitySlots (DimensionPower.machine 2 4096)
def first:=Composition.machine template wide
def machine:=Composition.machine first capacity
def budget (B : ℕ):=(2*B+8)+1+DimensionPower.cost 2 (B+1) 1+1+
  DimensionPower.cost 4096 (B+1) 2

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassDimensions
