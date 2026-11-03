import Proof.Supplier.EquationCount
import Proof.Supplier.EquationHeaders

/-! The original framed row now supplies the exact output headers as well
as every retained loop/count/capacity input. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaderCold
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 52 → Fin 111 := ![42,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,44,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,50,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110]
theorem slots_injective : Function.Injective slots := by decide
def bank (j : Fin 32) : Fin 111 := (EquationCountCold.slots j).castAdd 49
theorem bank_other (j : Fin 32) (h12 : j≠12) (h14 : j≠14) (h20 : j≠20) :
    RecoveryFocus.pick slots (bank j)=none := by
  fin_cases j
  all_goals first | contradiction | decide
noncomputable def first := TapeEmbedding.machine 49 EquationCountCold.machine
noncomputable def last := RecoveryFocus.machine slots EquationHeaders.machine
noncomputable def machine := Composition.machine first last
def values (d p g : ℕ) : Fin 3 → ℕ := ![d,p+1,2*g]
def input (d p g : ℕ) (odd : Bool) (suffix : List Bool) : Fin 111 → List Bool :=
  fun i => if i=0 then frame (EquationHeaderRead.word d p g (odd::suffix)) else []
def budget (d p g : ℕ) (odd : Bool) (suffix : List Bool) :=
  EquationCountCold.budget d p g odd suffix+1+EquationHeaders.budget (values d p g)

end NearCubicWires.RepairOrdinary.EquationHeaderCold
