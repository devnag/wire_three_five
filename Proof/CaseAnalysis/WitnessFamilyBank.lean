import Proof.CaseAnalysis.WitnessSelectedErase
import Proof.CaseAnalysis.CloseoutWitnessFamilyRun

/-! The two existing erase drivers allocate the whole family's private
workspace once. The retained source policy, mass accumulator and logical
streams are outside both sweeps. Their capacities remain independent. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyBank
open LocalBitMultitape
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def parser (i : Fin 3241) : Bool:=decide
  ((i.val<724 ∧ i.val≠720 ∧ i.val≠721 ∧ i.val≠722) ∨ (819 ≤ i.val ∧ i.val<826))
def family (i : Fin 3241) : Bool:=decide (i.val=722 ∨
  (827 ≤ i.val ∧ i.val≠2501 ∧ i.val≠2515 ∧ i.val≠2525 ∧ i.val≠2526 ∧
    i.val≠2530 ∧ i.val≠2531 ∧ i.val≠3034 ∧ i.val≠3035 ∧ i.val≠3059 ∧ i.val≠3238))
def first:=SelectedErase.machine parser 720 721
def second:=SelectedErase.machine family 2530 2531
def machine:=Composition.machine first second

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyBank
