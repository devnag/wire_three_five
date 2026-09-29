import Proof.PCP.PCPPNativeNodeArguments

/-! The whole NOT-node path consumes the reader-produced argument,
computes its shifted address, emits both native nodes, and halts. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem argument_input (right : Bool) (n : ℕ) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool)
    (hh : heads (argSlots right 0)=1) (ht : data (argSlots right 0)=UnaryTemplate.tape n)
    (work : ∀ i : Fin 5,i≠0 → heads (argSlots right i)=0 ∧ data (argSlots right i)=[]) :
    (∀ i,heads (argSlots right i)=PCPPNativeTemplateRaw.heads i) ∧
      (∀ i,data (argSlots right i)=MatrixTemplateCopy.resetInput n i) := by
  constructor
  · intro i
    by_cases hi : i=0
    · subst i; exact hh
    · simpa only [PCPPNativeTemplateRaw.heads,hi,ite_false] using (work i hi).1
  · intro i
    fin_cases i
    · exact ht
    all_goals exact (work _ (by decide)).2

def notBudget (index base C : ℕ) :=
  PCPPNativeNodeClassify.budget 2 index 0+(4*index+16)+PCPPNativeNotNode.budget base index C+3

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
