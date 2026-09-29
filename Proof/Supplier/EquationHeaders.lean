import Proof.Supplier.EquationHeaderAppend

/-! Three canonical headers are produced from their actual raw counts and
appended in order. Fresh local banks avoid an unnecessary reuse/erase stage. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaders
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot (j : Fin 3) (i : Fin 18) : Fin 52 :=
  if i.val<17 then ⟨17*j.val+i.val,by omega⟩ else 51

noncomputable def program (j : Fin 3) := RecoveryFocus.machine (slot j) EquationHeaderAppend.machine
noncomputable def first := Composition.machine (program 0) (program 1)
noncomputable def machine := Composition.machine first (program 2)


def budget (values : Fin 3 → ℕ) :=
  EquationHeaderAppend.budget (values 0)+1+EquationHeaderAppend.budget (values 1)+1+
    EquationHeaderAppend.budget (values 2)

end NearCubicWires.RepairOrdinary.EquationHeaders
