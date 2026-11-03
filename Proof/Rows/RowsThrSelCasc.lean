import Proof.Rows.RowsThrSelPure

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrSelCasc
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeyTop RowsConstruction.ThrKey
open RowsConstruction.ThrSel
noncomputable section

section Ports
variable (NI : Nat)

/-- The four child-digit masters. -/
def dPort : Fin 4 → Fin 254 := ![228, 229, 230, 231]

theorem dPort_val (c : Fin 4) : (dPort c).val = 228 + c.val := by
  fin_cases c <;> rfl

theorem masterPort_inj (i k : Fin 254) : masterPort NI i = masterPort NI k ↔ i = k := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [masterPort_val, masterPort_val] at hv
    exact Fin.ext (by omega)
  · intro h; rw [h]


end Ports

end
end RowsConstruction.ThrSelCasc
