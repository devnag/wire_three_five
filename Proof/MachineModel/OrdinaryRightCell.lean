import Proof.MachineModel.OrdinaryBoundaryAdvance

/-! Generate the next bucket boundary and consume it in the actual cell
comparison. The matrix output is appended; its cursor is never rewound. -/
namespace NearCubicWires.RepairOrdinary.RightCell
open LocalBitMultitape SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 6 ≃ Fin 6 where
  toFun := ![2, 4, 5, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 1, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 6 → Fin 6) = ![3, 4, 0, 5, 1, 2] := rfl


end NearCubicWires.RepairOrdinary.RightCell
