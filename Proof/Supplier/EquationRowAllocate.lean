import Proof.Supplier.EquationHeader

/-! One actual capacity sweep prepares all fourteen C-zero scratch tapes
and the C+1 erase log. Existing source/output/count cursors are preserved. -/
namespace NearCubicWires.RepairOrdinary.EquationRowAllocate
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 16) : Fin 126 :=
  if h : j.val<14 then ⟨111+j.val,by omega⟩ else if j.val=14 then 60 else 125
noncomputable def machine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 14)

end NearCubicWires.RepairOrdinary.EquationRowAllocate
