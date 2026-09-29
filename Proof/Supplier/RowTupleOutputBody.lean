import Proof.Supplier.RowTupleOutputParts

/-! One physical binary candidate: reset/filter, conditionally append its
position word, then increment and test the retained bounded binary cursor. -/
namespace NearCubicWires.RepairOrdinary.RowTupleOutputBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowTupleFilterParts
open RowTupleOutputParts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def states {t s : ℕ} (_ : Machine t s) := s
noncomputable def sizes : Fin 3→ℕ := ![states candidate,5,14]
noncomputable def programs : (i : Fin 3)→Machine 18 (sizes i)
  | ⟨0,_⟩=>candidate
  | ⟨1,_⟩=>append
  | ⟨2,_⟩=>advance
  | ⟨n+3,h⟩=>False.elim (by omega)
noncomputable def next (i : Fin 3) (_ : Fin (sizes i)) (bits : Fin 18→Bool) : Option (Fin 3) :=
  ![some (if bits 9 then 1 else 2),some 2,none] i
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.RowTupleOutputBody
