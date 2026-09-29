import Proof.Supplier.RowMaskBodyParts

/-! The mask bit itself controls whether its index is emitted. The common
tail advances the index and source and counts only selected occurrences. -/
namespace NearCubicWires.RepairOrdinary.RowMaskBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskBodyParts Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 4 1 where
  descriptionBits := 0
  start := 0
  halted := fun _=>true
  rule := fun _ _=>none
def sizes : Fin 3→ℕ := ![1,5,11]
noncomputable def programs : (i : Fin 3)→Machine 4 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>appendMachine
  | ⟨2,_⟩=>tailMachine
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (i : Fin 3) (_ : Fin (sizes i)) (bits : Fin 4→Bool) : Option (Fin 3) :=
  ![some (if bits 0 then 1 else 2),some 2,none] i
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.RowMaskBody
