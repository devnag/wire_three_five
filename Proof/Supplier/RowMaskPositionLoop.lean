import Proof.Supplier.RowMaskPositionParts

/-! A selected binary address controls the actual cache scan. Each accepted
counter step consumes one N-bit row; the output and occurrence count persist. -/
namespace NearCubicWires.RepairOrdinary.RowMaskPositionLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 2→ℕ := ![14,5]
noncomputable def programs : (i : Fin 2)→Machine 9 (sizes i)
  | ⟨0,_⟩=>counterMachine
  | ⟨1,_⟩=>skipMachine
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (i : Fin 2) (_ : Fin (sizes i)) (bits : Fin 9→Bool) : Option (Fin 2) :=
  ![if bits 7 then some 1 else none,some 0] i
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.RowMaskPositionLoop
