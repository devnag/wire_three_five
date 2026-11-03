import Proof.Rows.PhysicalFocusBoundary
import Proof.Amplification.RecoveryScratchErase

/-! Paid allocation or erasure of one ambient word from an actual retained
raw reserve and erase log, preserving all other tapes and cursors. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalEraseInto
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def slots {t : Nat} (target raw log : Fin t) : Fin 3→Fin t := ![target,raw,log]
noncomputable def machine {t : Nat} (target raw log : Fin t) :=
  RecoveryFocus.machine (slots target raw log) (RecoveryScratchErase.resetMachine 1)

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalEraseInto
