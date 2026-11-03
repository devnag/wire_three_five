import Proof.Packets.PhysicalBoundedLeftRewind
import Proof.Rows.PhysicalFocusBoundary

/-! Paid rewind by a retained capacity driver in an arbitrary ambient bank. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalRewindInto
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def slots {t : Nat} (width source : Fin t) : Fin 2→Fin t := ![width,source]
noncomputable def machine {t : Nat} (width source : Fin t) :=
  RecoveryFocus.machine (slots width source) Completion.PhysicalBoundedLeftRewind.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalRewindInto
