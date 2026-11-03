import Proof.Packets.NativeTerminator
import Proof.Packets.PhysicalRewindInto

/-! Physically terminate the generated window stream and rewind it with the
actual reserve driver. Both operations are included in the provider budget. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def terminatorPorts : Fin 1→Fin 256 := fun _=>78
noncomputable def terminate := RecoveryFocus.machine terminatorPorts NativeTerminator.machine
noncomputable def closeSource := Composition.machine terminate (PhysicalRewindInto.machine (31 : Fin 256) 78)

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
