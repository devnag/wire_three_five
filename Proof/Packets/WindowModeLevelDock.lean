import Proof.Packets.ModeLevelRaw
import Proof.Packets.WindowProviderPorts

/-! Physical level derivation in the fixed provider arena. The actual row
successor tag is retained; no standalone raw-level word is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def modeLevelPorts : Fin 5→Fin 256 := ![187,159,176,32,33]
noncomputable def makeModeLevel := RecoveryFocus.machine modeLevelPorts ModeLevelRaw.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
