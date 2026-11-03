import Proof.Packets.PacketsXModeCacheReady
import Proof.Packets.WindowProviderPorts

/-! The actual original-seed delta cache in the fixed provider arena.
Both source halves are emitted into125; the actually counted child cell is
retained at150. All remaining provider state lies outside the fixed ports. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
attribute [local irreducible] ModeCacheReady.machine

def modePorts : Fin 29→Fin 256 :=
  ![153,162,154,155,163,156,164,165,166,157,167,158,159,168,169,
    170,171,172,173,174,125,160,175,150,161,30,32,33,31]
noncomputable def buildModeCache := RecoveryFocus.machine modePorts ModeCacheReady.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
