import Proof.Packets.WindowProviderPorts
import Proof.Packets.ReusableNativeNormalize

/-! The concrete native-normalizer dock in the256-tape provider. It consumes
its physically produced source on122, returns the normalized operand on26/27,
and restores all native private backing without changing other provider data. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def normalize := RecoveryFocus.machine nativePorts ReusableNative.normalize

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
