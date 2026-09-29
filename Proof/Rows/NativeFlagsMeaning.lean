import Proof.Rows.ExpandedThresholdStream
import Proof.Rows.NativeFlagsLoop

/-! The actual original-native traversal emits exactly the flags consumed by
the expanded canonical equation, including child targets and final offset. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
namespace PCJ45bee56da9f34d5a_NativeFlagsMeaning
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open PCJ9eff70d512234a4c_Fixed
open PCJ45bee56da9f34d5a_NativeCircuitCodec
open PCJ45bee56da9f34d5a_ExpandedThresholdStream
noncomputable section

def circuits (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :=
 r.circuits.map (fun c=>(thrGates c,thrTop c))

end
end PCJ45bee56da9f34d5a_NativeFlagsMeaning
