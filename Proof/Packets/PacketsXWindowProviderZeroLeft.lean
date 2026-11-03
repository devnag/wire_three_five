import Proof.Packets.CycleCommonReserve
import Proof.Packets.PacketsXWindowCoordinateSubstitute
import Proof.Packets.SubstitutionOuterStep
import Proof.Packets.SubstitutionReusable
import Proof.Supplier.SupplierCapacity
import Proof.Supplier.SupplierEstimator
import Proof.Packets.PacketsXWindowProviderZeroRight

/-! Actual left-operand clearing at the coordinate-phase boundary. This
permits the last vector-loop operand to be an arbitrary fitting packet. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def zeroLeft := Composition.machine (PhysicalCopyInto.machine (31 : Fin 256) 0 25)
  (PhysicalCopyInto.machine (31 : Fin 256) 0 28)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
