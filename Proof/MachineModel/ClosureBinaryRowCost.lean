import Proof.MachineModel.ClosureBinaryReusableRow
import Proof.MachineModel.SourceEnvelope

/-! Actual binary-row driver accounting: header support stays linear and
additive, cut scanning retains load slack, and the signed table appears once.
The source radix and original degree, not the replicated pool, price p. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryRowCost
open RepairRepresentation RepairOrdinary ExtIncidence
open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput CloseoutRowsEstimator

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

end NearCubicWires.P1Closure.BinaryRowCost
