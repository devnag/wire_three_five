import Proof.MachineModel.ClosureBinaryPreparedWriter
import Proof.MachineModel.ClosureLocalSupport

/-! The header capacity follows from its executed producer, rather than
being an extra answer-size assumption. Its allocation remains paid input
until the enclosing cold initialization constructs the runtime driver. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryHeaderCapacity
open LocalBitMultitape RepairOrdinary ExtIncidence ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

end NearCubicWires.P1Closure.BinaryHeaderCapacity
