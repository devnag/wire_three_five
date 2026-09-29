import Proof.MachineModel.ClosureBinaryPreparedWriterLayout

/-! One fixed program constructs the actual raw family into the initially
empty native port, pays to rewind it, computes native metadata, then writes
the literal binary request header. All private preparation state survives
outside the native bank and every tape/head is specified at the endpoint.
The encoded hardwired cache and runtime dimensions remain real inputs. -/
namespace NearCubicWires.P1Closure.BinaryPreparedWriter
open LocalBitMultitape RepairOrdinary ExtIncidence ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

end
end NearCubicWires.P1Closure.BinaryPreparedWriter
