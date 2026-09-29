import Proof.MachineModel.ClosureBinaryRequest
import Proof.MachineModel.ClosureCompactFamily

/-! The physical compact writer at the binary-order pool. Length-proof casts
change only the types of the old indices: raw source bytes and mask-bank
bytes are unchanged. The fixed cold writer computes its metadata and emits
the literal binary request header, with complete final heads and tapes.
Physical cache/dimension/raw-source construction remains an upstream duty.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryWriter
open LocalBitMultitape RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput
open ExtIncidence ExtDecompositionBatch RepairSource.VerifierDecoding

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

end NearCubicWires.P1Closure.BinaryWriter
