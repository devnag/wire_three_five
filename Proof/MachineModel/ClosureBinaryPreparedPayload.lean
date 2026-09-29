import Proof.MachineModel.ClosureBinaryPreparedWriter
import Proof.MachineModel.ClosureBinaryReusableRow

/-! Actual cold native writer → paid header rewind/copy → actual C.10
selected count and binary payload, on one bank. The consumer header starts
blank. Source cache, lowered stream, metadata/mask and allocation inputs
remain explicit; no header or table answer is supplied to the entry. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryPreparedPayload
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary RecoveryRootRound
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler
open SourceInterfaces RepairSource CloseoutFinal RecoveryRootRound
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount CompetitorCountMask C10SupplierRowInput C10RowFrameJoin
open CompetitorCrossScheduler (producer)
attribute [local irreducible] pool BinaryPool.pool bank CloseoutRowsCacheInput.family CompactBounds.radix
  CompetitorCrossScheduler.producer Warm.input BinaryPreparedWriter.machine ScannedRawRow.machine



end NearCubicWires.P1Closure.BinaryPreparedPayload
