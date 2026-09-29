import Proof.MachineModel.ClosureScannedRowState
import Proof.MachineModel.ClosureBinaryRequest

/-! The physical binary-order row is consumed by the scanner/printer and
selected-count payload transaction. The complete bank returns in its reusable
state, and the value is the original C.10 table count. The produced header,
selection mask and paid workspace remain the explicit input boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.BinaryReusableRow
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler
open SourceInterfaces RepairSource RepairSource.CloseoutFinal RecoveryRootRound
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount CompetitorCountMask C10SupplierRowInput
open CompetitorCrossScheduler (producer)

attribute [local irreducible] pool BinaryPool.pool bank CloseoutRowsCacheInput.family CompactBounds.radix

end NearCubicWires.P1Closure.BinaryReusableRow
