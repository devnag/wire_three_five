import Proof.MachineModel.ClosureScannedRowState

/-! The actual count-table row now returns the complete reusable input
bank. The next call may start on this same physical backing; no assumed
answer, shortened tape, or fresh reset log is introduced. Next-label syntax
production is still an upstream computation. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ActualReusableRow
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler
open SourceInterfaces RepairSource RepairSource.CloseoutFinal RecoveryRootRound
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount CompetitorCountMask C10SupplierRowInput
open CompetitorCrossScheduler (producer)

end NearCubicWires.P1Closure.ActualReusableRow
