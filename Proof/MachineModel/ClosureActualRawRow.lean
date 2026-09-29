import Proof.MachineModel.ClosureScannedRawRow

/-! The actual C10 table instantiates the raw-output transaction. All table
correctness and value bounds are discharged here, as they were for the framed
printer. Only request legality, physical input preparation and capacities remain.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ActualRawRow
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler
open SourceInterfaces RepairSource RepairSource.CloseoutFinal RecoveryRootRound
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount CompetitorCountMask C10SupplierRowInput
open CompetitorCrossScheduler (producer)

end NearCubicWires.P1Closure.ActualRawRow
