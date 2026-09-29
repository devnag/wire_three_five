import Proof.MachineModel.ClosureScannedRow

/-! Consume the common-bank transaction at the paper's actual hardwired row.
A.12.1 fixes Q = K+1; A.13.9/A.13.10 select entries of this exact table.
The native header and mask are physical inputs, whose upstream production is
still required. The selected count is computed, never an input word.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ActualRow
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler
open SourceInterfaces RepairSource RepairSource.CloseoutFinal
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount CompetitorCountMask C10SupplierRowInput
open CompetitorCrossScheduler (producer)

end NearCubicWires.P1Closure.ActualRow
