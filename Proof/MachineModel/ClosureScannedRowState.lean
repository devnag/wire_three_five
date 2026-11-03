import Proof.MachineModel.ClosureRawRowState

/-! Full-state reuse of the existing warm scanner/printer.  These identities
test the actual exit, not just its answer port.  The next row's header and
metadata still require their physical producer. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ScannedRowState
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open CloseoutRowsEstimator C10RowFrameJoin CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount MatrixScoreBatch P1Independent RecoveryRootRound
attribute [local irreducible] Warm.input RecoveryRootRound.install

end NearCubicWires.P1Closure.ScannedRowState
