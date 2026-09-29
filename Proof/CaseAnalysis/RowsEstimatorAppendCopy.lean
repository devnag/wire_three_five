import Proof.CaseAnalysis.RowsEstimatorAppendRaw

/-! The paid six-field append restores its local record cursor while leaving
the growing global stream at its append cursor. The existing finite reset
backing is retained and can be used again. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendCopy
open LocalBitMultitape RepairSource.ProjectionNormalization
open CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine := CursorRestore.machine AppendRaw.machine 0

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendCopy
