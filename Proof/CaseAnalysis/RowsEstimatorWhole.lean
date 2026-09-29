import Proof.CaseAnalysis.RowsEstimatorWholePrefix
import Proof.CaseAnalysis.RowsEstimatorRecord

/-! One shared physical estimator from actual native cut bytes at their
append cursor. The original row/Williams full table runs before the selected
SUM. The live metadata producers remain explicit in the input bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Whole
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask
open CompetitorCrossScheduler (producer)
open CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def callee (a : WilliamsAlgorithm):=
  CloseoutRowsRawRecord.machine (producer a) (CompetitorCountTableRecord.machine a)
def recordSlot (p : Program):=WholePrefix.slots p (CloseoutRowsRawRecord.receive p (CompetitorCountTableRecord.slots p 117))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Whole
