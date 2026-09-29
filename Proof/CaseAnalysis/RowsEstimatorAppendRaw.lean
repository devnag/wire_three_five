import Proof.CaseAnalysis.RowsEstimatorWhole

/-! Append the existing six-field scalar record using two existing fixed
three-field copies. The number of fields is in the finite control; there is
no supplied count stream or runtime record-length prepass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendRaw
open LocalBitMultitape RepairSource.ProjectionNormalization SignedSortKey
open CloseoutRowsEstimatorCoefficients CompetitorMonomialStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine := Composition.machine ClauseCopy.machine ClauseCopy.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendRaw
