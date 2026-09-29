import Proof.CaseAnalysis.RowsEstimatorScanned

/-! Scalar formula for the paid reset driver. Its only varying arguments
are the actual scanner counts d,p,G and retained native C. Table size enters
once, and the native capacity enters linearly. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Driver
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tableCoefficient (a : WilliamsAlgorithm) :=
  4*2^(CompetitorCrossScheduler.exponent a)*(CompetitorCountTableRecord.coefficient a+1)
noncomputable def tableValue (a : WilliamsAlgorithm) (d p : ℕ) :=
  tableCoefficient a*(2^d)^2*(d+p+1)^(CompetitorCrossScheduler.exponent a)
noncomputable def value (a : WilliamsAlgorithm) (d p G C : ℕ) :=
  64*(C+1)+2000000*(d+p+G+1)^3+tableValue a d p

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Driver
