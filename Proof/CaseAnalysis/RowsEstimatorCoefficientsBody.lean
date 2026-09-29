import Proof.CaseAnalysis.RowsEstimatorCoefficientsPrepare
import Proof.Hierarchy.CompetitorMonomialBody

/-! The original reusable six-field body on unreduced signed fractions.
Its source cursor, append cursor, work support, machine and time bound are
exactly the original ones. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorMonomialStream Products
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Entry where
  coefficient : CompetitorValidity.Estimate
  count : ℕ
  denominator : ℕ

def Entry.estimate (a : Entry) := contribution a.coefficient a.count a.denominator

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream
