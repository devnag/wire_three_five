import Proof.CaseAnalysis.RowsEstimatorCoefficientsRequest
import Proof.CaseAnalysis.RowsScalarFits

/-! The selected coefficient tuple is read in its original compact grammar.
This bank deliberately keeps the existing framed-reader and clear ports;
all factors are actual source fields and all work backing is physical. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Product
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision CompetitorReusableDecision CompetitorMonomialStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def record (c : ℕ) (q : ℚ) :=
  frame [decide (q.num<0)]++frame (binary c q.num.natAbs)++frame (binary c q.den)


end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Product
