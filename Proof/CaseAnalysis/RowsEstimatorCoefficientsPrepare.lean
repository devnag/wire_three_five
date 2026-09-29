import Proof.CaseAnalysis.RowsEstimatorCoefficientsProducts
import Proof.Hierarchy.CompetitorMonomialPrepare

/-! The existing six-field stream reader, scratch clear, and runtime-width
preparation applied to an unreduced signed coefficient. Physical inputs and
logical cursors are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorMonomialStream
open Products
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def recordFields (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) : Fin 6 → List Bool :=
  ![binary (width b) (q.positive),binary (width b) (q.negative),binary (width b) q.denominator,
    binary (width b) 0,binary b denominator,binary b count]
def recordWord (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) := fieldStream (recordFields b q count denominator) allFields


end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream
