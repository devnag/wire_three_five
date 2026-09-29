import Proof.Hierarchy.CompetitorMonomialTargetWidth

/-! The original monomial product and width programs accept signed natural
fractions directly. These are the same input fields and the same controllers;
no reduction to canonical rational numerator/denominator bytes is required. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Products

def contribution (q : CompetitorValidity.Estimate) (count denominator : ℕ) : CompetitorValidity.Estimate :=
  ⟨q.positive*count,q.negative*count,q.denominator*denominator⟩

end Products

namespace Target
open Products CompetitorMonomialTarget CompetitorReusableDecision

end Target
end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
