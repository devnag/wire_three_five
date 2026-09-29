import Proof.Hierarchy.CompetitorMonomialProducts

/-! Expose the two actual numerator tapes of the accepted rational decision
machine. Swapping the second sign pair makes these its exact rational-addition
numerators. This is an endpoint of the existing paid execution, not a new
unaccounted arithmetic routine. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRationalNumerators
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def add (a c : CompetitorValidity.Estimate) : CompetitorValidity.Estimate :=
  ⟨a.positive*c.denominator+c.positive*a.denominator,
   a.negative*c.denominator+c.negative*a.denominator,
   a.denominator*c.denominator⟩

end NearCubicWires.RepairOrdinary.CompetitorRationalNumerators
