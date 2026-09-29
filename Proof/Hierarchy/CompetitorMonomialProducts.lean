import Proof.Hierarchy.CompetitorValidityMidpoint

/-! Actual signed monomial contribution at the scalar fold. The exact
natural count and its paper denominator are multiplied by the guessed
rational coefficient's two sign parts and denominator. Only bounded scalar
words enter; the parent matrix tables are neither copied nor simulated. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialProducts
open LocalBitMultitape SignedSortKey CompetitorRationalProducts CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def positive (q : ℚ) := q.num.toNat
def negative (q : ℚ) := (-q.num).toNat

end NearCubicWires.RepairOrdinary.CompetitorMonomialProducts
