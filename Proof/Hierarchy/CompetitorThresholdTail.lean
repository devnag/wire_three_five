import Proof.Hierarchy.CompetitorThresholdPrepared

/-! Complete actual threshold tail: print the fixed rational, physically
clear the scalar workspace, then compare the retained exact sum. Both
validity upper tests and the acceptance midpoint lower test use this tail. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def decisionTail (lower : Bool) := Composition.machine clearProgram (decisionProgram lower)
noncomputable def machine (lower : Bool) (k : ℕ) (q : ℚ) :=
  Composition.machine (constantsProgram k q) (decisionTail lower)
def budget (b k : ℕ) := CompetitorThresholdConstants.budget b k+2*capacity b+2000*(b+1)^2+6

end NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
