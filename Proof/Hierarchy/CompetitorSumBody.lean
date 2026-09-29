import Proof.Hierarchy.CompetitorSumResult

/-! Enclosing paid update for the exact signed-rational term stream:
clear/load the next term, execute the addition and denominator product, then
clear/copy back the accumulator. The global source cursor advances once. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bodyTail := Composition.machine nativeProgram restoreProgram
noncomputable def bodyProgram := Composition.machine prepareProgram bodyTail
def bodyBudget (b : ℕ) := 20000*(b+1)^2

end NearCubicWires.RepairOrdinary.CompetitorSumFold
