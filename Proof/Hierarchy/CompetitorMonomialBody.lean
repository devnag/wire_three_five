import Proof.Hierarchy.CompetitorMonomialNative

/-! Enclosing reusable coefficient/count record execution. Every iteration
physically clears local scratch, copies runtime widths, reads six fields,
multiplies and widens the exact signed contribution, and appends its term. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bodyProgram := Composition.machine prepareProgram nativeProgram
def bodyBudget (t : ℕ) := 12000*(t+1)^2


end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
