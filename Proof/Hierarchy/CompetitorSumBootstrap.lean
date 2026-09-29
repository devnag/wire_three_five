import Proof.Hierarchy.CompetitorSumClear

/-! Cold initial accumulator producer. Physical clearing provides every
retained zero cell consumed by the subsequent constant writers and fold. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def constantsProgram := RecoveryFocus.machine nativeSlots CompetitorSumConstants.machine
noncomputable def bootstrapProgram := Composition.machine coldClearProgram constantsProgram
def bootstrapBudget (b : ℕ) := 2*capacity b+20*b+58

end NearCubicWires.RepairOrdinary.CompetitorSumFold
