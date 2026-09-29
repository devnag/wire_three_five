import Proof.Amplification.RecoveryCompactOutput

/-! Actual count positioning,34 broadcasts and final native-head setup
from the literal cold-marker endpoint, with every call return charged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def entryProgram := Composition.machine countBoot bankProgram
noncomputable def materializeProgram := Composition.machine entryProgram finish
def materializeBudget (bits word : List Bool) (n m : Nat) := bankBudget bits word n m+4

end NearCubicWires.RepairOrdinary.RecoveryColdCompact
