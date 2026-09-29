import Proof.Amplification.RecoveryRowStructureSmallCases

/-! The paired-row branch executes a second unpair on the retained right
component of the original code. Its two actual output words are the keys
for the two prior-row lookups. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairWord (d : Data) := RecoveryChildSelection.word false d.code

theorem front_field (d : Data) : (frontOutput d).state.fields 0=frame (pairWord d) := by
  unfold frontOutput
  split <;> exact code_child d 0

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
