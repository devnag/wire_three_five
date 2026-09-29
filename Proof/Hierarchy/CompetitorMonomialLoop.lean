import Proof.Hierarchy.CompetitorMonomialBody

/-! The actual repeated coefficient/count stream producer. Its sole global
append tape is never rewound inside the loop, and the physical unary driver
is returned after exactly the requested number of records. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (_ : Fin 88 → Bool) := true
noncomputable def loopProgram := RepeatMachine.machine bodyProgram accepted
def loopBudget (t n : ℕ) := n*(bodyBudget t+3)+3


end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
