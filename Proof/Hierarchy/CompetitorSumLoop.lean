import Proof.Hierarchy.CompetitorSumBody

/-! Whole physical repetition of the exact signed-rational fold. The unary
term driver is exhausted and rewound; each iteration updates the same
accumulator and consumes exactly one three-field scalar record. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (_ : Fin 94 → Bool) := true
noncomputable def loopProgram := RepeatMachine.machine bodyProgram accepted
def words (b : ℕ) (xs : List CompetitorValidity.Estimate) := xs.flatMap (termWord b)
def folded : CompetitorValidity.Estimate → List CompetitorValidity.Estimate → CompetitorValidity.Estimate
  | a,[] => a
  | a,c::cs => folded (CompetitorRationalNumerators.add a c) cs
def loopBudget (b n : ℕ) := n*(bodyBudget b+3)+3

end NearCubicWires.RepairOrdinary.CompetitorSumFold
