import Proof.CaseAnalysis.RowsEstimatorCoefficientsBody
import Proof.Hierarchy.CompetitorMonomialEntry

/-! The original finite scalar-stream loop and cold entry, specialized to
signed Estimate coefficients. All repeated controllers, drivers and budgets
are the accepted ones; only the coefficient representation is generalized. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Stream
open CompetitorMonomialStream
def entryWord (b : ℕ) (a : Entry) := recordWord b a.coefficient a.count a.denominator
def words (b : ℕ) (xs : List Entry) := xs.flatMap (entryWord b)
def contributions (xs : List Entry) := xs.map Entry.estimate

end Stream

namespace EntryMachine
open Stream CompetitorMonomialEntry
open CompetitorMonomialStream (coldInput zeroed cold_clear_run zeroed_store Store loopProgram loopBudget cfg bodyProgram heads)

def input (b t : ℕ) (xs : List Entry) := extendTapes (coldInput b t (words b xs)) xs.length

def readyInput (b t : ℕ) (xs : List Entry) : Fin 90 → List Bool :=
  Fin.addCases (m := 89) (n := 1) (motive := fun _ => List Bool) (input b t xs) (fun _ => [])

end EntryMachine
end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
