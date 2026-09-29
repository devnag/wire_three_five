import Proof.CaseAnalysis.WitnessFamilyMode
import Proof.CaseAnalysis.WitnessFamilyPrepare

/-! Actual cold family validation in either mode: paid workspace setup,
canonical exact-V header, every original sum and term, actual circuit
worker, coefficient guard, exact mass test and retained native streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def passed (sym : Bool) (V C T core W L : ℕ) (q : ℚ) (bits arity : List Bool):=
  FamilyRun.passed V C T q bits arity (FamilyMode.flag sym core W L)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold
