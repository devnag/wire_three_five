import Proof.CaseAnalysis.WitnessFamilyRound

/-! The exact outer list addresses one sum per source variable. Its
invariant carries only the zero accumulator and the three ordered
logical streams. The successor bank is projected from the same receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def passed (C T : ℕ) (q : ℚ) (words : List (List Bool)) (arity : List Bool) (circuitPass : List Bool → Bool):=
  words.all (fun bits=>SumRound.passed C T q bits arity circuitPass)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoop
