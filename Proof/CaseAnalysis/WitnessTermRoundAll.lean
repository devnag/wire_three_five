import Proof.CaseAnalysis.WitnessTermChoice

/-! One total term result combines all three checked physical branches.
The only pending worker premise is the same full circuit call on the
retained payload and paid source/mode fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRoundAll
open LocalBitMultitape CanonicalWitnessCodec RadixSemantics CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def accepted (C : ℕ) (bits : List Bool) (circuitPass : Bool) :=
  (TermChoice.coefficient (natBitLength C) bits).isSome && circuitPass

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRoundAll
