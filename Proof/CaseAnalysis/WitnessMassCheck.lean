import Proof.CaseAnalysis.WitnessMassStep

/-! The unchanged fixed absolute-mass cap is checked by the existing paid
constant printer, native-bank clear, and exact rational comparator. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassCheck
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def machine (k : ℕ) (q : ℚ):=CompetitorThresholdAmbient.machine false k q

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassCheck
