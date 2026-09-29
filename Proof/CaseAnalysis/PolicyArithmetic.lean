import Proof.CaseAnalysis.WitnessPolicy

/-! Exact arithmetic for the existing family policy. Fixed rational data is
represented by its numerator and positive denominator; restricted description
caps use a bit-length shift and never materialize the exponential parameter. -/
namespace NearCubicWires.RepairSource.CloseoutWitnessPolicy
open SourceInterfaces RepairRepresentation RepairOrdinary
open RecoveryWitnessPolicy ComponentwiseCircuitRestriction ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def termFactor (delta : ℚ) (copies : Nat) : ℚ :=
  16 / (delta^2 * epsilonQ delta copies^2)
def termNumerator (delta : ℚ) (copies : Nat) := (termFactor delta copies).num.natAbs
def termDenominator (delta : ℚ) (copies : Nat) := (termFactor delta copies).den

end
end NearCubicWires.RepairSource.CloseoutWitnessPolicy
