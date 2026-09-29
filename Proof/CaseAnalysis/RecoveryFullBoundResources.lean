import Proof.CaseAnalysis.RecoveryFullBound
import Proof.Circuits.PaddedRunnerBudgetClosure

/-! One loose fixed-degree polynomial pays the complete cold oracle-cap
producer, including the actual marker rewrite, copy and head restoration. -/
namespace NearCubicWires.RepairOrdinary.RecoveryFullBound
open LocalBitMultitape RepairSource RecoveryScheduleEnvelope
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def degree (d : ℕ) := 2*exponent d+2
def coefficient (d : ℕ) := DimensionPolynomial.coefficient (exponent d) 1+11

theorem budget_bound (d R : ℕ) : budget d R≤coefficient d*(R+2)^degree d := by
  have hb:=DimensionPolynomial.budget_bound (exponent d) 1 R
  have hv:=power_value d R
  have hf : oracleSizeBound d R≤(R+1)^exponent d := by
    dsimp only [DimensionPolynomial.value,Nat.one_mul] at hv
    omega
  have hp : oracleSizeBound d R≤(R+2)^degree d :=
    (hf.trans (Nat.pow_le_pow_left (by omega) (exponent d))).trans
      (Nat.pow_le_pow_right (by omega) (by unfold degree;omega))
  have hone : 1≤(R+2)^degree d := Nat.one_le_pow _ _ (by omega)
  change _≤DimensionPolynomial.coefficient (exponent d) 1*(R+2)^degree d at hb
  unfold budget coefficient
  nlinarith

end
end NearCubicWires.RepairOrdinary.RecoveryFullBound
