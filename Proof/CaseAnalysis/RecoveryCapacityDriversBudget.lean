import Proof.CaseAnalysis.RecoveryCapacityDrivers
import Proof.CaseAnalysis.CaseTwoBudget

/-! All physical capacity production and reset-log allocation is polynomial
in the already paid raw W. Its producer remains the common controller's call. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCapacityDrivers
open LocalBitMultitape PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem generic_polynomial (C B J : ℕ) : SourcePoly (genericBudget C B J):=by
  have hc:=CloseoutCaseTwo.ColdBudget.power_polynomial sourcePoly_id 2 C
  have hb:=CloseoutCaseTwo.ColdBudget.power_polynomial sourcePoly_id 6 B
  have hn:=(sourcePoly_pow (sourcePoly_id.add (polyDominated_const 1)) 6).const_mul B
  have ho : SourcePoly (fun W=>Offset.budget J (B*(W+1)^6)):=by
    apply ((hn.const_mul 4).add (polyDominated_const (6*J+14))).mono
    intro W
    unfold Offset.budget
    omega
  exact (((hc.add (polyDominated_const 1)).add hb).add (polyDominated_const 1)).add ho

end NearCubicWires.RepairOrdinary.RecoveryCapacityDrivers
