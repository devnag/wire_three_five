import W3.Aliases
import Proof.CaseAnalysis.WitnessFamilyResourcesCosts
import Proof.CaseAnalysis.WitnessLegalPolicyRun
import Proof.CaseAnalysis.MassThresholdWidth
import W3.Proof.CaseAnalysis.WitnessCorePolicy
import W3.Proof.CaseAnalysis.Language
import W3.Proof.CaseAnalysis.ScheduleBounds
import Proof.CaseAnalysis.WitnessDescriptionPolicy
import Proof.CaseAnalysis.WitnessFamilyCount
import Proof.CaseAnalysis.WitnessMass
import Proof.CaseAnalysis.WitnessModeDivide
import Proof.CaseAnalysis.WitnessTermPolicy
import W3.Proof.CaseAnalysis.ScheduleClauseWidth

w3_alias_base

namespace W3


/-! The actual coefficient and term caps have one fixed-source polynomial
envelope in the guarded public input length. No hierarchy clock occurs in
the parameters of this construction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
open SourceInterfaces RepairSource RepairRepresentation CloseoutWitnessPolicy PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def coreBound (D N : ℕ) := (D+1)*(N+1)

theorem core_bound (D R N : ℕ) (h : R ≤ N) : CorePolicy.q0 D R ≤ coreBound D N := by
  have hc:=CloseoutLanguage.clause_linear D R
  unfold CorePolicy.q0 coreBound
  nlinarith


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources

end W3
