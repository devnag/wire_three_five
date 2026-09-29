import Proof.CaseAnalysis.WitnessSampledSource
import Proof.CaseAnalysis.WitnessFamilySupportRun

/-! The physical source call and the selected outer PCP give the same
request. Dimension casts are discharged before the source circuit is used. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def hierarchy (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n=>n^(k+2))):=
  (sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
def code (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n=>n^(k+2))):=
  VerifierEncoding.code (hierarchy sources k clock).verifier

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
