import Proof.CaseAnalysis.FinalTotalDecode
import Proof.CaseAnalysis.FinalOnset
import Proof.CaseAnalysis.FinalPipeline

/-! Paper C.10 tests the two validity estimates and C.10.1 the acceptance mean.
The existing decision bridge proves these facts from a decoded, pinned verdict.
Here the phase widths belong to that verdict: they are inside the existential,
as in Pipeline, because the guessed families determine the phase call counts.
This is external_in.md section 0.3's authorized sibling of C10Decides. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10DecidesUniform

open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CanonicalWitnessCodec RecoveryScheduleEnvelope
open ExtDecompositionBatch CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10Verdict
open NearCubicWires.RepairSource.CloseoutFinal

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section


end
end NearCubicWires.RepairSource.CloseoutFinal.C10DecidesUniform
