import Proof.MachineModel.TopDownWorkspaceSelectedEntryReady

/-! Factor the existing physical entry execution through its actual input
facts. The fixed program, execution budget, output heads and installed bank
are unchanged; no admission or entry Step is added as a premise. -/
namespace PCJ57feb257fbc0439a_
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration CanonicalWitnessCodec
open WorkspaceSelectedAdmission (originalTapes capacity)
open WorkspaceSelectedEntry (size output outputHeads)
open RecoveryRootRound
open WorkspaceSelectedEntryReady
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

end
end PCJ57feb257fbc0439a_
