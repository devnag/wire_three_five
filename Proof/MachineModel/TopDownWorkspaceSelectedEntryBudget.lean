import Proof.MachineModel.TopDownWorkspaceSelectedEntryReady

/-! The original cached header supplies a fixed-source polynomial bound for
the actual count initializer. Its degree is fixed before the hierarchy; the
prologue and append schedule are charged separately from hot supplier calls. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryBudget
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.ProjectionNormalization PaddedRunnerBudgetClosure
open RepairSource.SelectedRecoveryIntegration
open WorkspaceSelectedEntry (size)
noncomputable section

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryBudget
