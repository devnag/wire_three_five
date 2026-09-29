import Proof.MachineModel.TopDownWorkspaceSelectedProgram

/-! The chosen physical admission has a degree fixed before k. The selected
capacity, cutoff, source and denominators are actual definitions, so this
statement has no free capacity or polynomial preprocessing premise. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedBudget
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open WorkspaceSelectedAdmission (originalTapes preFuel capacity coldCutoff)
noncomputable section

end
end NearCubicWires.P1TopDown.WorkspaceSelectedBudget
