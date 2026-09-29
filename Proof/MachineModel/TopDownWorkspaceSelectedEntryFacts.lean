import Proof.MachineModel.TopDownWorkspaceSelectedEntry

/-! Same-admission application and exact frame facts for the direct prologue.
No original-word premise is left on the public admission-to-entry theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryFacts
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal
open WorkspaceGuardedWorker (entry reference)
open WorkspaceSelectedAdmission (originalTapes preFuel coldCutoff)
open WorkspaceSelectedEntry RecoveryRootRound
noncomputable section
attribute [local irreducible] WorkspaceSelectedProgram.admission

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryFacts
