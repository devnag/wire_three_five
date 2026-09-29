import Proof.MachineModel.TopDownWorkspaceSelectedProgram
import Proof.CaseAnalysis.FinalOriginalFrame

/-! The actual admitted parser exit retains the original input, witness and
mode words. This enriches the same selected physical admission run by
receipt determinism; it does not execute the source a second time. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedOriginals
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open WorkspaceGuardedWorker (input entry reference)
open WorkspaceSelectedAdmission (originalTapes coldCutoff preFuel capacity)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine
  CloseoutFinalC10ColdCacheRewind.machine WorkspaceSelectedProgram.admission
  WorkspaceSelectedAdmission.admission

end
end NearCubicWires.P1TopDown.WorkspaceSelectedOriginals
