import Proof.MachineModel.ControllerCappedSelected
import Proof.MachineModel.TopDownWorkspaceSelectedOriginals

/-! Recover the original header words at the exact capped admission boundary.
The proof uses the same denominator and deterministic run, retaining the original
Originals predicate and the caller's final bank. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ138fdb4302e34c7e_CappedOriginals
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open WorkspaceGuardedWorker (input entry)
open WorkspaceSelectedAdmission (originalTapes coldCutoff capacity)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine
  CloseoutFinalC10ColdCacheRewind.machine ControllerCappedSelected.admission

end
end PCJ138fdb4302e34c7e_CappedOriginals
