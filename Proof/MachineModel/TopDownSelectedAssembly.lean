import Proof.MachineModel.TopDownWorkspaceSelectedProgram

/-! Substitute the actual admission into the literal endpoint. The complete
continuation program remains data, and its Verdict and Runtime remain open.
This is a checked reduction of the construction target, not a closed theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.SelectedAssembly
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
open RepairSource.CloseoutFinal.C10GuardedMachineConsumer
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes

end
end NearCubicWires.P1TopDown.SelectedAssembly
