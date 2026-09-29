import Proof.MachineModel.ControllerCappedSelected
import Proof.MachineModel.ControllerSelectedContinuation

/-! Preserve the C.10 choice order and complete runtime obligation at the
capped physical parser. Reuse the existing additive ledger and same three-phase
continuation syntax. This supplies no estimate for the still-unbuilt supplier. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.ControllerCappedRuntime
open RepairOrdinary RepairSource SourceInterfaces
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open ControllerCappedSelected
noncomputable section

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

end
end NearCubicWires.P1TopDown.ControllerCappedRuntime
