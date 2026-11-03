import Proof.MachineModel.TopDownWorkspaceSelectedEntryBudget
import Proof.MachineModel.TopDownSelectedRuntime

/-! Apply the selected-worker Runtime split with the actual entry initializer
paid once. The only remaining numeric execution bound is for the continuation
after entry, with its single residual-table term retained explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryRuntime
open LocalBitMultitape RepairOrdinary RepairSource SourceInterfaces
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
noncomputable section

def entryDegree (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) :=
  Classical.choose (WorkspaceSelectedEntryBudget.degree_before_hierarchy sources p)

def degree (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (remainingDegree : Nat) :=
  max (entryDegree sources p) remainingDegree

def fuel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r : Nat) (remaining : Nat→Nat) (n : Nat) :=
  WorkspaceSelectedEntryBudget.envelope sources p k r n+1+remaining n

theorem entry_bound (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r : Nat) :
    ∃ coefficient onset,∀ n,onset≤n →
      WorkspaceSelectedEntryBudget.envelope sources p k r n≤coefficient*(n+1)^entryDegree sources p :=
  Classical.choose_spec (WorkspaceSelectedEntryBudget.degree_before_hierarchy sources p) k r

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryRuntime
