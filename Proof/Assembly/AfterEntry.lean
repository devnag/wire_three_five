import Proof.Assembly.CappedReady

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ687b3b71abe848ce_
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource SourceInterfaces RepairSource.CloseoutFinal
open ControllerSelectedContinuation
open PCJad94ffa93252467f_SelectedFactorization (branch)
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size branch

theorem space (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) :
    WorkspaceSelectedEntry.size sources k r p.clauseDegree+96 ≤ extra sources p k r scratch := by
  dsimp [extra]; omega

end
end PCJ687b3b71abe848ce_
