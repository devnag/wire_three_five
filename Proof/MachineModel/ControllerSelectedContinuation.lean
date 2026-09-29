import Proof.CaseAnalysis.FinalFirstPhaseEntry
import Proof.CaseAnalysis.FinalRequestAtCursor
import Proof.MachineModel.ControllerSelectedLayout
import Proof.MachineModel.TopDownSelectedAssembly
import Proof.MachineModel.TopDownWorkspaceSelectedBudget
import Proof.MachineModel.TopDownWorkspaceSelectedEntryBudget

/-! Recover the complete three-phase continuation syntax at the actual selected
admission layout. This replaces the old state-count-only recipe: both state
count and Machine are exported together. EntryReady supplies the real source
count and the Repeat uses that same driver. Existing retained folds and tail
are reused. The site callback and length-only remaining fuel are explicit
construction inputs, not claimed closed by assembling the syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.ControllerSelectedContinuation
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsOriginalSchedule
noncomputable section

def extra (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) := WorkspaceSelectedEntry.size sources k r p.clauseDegree+1155+scratch

def bodyTapes (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) := WorkspaceSelectedAdmission.originalTapes sources p k+2+extra sources p k r scratch-4

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

end
end NearCubicWires.P1TopDown.ControllerSelectedContinuation
