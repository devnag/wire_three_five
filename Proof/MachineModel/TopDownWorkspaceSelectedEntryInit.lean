import Proof.CaseAnalysis.FinalAdmittedEntry
import Proof.MachineModel.TopDownWorkspaceSelectedEntryFacts

/-! Dock the existing grouped initializer after the actual direct prologue.
It aliases the retained original cache and the produced width driver, and uses
96 further fresh tapes. The envelope-counter head is outside this call. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryInit
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RecoveryRootRound
open WorkspaceSelectedEntry (size slots output outputHeads)
open WorkspaceSelectedEntryFacts
noncomputable section

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryInit
