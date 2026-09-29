import Proof.Assembly.BranchPhases
import Proof.CaseAnalysis.FinalUnaryAddress

/-! Exact live-clause consumer. The actual source-count loop visits only
indices below its source count; no saturated/idle execution is required.
Unrelated ambient heads are preserved (the prologue counter need not be zero).
The site execution and restored clean cache remain explicit obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ30aa6f1b7c2a4221_
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding RecoveryRootRound
open RepairSource.CloseoutFinal
open CloseoutFinalC10UnaryAddressProbe
noncomputable section

variable {B : Nat} (cache : Fin 19 → Fin B) (hi : Function.Injective cache)


attribute [local irreducible] P1TopDown.WorkspaceSelectedAdmission.originalTapes
 P1TopDown.WorkspaceSelectedEntry.size

end
end PCJ30aa6f1b7c2a4221_
