import Proof.Assembly.Clause
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ30aa6f1b7c2a4221_
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding RecoveryRootRound
open RepairSource RepairSource.CloseoutFinal P1TopDown SelectedRecoveryIntegration
noncomputable section
namespace Selected
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k r scratch : Nat) (mode : Bool)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

end Selected
end
end PCJ30aa6f1b7c2a4221_
