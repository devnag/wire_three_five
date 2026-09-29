import Proof.Assembly.ActualClause

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal P1TopDown
noncomputable section

section body
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat) (mode : Bool)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

end body

end
end NearCubicWires.SourceRequest.SelLocal

