import Proof.Assembly.AfterEntry
import Proof.Assembly.BranchPhases

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ374c44bb8b7f47d9_
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary P1TopDown
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
open CloseoutRowsOriginalSchedule CloseoutFinalC10Realizes
open ControllerSelectedContinuation
namespace S
open PCJda54a286946142d3_BranchPhases
noncomputable section
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size




end
end S
end PCJ374c44bb8b7f47d9_
