import Proof.Assembly.ThreePhaseTail
import Proof.Assembly.BranchPhases
import Proof.Assembly.AfterEntry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ374c44bb8b7f47d9_
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary P1TopDown
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
open CloseoutRowsOriginalSchedule CloseoutFinalC10Realizes
open ControllerSelectedContinuation
open PCJ687b3b71abe848ce_ (readyBank)
namespace S
open PCJda54a286946142d3_BranchPhases
noncomputable section
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

def ports := recordPort (offset sources p k r) (bodyTapes sources p k r scratch)
 (tapes sources p k r scratch) (offset_ge sources p k r) (fresh_lt sources p k r scratch)
 (body sources p k r scratch)
def heads := WorkspaceSelectedEntryReady.finalHeads sources p k r (extra sources p k r scratch)
 (PCJ687b3b71abe848ce_.space sources p k r scratch)
def bank := readyBank sources p den hden k r (extra sources p k r scratch)
 (PCJ687b3b71abe848ce_.space sources p k r scratch) n x bits hp
def mode := readTapeBit (bank sources p den hden k r scratch n x bits hp
 (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch)))
 (heads sources p k r scratch (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch)))



end
end S
end PCJ374c44bb8b7f47d9_
