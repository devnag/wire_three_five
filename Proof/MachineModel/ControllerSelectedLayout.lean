import Proof.CaseAnalysis.FinalRetainedPhaseFold
import Proof.MachineModel.TopDownWorkspaceSelectedEntryRepeat

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1TopDown.ControllerSelectedLayout
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding

def location (t P i : Nat) : Nat :=
  if i=0 then 0 else if i=1 then 1 else if i=216 then t+1
  else if i<P then t+2+i else if i<P+t-2 then i-P+2
  else if i=P+t-2+51 then t+2 else i+4

theorem facts (t P extra : Nat) (ht : 2 ≤ t) (hP : 302 ≤ P)
    (hspace : P+1155 ≤ extra) :
    (∀ i, i < t+2+extra-4 → location t P i < t+2+extra) ∧
    (∀ i j, i < t+2+extra-4 → j < t+2+extra-4 →
      location t P i=location t P j → i=j) ∧
    (∀ i, i < t+2+extra-4 → location t P i ≠ t+2+P+51) ∧
    (∀ i, i<P → location t P i=
      (if i=0 then 0 else if i=1 then 1 else if i=216 then t+1 else t+2+i)) ∧
    (∀ j, j<t → location t P (if j<2 then j else P+j-2)=j) ∧
    (∀ i, P+t-2 ≤ i → i ≠ P+t-2+51 → location t P i=i+4) := by
  unfold location
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    split_ifs <;> omega
  · intro i j hi hj he
    split_ifs at he <;> omega
  · intro i hi he
    split_ifs at he <;> omega
  · intro i hi
    split_ifs <;> omega
  · intro j hj
    split_ifs <;> omega
  · intro i hi hne
    split_ifs <;> omega

def body {t P extra : Nat} (ht : 2 ≤ t) (hP : 302 ≤ P)
    (hspace : P+1155 ≤ extra) (i : Fin (t+2+extra-4)) : Fin (t+1+1+extra) :=
  ⟨location t P i.val, by have := (facts t P extra ht hP hspace).1 i.val i.isLt; omega⟩

noncomputable section
variable (sources : EightSources) {gamma : Real} (par : Parameters sources gamma)
  (k r extra : Nat)

def selectedBody (hspace : WorkspaceSelectedEntry.size sources k r par.clauseDegree+1155 ≤ extra) :=
  body (WorkspaceSelectedEntryReady.old_size sources par k)
    (show 302 ≤ WorkspaceSelectedEntry.size sources k r par.clauseDegree by
      dsimp [WorkspaceSelectedEntry.size]; omega) hspace

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

end
end NearCubicWires.P1TopDown.ControllerSelectedLayout
