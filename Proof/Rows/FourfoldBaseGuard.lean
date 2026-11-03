import Proof.Rows.FourfoldBaseCell
import Proof.CaseAnalysis.RowsOriginalSwitch
import Proof.CaseAnalysis.RowsGateTemplateCheck

/-! Each of the four actual circuit calls is guarded by the decoded unary
count. Absent circuits execute the empty branch without requesting a child. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_FourfoldBaseGuard
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open PCJ45bee56da9f34d5a_FourfoldBaseCell
noncomputable section

def guard (j : Fin 4):=CloseoutRowsOriginalSwitch.machine (PCJ45bee56da9f34d5a_FourfoldBaseCell.machine j)
  (CloseoutRowsOriginalSwitch.stop 82) 81
def advance:=DecompositionCountPosition.move (fun i : Fin 82=>if i=81 then .right else .stay)
def left:=DecompositionCountPosition.move (fun i : Fin 82=>if i=81 then .left else .stay)
def restore:=Composition.machine (Composition.machine (Composition.machine left left) left) left
def phase (j : Fin 4):=Composition.machine (guard j) advance

theorem true_run (j : Fin 4) (digits : Fin 4→Nat) (words : List (List Bool)) (circuit : Fin words.length) (B : Nat) {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (v w C D U a : Nat)
    (hci : circuit.val=j.val) (hdigit : digits j=i.val)
    (hi : i.val<2^v) (hv : MatrixUnaryTemplate.budget v i.val<U)
    (hb : ∀x∈words,x.length ≤ B)
    (htop : PCJ45bee56da9f34d5a_TopFrameReentry.budget words circuit B+2 ≤ U)
    (hselected : words.get circuit=PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
    (hu : PCPPQueryNatural.budget n<U)
    (hp : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length ≤ U)
    (hf : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1 ≤ U)
    (hg : (exactWord (gs.get i)).length+2 ≤ U)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items (gs.get i),natBitLength x.1.natAbs ≤ w)
    (hc : 8*w+12 ≤ C) (hm : childMagnitude (gs.get i)<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items (gs.get i)) w C ≤ D)
    (hC : C+1 ≤ U) (hDU : D ≤ U) (ha : childMagnitude (gs.get i)+a<2^(w+2))
    (hF : C10ThresholdChildMagnitude.budget (gs.get i) w C+2 ≤ U)
    (hU : ∀ j,(PCJ45bee56da9f34d5a_SelectedBase.Base.words (ZeroPadding.pad U (exactWord (gs.get i))) (List.replicate (n+1) true)
      (n+1) w C U a j).length ≤ U) :
    Step (guard j) (PCJ45bee56da9f34d5a_DigitBaseRun.budget words circuit B gs i v w C U+2)
      (heads (j.val+1)) (bank (words.flatMap frame) digits words.length v w C U a)
      (heads (j.val+1)) (bank (words.flatMap frame) digits words.length v w C U (childMagnitude (gs.get i)+a)):=by
  have h:=PCJ45bee56da9f34d5a_FourfoldBaseCell.run j digits (j.val+1) words circuit B gs i v w C D U a
    hci hdigit hi hv hb htop hselected hu hp hf hg hw hc hm hD hC hDU ha hF hU
  apply CloseoutRowsOriginalSwitch.true_run _ _ _ h
  change readTapeBit (ZeroPadding.pad U (UnaryTemplate.tape words.length)) (j.val+1)=true
  rw [ZeroPadding.read_pad]
  exact UnaryTemplate.tape_mark _ _ (by have hc:=circuit.isLt;omega)

theorem false_run (j : Fin 4) (source : List Bool) (digits : Fin 4→Nat) (N v w C U a : Nat)
    (hN : N ≤ j.val):
    Step (guard j) 2 (heads (j.val+1)) (bank source digits N v w C U a)
      (heads (j.val+1)) (bank source digits N v w C U a):=by
  let cfg:Configuration 82 1:=⟨0,heads (j.val+1),bank source digits N v w C U a⟩
  let r:ExecutionReceipt 82 1:=⟨cfg,0,cfg.tapeCells⟩
  have h:Step (CloseoutRowsOriginalSwitch.stop 82) 0 (heads (j.val+1)) (bank source digits N v w C U a)
      (heads (j.val+1)) (bank source digits N v w C U a):=
    Step.of_run (show runFrom (CloseoutRowsOriginalSwitch.stop 82) 0 cfg=some r from rfl) rfl rfl
  apply CloseoutRowsOriginalSwitch.false_run _ _ _ h
  change readTapeBit (ZeroPadding.pad U (UnaryTemplate.tape N)) (j.val+1)=false
  rw [ZeroPadding.read_pad,CloseoutRowsGateTemplateCheck.template_read]
  simp only [decide_eq_false_iff_not]
  omega

theorem advance_run (source : List Bool) (digits : Fin 4→Nat) (N v w C U a pos : Nat):
    Step advance 1 (heads pos) (bank source digits N v w C U a)
      (heads (pos+1)) (bank source digits N v w C U a):=by
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 82=>if i=81 then .right else .stay) (heads pos) (bank source digits N v w C U a)
  apply (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
  · funext i;by_cases hi:i=81 <;>simp [heads,hi,HeadMove.apply]
  · rfl

theorem left_run (source : List Bool) (digits : Fin 4→Nat) (N v w C U a pos : Nat):
    Step left 1 (heads (pos+1)) (bank source digits N v w C U a)
      (heads pos) (bank source digits N v w C U a):=by
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 82=>if i=81 then .left else .stay) (heads (pos+1)) (bank source digits N v w C U a)
  apply (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
  · funext i;by_cases hi:i=81 <;>simp [heads,hi,HeadMove.apply]
  · rfl

theorem restore_run (source : List Bool) (digits : Fin 4→Nat) (N v w C U a : Nat):
    Step restore 7 (heads 5) (bank source digits N v w C U a)
      (heads 1) (bank source digits N v w C U a):=by
  exact (((left_run source digits N v w C U a 4).seq (left_run source digits N v w C U a 3)).seq
    (left_run source digits N v w C U a 2)).seq (left_run source digits N v w C U a 1)
end
end PCJ45bee56da9f34d5a_FourfoldBaseGuard
