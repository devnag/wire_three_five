import Proof.Rows.HeaderErase

/-! Physically rewind bounded dirty Header heads before the scratch sweep.
The unary U driver is scanned once; only its own head needs the recorded
return pass. No tape content is changed, and the cap driver/log are reusable.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ45bee56da9f34d5a_HeaderRewind
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution

variable (t : Nat)

def raw : Machine (t+1) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then
    if scanned ((0 : Fin 1).natAdd t) then some ⟨0,fun _=>none,
      Fin.addCases (fun _ : Fin t=>.left) (fun _ : Fin 1=>.right)⟩
    else some ⟨1,fun _=>none,fun _=>.stay⟩
    else none

def heads (H : Fin t→Nat) (done : Nat) : Fin (t+1)→Nat :=
  Fin.addCases (fun i=>H i-done) (fun _ : Fin 1=>done)

def bank (A : Fin t→List Bool) (U : Nat) : Fin (t+1)→List Bool :=
  Fin.addCases A (fun _ : Fin 1=>List.replicate U true)

def cfg (H : Fin t→Nat) (A : Fin t→List Bool) (U done : Nat) (s : Fin 2) :
    Configuration (t+1) 2 := ⟨s,heads t H done,bank t A U⟩

theorem advance (H : Fin t→Nat) (A : Fin t→List Bool) (U done : Nat) (hd : done<U) :
    step (raw t) (cfg t H A U done 0)=some (cfg t H A U (done+1) 0) := by
  have hr : readTapeBit (List.replicate U true) done=true := by
    simp [readTapeBit,List.getD,hd]
  simp only [step,raw,cfg,Configuration.scanned,bank,heads,Fin.addCases_right,
    Fin.val_zero,hr,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t) (n:=1) (fun i=>?_) (fun i=>?_) i
    · simp only [applyAction,heads,Fin.addCases_left,HeadMove.apply]
      omega
    · simp only [applyAction,heads,Fin.addCases_right,HeadMove.apply]
  · rfl

theorem stop (H : Fin t→Nat) (A : Fin t→List Bool) (U : Nat) :
    step (raw t) (cfg t H A U U 0)=some (cfg t H A U U 1) := by
  have hr : readTapeBit (List.replicate U true) U=false := by
    simp [readTapeBit,List.getD]
  simp only [step,raw,cfg,Configuration.scanned,bank,heads,Fin.addCases_right,
    Fin.val_zero,hr,↓reduceIte]
  rfl

theorem walk_prefix (H : Fin t→Nat) (A : Fin t→List Bool) (n done : Nat) :
    Timed (raw t) (n+1) (cfg t H A (done+n) done 0)
      (cfg t H A (done+n) (done+n) 1) := by
  induction n generalizing done with
  | zero => simpa only [Nat.add_zero] using Timed.single (by rfl) (stop t H A done)
  | succ n ih =>
    have ht := ih (done+1)
    have he : done+1+n=done+(n+1) := by omega
    rw [he] at ht
    exact Timed.step (by rfl) (advance t H A (done+(n+1)) done (by omega)) ht

theorem raw_run (H : Fin t→Nat) (A : Fin t→List Bool) (U : Nat) :
    Step (raw t) (U+1) (Fin.addCases H (fun _ : Fin 1=>0)) (bank t A U)
      (heads t H U) (bank t A U) := by
  have hp := walk_prefix t H A U 0
  simp only [Nat.zero_add] at hp
  obtain ⟨r,hr,hf,_⟩ := hp.run (by rfl)
  have hi : cfg t H A U 0 0 =
      (⟨(raw t).start,Fin.addCases H (fun _ : Fin 1=>0),bank t A U⟩ : Configuration (t+1) 2) := by
    rfl
  rw [hi] at hr
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

def selected : Fin (t+1)→Bool := Fin.addCases (fun _ : Fin t=>false) (fun _ : Fin 1=>true)
def machine := MaskedReset.machine (raw t) (selected t)

theorem run (H : Fin t→Nat) (A : Fin t→List Bool) (U : Nat) (hH : ∀ i,H i≤U) :
    Step (machine t) (2*U+4)
      (Fin.addCases (Fin.addCases H (fun _ : Fin 1=>0)) (fun _ : Fin 1=>0))
      (PCJ45bee56da9f34d5a_Plan.clearInput U (U+1) A)
      (fun _=>0) (PCJ45bee56da9f34d5a_Plan.clearInput U (U+1) A) := by
  have hm := (raw_run t H A U).mask (selected t) (by
    intro i
    refine Fin.addCases (m:=t) (n:=1) (fun i hi=>?_) (fun i _=>?_) i
    · simp only [selected,Fin.addCases_left,Bool.false_eq_true] at hi
    · simp only [Fin.addCases_right]) (Nat.le_refl (U+1))
  have hf : 2*(U+1)+2=2*U+4 := by omega
  rw [hf] at hm
  apply hm.congr
  · funext i
    refine Fin.addCases (m:=t+1) (n:=1) (fun i=>?_) (fun i=>?_) i
    · refine Fin.addCases (m:=t) (n:=1) (fun i=>?_) (fun i=>?_) i
      · simp only [selected,heads,Fin.addCases_left,Bool.false_eq_true,↓reduceIte,
          Nat.sub_eq_zero_of_le (hH i)]
      · simp only [selected,heads,Fin.addCases_left,Fin.addCases_right,↓reduceIte]
    · simp only [Fin.addCases_right]
  · rfl


def clear := Composition.machine (machine t) (RecoveryScratchErase.resetMachine t)

/-- Complete paid rewind-and-clear call; its input may have dirty heads. -/
theorem clear_run (H : Fin t→Nat) (A : Fin t→List Bool) (U : Nat)
    (hH : ∀ i,H i≤U) (hA : ∀ i,(A i).length≤U) :
    Step (clear t) (4*U+9)
      (Fin.addCases (Fin.addCases H (fun _ : Fin 1=>0)) (fun _ : Fin 1=>0))
      (PCJ45bee56da9f34d5a_Plan.clearInput U (U+1) A)
      (fun _=>0) (PCJ45bee56da9f34d5a_Plan.clearOutput t U (U+1)) := by
  have erase : Step (RecoveryScratchErase.resetMachine t) (2*U+4) (fun _=>0)
      (PCJ45bee56da9f34d5a_Plan.clearInput U (U+1) A) (fun _=>0)
      (PCJ45bee56da9f34d5a_Plan.clearOutput t U (U+1)) := by
    unfold PCJ45bee56da9f34d5a_Plan.clearOutput PCJ45bee56da9f34d5a_Plan.clearInput
    simpa only [Nat.max_self] using Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) A hA)
  have joined := (run t H A U hH).seq erase
  have hf : (2*U+4)+1+(2*U+4)=4*U+9 := by omega
  rw [hf] at joined
  exact joined

open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation PCJd4d1d9d7d1fa4313_Production
open PCJ45bee56da9f34d5a_RowState PCJ45bee56da9f34d5a_HeaderErase
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

end

end PCJ45bee56da9f34d5a_HeaderRewind
