import Proof.MachineModel.TopDownWorkspaceGuarded

/-! Choose admission's fixed onset using k/clock alone, then build the actual
ordinary gate at that onset. The rejected branch is proved from the exact
admission receipt. The admitted continuation and whole Runtime stay explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceGuardedWorker
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal
open CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal.C10GuardedMachineConsumer
open RepairSource.CloseoutFinal.C10GuardedStageConsumer
open RepairSource.CloseoutFinal.C10Fusion
open RepairSource.CloseoutFinal.C10LengthGate
noncomputable section

/-- This datum selects only the semantic k/clock-dependent admission onset;
its dummy worker is never run by the constructed weak machine. -/
def reference (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) : WorkerData where
  k := k
  clock := clock
  tapes := 2
  states := 2
  worker := counter 0 0 1
  result := 1
  fuel := fun _ => 0
  onset := 0
  passed := fun _ _ _ => false

def input {t : Nat} (x bits : List Bool) : Fin t → List Bool :=
  fun i => if i.val=0 then RepairOrdinary.frame x else if i.val=1 then RepairOrdinary.frame bits else []

def entry {t : Nat} (lengthFlag : Fin t) (x bits : List Bool) : Fin t → List Bool :=
  exitTapes lengthFlag (input x bits) 0 true

/-- A physically rejecting run below the actual final finite gate. -/
theorem below_run {t a b : Nat} (C : Nat) (admission : Machine t a)
    (continuation : Machine t b) (inputTape lengthFlag admissionFlag result : Fin t)
    (hinput : inputTape.val=0) (hflag : lengthFlag ≠ inputTape)
    {n : Nat} (x : BitInput n) (bits : List Bool) (hn : n<C) :
    ∃ heads exit, Step (admittedWorker C admission continuation
      inputTape lengthFlag admissionFlag result) (2*n+3)
      (fun _ => 0) (input (List.ofFn x) bits) heads exit ∧
      readTapeBit (exit result) (heads result) = false := by
  have hT : input (List.ofFn x) bits inputTape = RepairOrdinary.frame (List.ofFn x) := by
    simp [input,hinput]
  have hread : ∀ j,j<2*n → j%2=0 →
      readTapeBit (input (List.ofFn x) bits inputTape) ((fun _ : Fin t => 0) inputTape+j)=true := by
    intro j hj he
    rw [hT]
    simpa only [Nat.zero_add,List.length_ofFn] using frame_short (List.ofFn x) j
      (by simpa only [List.length_ofFn] using hj) he
  have hstop : readTapeBit (input (List.ofFn x) bits inputTape)
      ((fun _ : Fin t => 0) inputTape+2*n)=false := by
    rw [hT]
    simpa only [Nat.zero_add,List.length_ofFn] using frame_stop (List.ofFn x)
  obtain ⟨r,hr,hfalse⟩ := gated_reject C inputTape lengthFlag result
    (admittedInner admission continuation admissionFlag result) hflag (fun _ => 0)
    (input (List.ofFn x) bits) n (by omega) hread hstop
  exact ⟨r.final.heads,r.final.tapes,Step.of_run hr rfl rfl,hfalse⟩

/-- Exact above-onset rejected path: run admission once and stop at its false
flag, keeping all its final heads and tapes except the decision bit. -/
theorem rejected_run {t a b : Nat} (C : Nat) (admission : Machine t a)
    (continuation : Machine t b) (inputTape lengthFlag admissionFlag result : Fin t)
    (hinput : inputTape.val=0) {n : Nat} (x : BitInput n) (bits : List Bool) (hn : C≤n)
    (preFuel : Nat) (H : Fin t → Nat) (A : Fin t → List Bool)
    (hpre : Step admission preFuel (fun _ => 0) (entry lengthFlag (List.ofFn x) bits) H A)
    (hfalse : readTapeBit (A admissionFlag) (H admissionFlag)=false) :
    Step (admittedWorker C admission continuation inputTape lengthFlag admissionFlag result)
      (4*C+5+preFuel) (fun _ => 0) (input (List.ofFn x) bits) H
      (exitTapes result A (H result) false) := by
  have inner := inner_reject admission continuation admissionFlag result preFuel
    (fun _ => 0) H (entry lengthFlag (List.ofFn x) bits) A hpre hfalse
  have hread : ∀ j,j<2*C → j%2=0 →
      readTapeBit (input (List.ofFn x) bits inputTape) ((fun _ : Fin t => 0) inputTape+j)=true := by
    intro j hj he
    rw [show input (List.ofFn x) bits inputTape = RepairOrdinary.frame (List.ofFn x) by
      simp [input,hinput]]
    simpa only [Nat.zero_add] using frame_short (List.ofFn x) j
      (by simpa only [List.length_ofFn] using (show j<2*n by omega)) he
  have whole := gated_pass C inputTape lengthFlag result
    (admittedInner admission continuation admissionFlag result) (fun _ => 0)
    (input (List.ofFn x) bits) hread (preFuel+1+1) H _ inner
  have hf : (4*C+1)+1+((preFuel+1+1)+1)=4*C+5+preFuel := by omega
  rw [hf] at whole
  exact whole

end
end NearCubicWires.P1TopDown.WorkspaceGuardedWorker
