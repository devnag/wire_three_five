import Proof.Rows.TopFrameReady

/-! Bounded reusable extraction of one actual circuit from framed topWord. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_TopFrameReentry
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def heads (pos : Nat) : Fin 10→Nat:=![0,pos,0,1,0,0,0,0,0,0]
def bank (source out : List Bool) (index U : Nat) : Fin 10→List Bool:=
  ![frame source,List.replicate U false,List.replicate U false,ZeroPadding.pad U (CompareMachine.word index),
    List.replicate U false,List.replicate U false,out,List.replicate U false,
    List.replicate U true,List.replicate (U+1) false]
def extract:=TapeEmbedding.machine 2 PCJ45bee56da9f34d5a_TopFrame.machine
def rewind:=PCJ45bee56da9f34d5a_HeaderRewind.machine 8
def clearSlots : Fin 7→Fin 10:=![1,2,4,5,7,8,9]
def erase:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 5)
def raise:=DecompositionCountPosition.move (fun i : Fin 10=>if i=3 then .right else .stay)
def clean:=Composition.machine (Composition.machine rewind erase) raise
def machine:=Composition.machine extract clean

theorem clean_run (source bits : List Bool) (index U : Nat) (H : Fin 10→Nat) (A : Fin 10→List Bool)
    (hH : ∀ j : Fin 8,H (j.castAdd 2)≤U)
    (hA : ∀ j : Fin 5,(A (clearSlots j.castSucc.castSucc)).length≤U)
    (h8 : H 8=0) (h9 : H 9=0)
    (a0 : A 0=frame source) (a3 : A 3=ZeroPadding.pad U (CompareMachine.word index))
    (a6 : A 6=ZeroPadding.pad U bits) (a8 : A 8=List.replicate U true)
    (a9 : A 9=List.replicate (U+1) false) :
    Step clean (4*U+11) H A (heads 0) (bank source (ZeroPadding.pad U bits) index U):=by
  have first:=PCJ45bee56da9f34d5a_HeaderRewind.run 8
    (fun j : Fin 8=>H (j.castAdd 2)) (fun j : Fin 8=>A (j.castAdd 2)) U hH
  have first':Step rewind (2*U+4) H A (fun _=>0) A:=by
    refine (first.congr_in ?_ ?_).congr rfl ?_
    · funext j;fin_cases j <;>first | rfl | exact h8.symm | exact h9.symm
    · funext j;fin_cases j <;>first | rfl | exact a8.symm | exact a9.symm
    · funext j;fin_cases j <;>first | rfl | exact a8.symm | exact a9.symm
  let scratch : Fin 5→List Bool:=fun j=>A (clearSlots j.castSucc.castSucc)
  have second:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) scratch hA)).dock
    clearSlots (by decide) (fun _ : Fin 10=>0) A
    (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>first | rfl | exact a8 | exact a9)
  have second':Step erase (2*U+4) (fun _=>0) A (fun _=>0) (bank source (ZeroPadding.pad U bits) index U):=by
    apply second.congr
    · exact dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
    · apply HierarchyAllocation.install_eq clearSlots (by decide)
      · intro j;fin_cases j <;>simp only [Nat.max_self] <;>rfl
      · intro j hj;fin_cases j
        all_goals first
          | exact a0.symm
          | exact a3.symm
          | exact a6.symm
          | exact False.elim (hj 0 rfl)
          | exact False.elim (hj 1 rfl)
          | exact False.elim (hj 2 rfl)
          | exact False.elim (hj 3 rfl)
          | exact False.elim (hj 4 rfl)
          | exact False.elim (hj 5 rfl)
          | exact False.elim (hj 6 rfl)
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun j : Fin 10=>if j=3 then .right else .stay) (fun _=>0) (bank source (ZeroPadding.pad U bits) index U)
  have last:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
    (show _=heads 0 by funext j;fin_cases j <;>rfl) rfl
  have all:=(first'.seq second').seq last
  simpa only [clean,raise,show ((2*U+4)+1+(2*U+4))+1+1=4*U+11 by omega] using all

def budget (words : List (List Bool)) (i : Fin words.length) (B : Nat):=
  4*(words.flatMap frame).length+CloseoutRowsTouching.FrameSeek.budget B i.val+8*(words.get i).length+11

theorem run (words : List (List Bool)) (i : Fin words.length) (B U : Nat)
    (hb : ∀ x∈words,x.length≤B) (hu : budget words i B+2≤U) :
    Step machine (budget words i B+4*U+12)
      (heads 0) (bank (words.flatMap frame) (List.replicate U false) i.val U)
      (heads 0) (bank (words.flatMap frame) (ZeroPadding.pad U (words.get i)) i.val U):=by
  obtain ⟨H,A,h,_h6,a6,a0,a3⟩:=PCJ45bee56da9f34d5a_TopFrameReady.retained_run words i B hb
  change Step _ (budget words i B) _ _ _ _ at h
  let outH : Fin 10→Nat:=Fin.addCases (m:=8) (n:=2) (motive:=fun _=>Nat) H (fun _=>0)
  let outA : Fin 10→List Bool:=Fin.addCases (m:=8) (n:=2) (motive:=fun _=>List Bool)
    (fun j=>ZeroPadding.pad (if j=0 then 0 else U) (A j))
    (![List.replicate U true,List.replicate (U+1) false] : Fin 2→List Bool)
  have first:=(h.pad (fun j : Fin 8=>if j=0 then 0 else U)).embed (fun _ : Fin 2=>0)
    (![List.replicate U true,List.replicate (U+1) false] : Fin 2→List Bool)
  have first':Step extract (budget words i B) (heads 0)
      (bank (words.flatMap frame) (List.replicate U false) i.val U) outH outA:=by
    refine first.congr_in ?_ ?_
    all_goals funext j;fin_cases j <;>simp [heads,bank,PCJ45bee56da9f34d5a_TopFrame.heads,
      PCJ45bee56da9f34d5a_TopFrame.input,Fin.addCases,ZeroPadding.pad]
  have hheads:∀j : Fin 8,outH (j.castAdd 2)≤U:=by
    intro j
    obtain ⟨r,hr,rh,_rt,rs⟩:=h
    have hb:=SelectiveReset.prefix_head (prefix_of_run _ _ _ _ hr).1 j
    rw [rh] at hb
    simp only [outH,Fin.addCases_left]
    have hi:PCJ45bee56da9f34d5a_TopFrame.heads 0 j≤1:=by fin_cases j <;>decide
    change H j≤PCJ45bee56da9f34d5a_TopFrame.heads 0 j+r.steps at hb
    omega
  have htapes:∀j : Fin 5,(outA (clearSlots j.castSucc.castSucc)).length≤U:=by
    intro j
    let k : Fin 8:=![1,2,4,5,7] j
    have hk:(PCJ45bee56da9f34d5a_TopFrame.input (words.flatMap frame) i.val k).length≤U:=by fin_cases j <;>simp [k,PCJ45bee56da9f34d5a_TopFrame.input]
    have hi:PCJ45bee56da9f34d5a_TopFrame.heads 0 k+budget words i B+1≤U:=by fin_cases j <;>simp [k,PCJ45bee56da9f34d5a_TopFrame.heads] <;>omega
    have fits:=NearCubicWires.P1Closure.LocalSupport.step_fits h k U hk hi
    fin_cases j <;>simpa [outA,clearSlots,k,Fin.addCases,ZeroPadding.pad_length] using fits
  have o0:outA 0=frame (words.flatMap frame):=by
    change ZeroPadding.pad 0 (A 0)=_;rw [ZeroPadding.pad_zero,a0]
  have o3:outA 3=ZeroPadding.pad U (CompareMachine.word i.val):=congrArg (ZeroPadding.pad U) a3
  have o6:outA 6=ZeroPadding.pad U (words.get i):=congrArg (ZeroPadding.pad U) a6
  have last:=clean_run (words.flatMap frame) (words.get i) i.val U outH outA hheads htapes
    rfl rfl o0 o3 o6 rfl rfl
  have all:=first'.seq last
  unfold machine
  convert all using 1
  omega
end
end PCJ45bee56da9f34d5a_TopFrameReentry
