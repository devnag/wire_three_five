import Proof.Rows.TopNativeChild
import Proof.Rows.TopIndex

/-! The selected native child is delivered in a reusable bounded bank. The
original circuit payload, unary arity and child digit survive; all locator
and copy scratch is paidly cleared and the source is physically rewound. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_TopChildReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.P1Closure
noncomputable section

def head (pos prior : Nat) : Fin 9→Nat:=![pos,0,prior,1,1,0,0,0,0]
def bank (source backing prior out : List Bool) (n index U : Nat) (copy : List Bool) : Fin 9→List Bool:=
  ![source,ZeroPadding.pad U backing,ZeroPadding.pad U prior,
    ZeroPadding.pad U (UnaryTemplate.tape n),ZeroPadding.pad U (UnaryTemplate.tape index),
    copy,out,List.replicate U true,List.replicate (U+1) false]
def ready (source out : List Bool) (n index U : Nat):=
  bank source [] [] out n index U (List.replicate U false)
def caps (U : Nat) (i : Fin 9):=if i=1 ∨ i=2 ∨ i=3 ∨ i=4 then U else 0

theorem selected_run {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (U : Nat)
    (hg : (exactWord (gs.get i)).length≤U) :
    Step PCJ45bee56da9f34d5a_TopNativeChild.machine (PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1+C10ThresholdSelectedChild.budget (gs.get i) U)
      (head 0 0) (ready (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (List.replicate U false) n i.val U)
      (head ((PCJ45bee56da9f34d5a_TopChildCursor.prefixWord gs i.val).length+(exactWord (gs.get i)).length)
        ((gs.take i.val).flatMap exactWord).length)
      (bank (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
        (DecompositionSource.Records.savedList (gs.take i.val) (PCJ45bee56da9f34d5a_TopChildCursor.afterHeaders n gs.length))
        ((gs.take i.val).flatMap exactWord) (ZeroPadding.pad U (exactWord (gs.get i))) n i.val U
        (ZeroPadding.pad U (DecompositionSource.Records.childSaved (gs.get i) []))):=by
  have first:=(PCJ45bee56da9f34d5a_TopChildCursor.run gs i.val (Nat.le_of_lt i.isLt)).embed
    (![0,0,0,0] : Fin 4→Nat) (C10ThresholdSelectedChild.extras (List.replicate U false) (List.replicate U false) U)
  let H : Fin 9→Nat:=Fin.addCases (m:=5) (n:=4) (motive:=fun _=>Nat)
    (PCJ45bee56da9f34d5a_TopChildCursor.heads (PCJ45bee56da9f34d5a_TopChildCursor.prefixWord gs i.val).length ((gs.take i.val).flatMap exactWord))
    (![0,0,0,0] : Fin 4→Nat)
  let A : Fin 9→List Bool:=Fin.addCases (m:=5) (n:=4) (motive:=fun _=>List Bool)
    (PCJ45bee56da9f34d5a_TopChildCursor.bank (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
      (DecompositionSource.Records.savedList (gs.take i.val) (PCJ45bee56da9f34d5a_TopChildCursor.afterHeaders n gs.length))
      ((gs.take i.val).flatMap exactWord) n i.val)
    (C10ThresholdSelectedChild.extras (List.replicate U false) (List.replicate U false) U)
  have cp:=C10ThresholdSelectedChild.run (gs.get i) (PCJ45bee56da9f34d5a_TopChildCursor.prefixWord gs i.val)
    ((gs.drop (i.val+1)).flatMap exactWord) (List.replicate U false) (List.replicate U false)
    U 0 (by simp) (by simp) (by omega) hg
  rw [←PCJ45bee56da9f34d5a_TopChildCursor.selected_word] at cp
  have last:=cp.dock C10ThresholdSelectedChild.selectedSlots (by decide) H A
    (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>rfl)
  have all:=(first.seq last).pad (caps U)
  refine (all.congr_in ?_ ?_).congr ?_ ?_
  · funext j;fin_cases j <;>rfl
  · funext j;fin_cases j <;>simp [caps,ready,bank,PCJ45bee56da9f34d5a_TopChildCursor.bank,C10ThresholdSelectedChild.extras,
      Fin.addCases,ZeroPadding.pad]
  · funext j;fin_cases j
    all_goals first
      | exact dockH_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 0
      | exact dockH_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 1
      | exact dockH_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 2
      | exact dockH_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 3
      | exact dockH_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 4
      | exact dockH_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 5
      | exact (dockH_other C10ThresholdSelectedChild.selectedSlots _ _ _ (by decide)).trans rfl
  · funext j;fin_cases j
    all_goals simp only [caps]
    all_goals first
      | exact (ZeroPadding.pad_zero _).trans (install_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 0)
      | exact (ZeroPadding.pad_zero _).trans (install_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 1)
      | exact (ZeroPadding.pad_zero _).trans (install_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 2)
      | exact (ZeroPadding.pad_zero _).trans (install_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 4)
      | exact (ZeroPadding.pad_zero _).trans (install_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 5)
      | exact congrArg (ZeroPadding.pad U) (install_slot C10ThresholdSelectedChild.selectedSlots (by decide) _ _ 3)
      | exact congrArg (ZeroPadding.pad U) ((install_other C10ThresholdSelectedChild.selectedSlots _ _ _ (by decide)).trans rfl)

def clearSlots : Fin 5→Fin 9:=![1,2,5,7,8]
def rewind:=PCJ45bee56da9f34d5a_HeaderRewind.machine 7
def erase:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 3)
def raise:=DecompositionCountPosition.move (fun i : Fin 9=>if i=3 ∨ i=4 then .right else .stay)
def clean:=Composition.machine (Composition.machine rewind erase) raise
def machine:=Composition.machine PCJ45bee56da9f34d5a_TopNativeChild.machine clean

theorem clean_run (source backing prior out copy : List Bool) (n index U pos : Nat)
    (hb : backing.length≤U) (hp : prior.length≤U) (hc : copy.length≤U) (hpos : pos≤U) (hu : 1≤U) :
    Step clean (4*U+11) (head pos prior.length) (bank source backing prior out n index U copy)
      (head 0 0) (ready source out n index U):=by
  let input:=bank source backing prior out n index U copy
  have first:=PCJ45bee56da9f34d5a_HeaderRewind.run 7
    (fun j : Fin 7=>(head pos prior.length) (j.castAdd 2))
    (fun j : Fin 7=>input (j.castAdd 2)) U
    (by intro j;fin_cases j <;>simp [head] <;>omega)
  have first':Step rewind (2*U+4) (head pos prior.length) input (fun _=>0) input:=by
    refine (first.congr_in ?_ ?_).congr rfl ?_
    all_goals funext j;fin_cases j <;>rfl
  let dirty : Fin 3→List Bool:=![ZeroPadding.pad U backing,ZeroPadding.pad U prior,copy]
  have hd:∀j,(dirty j).length≤U:=by
    intro j;fin_cases j <;>simp [dirty,ZeroPadding.pad_length] <;>assumption
  have second:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) dirty hd)).dock
    clearSlots (by decide) (fun _ : Fin 9=>0) input (by intro j;fin_cases j <;>rfl)
    (by intro j;fin_cases j <;>rfl)
  have second':Step erase (2*U+4) (fun _=>0) input (fun _=>0) (ready source out n index U):=by
    apply second.congr
    · exact dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
    · apply HierarchyAllocation.install_eq clearSlots (by decide)
      · intro j;fin_cases j <;>simp [ready,bank,clearSlots,ZeroPadding.pad,Fin.addCases]
      · intro j hj;fin_cases j
        all_goals first
          | rfl
          | exact False.elim (hj 0 rfl)
          | exact False.elim (hj 1 rfl)
          | exact False.elim (hj 2 rfl)
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun j : Fin 9=>if j=3 ∨ j=4 then .right else .stay) (fun _=>0) (ready source out n index U)
  have last:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
    (show _=head 0 0 by funext j;fin_cases j <;>rfl) rfl
  have all:=(first'.seq second').seq last
  simpa only [clean,raise,show ((2*U+4)+1+(2*U+4))+1+1=4*U+11 by omega] using all

theorem run {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (U : Nat)
    (hp : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length≤U) (hf : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1≤U)
    (hg : (exactWord (gs.get i)).length+2≤U) :
    Step machine (PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+C10ThresholdSelectedChild.budget (gs.get i) U+4*U+13)
      (head 0 0) (ready (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (List.replicate U false) n i.val U)
      (head 0 0) (ready (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (ZeroPadding.pad U (exactWord (gs.get i))) n i.val U):=by
  have cursor:=PCJ45bee56da9f34d5a_TopChildCursor.run gs i.val (Nat.le_of_lt i.isLt)
  have hb:=LocalSupport.step_fits cursor 1 U (by simp [PCJ45bee56da9f34d5a_TopChildCursor.bank]) (by simpa [PCJ45bee56da9f34d5a_TopChildCursor.heads] using hf)
  have hprior:=LocalSupport.step_fits cursor 2 U (by simp [PCJ45bee56da9f34d5a_TopChildCursor.bank]) (by simpa [PCJ45bee56da9f34d5a_TopChildCursor.heads] using hf)
  have hpos:(PCJ45bee56da9f34d5a_TopChildCursor.prefixWord gs i.val).length+(exactWord (gs.get i)).length≤U:=by
    have h:=hp
    rw [PCJ45bee56da9f34d5a_TopChildCursor.selected_word gs i,List.length_append,List.length_append] at h
    omega
  have hc:=C10ThresholdSelectedChild.child_saved_fit (gs.get i) U hg
  have first:=selected_run gs i U (by omega)
  have last:=clean_run (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
    (DecompositionSource.Records.savedList (gs.take i.val) (PCJ45bee56da9f34d5a_TopChildCursor.afterHeaders n gs.length))
    ((gs.take i.val).flatMap exactWord) (ZeroPadding.pad U (exactWord (gs.get i)))
    (ZeroPadding.pad U (DecompositionSource.Records.childSaved (gs.get i) [])) n i.val U _ hb hprior
    (by simpa [ZeroPadding.pad_length] using hc) hpos (by omega)
  have all:=first.seq last
  simpa only [machine,show (PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1+C10ThresholdSelectedChild.budget (gs.get i) U)+1+(4*U+11)=
    PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+C10ThresholdSelectedChild.budget (gs.get i) U+4*U+13 by omega] using all
end
end PCJ45bee56da9f34d5a_TopChildReady
