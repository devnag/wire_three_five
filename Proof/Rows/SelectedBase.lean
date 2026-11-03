import Proof.Rows.TopChildReady

/-! Actual circuit payload to canonical-base addition in one reusable bank.
The first native header supplies arity; the chosen child is copied physically,
then its magnitude is added. All worker tapes and both transient masters are
cleared, preserving the payload, runtime child driver and updated accumulator. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_SelectedBase
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
namespace Base
export PCJ45bee56da9f34d5a_CanonicalBaseInput (input heads)
export PCJ45bee56da9f34d5a_CanonicalBaseCell (words)
end Base
noncomputable section

@[simp] theorem input_zero (source : List Bool) (n w C U a : Nat) :
    Base.input source n w C U a 0=source:=ZeroPadding.pad_zero _
@[simp] theorem input_driver (source : List Bool) (n w C U a : Nat) :
    Base.input source n w C U a 54=List.replicate U true:=ZeroPadding.pad_zero _
@[simp] theorem input_log (source : List Bool) (n w C U a : Nat) :
    Base.input source n w C U a 55=List.replicate (U+1) false:=ZeroPadding.pad_zero _

def core (source arity : List Bool) (w C U a : Nat) (i : Fin 57):=
  if i=56 then arity else Base.input source 0 w C U a i
def extras (source : List Bool) (index U : Nat) (i : Fin 14):=
  if i=0 then source else if i=3 then ZeroPadding.pad U (UnaryTemplate.tape index)
  else List.replicate U false
def bank (source chosen arity : List Bool) (index w C U a : Nat) : Fin 71→List Bool:=
  Fin.addCases (m:=57) (n:=14) (motive:=fun _=>List Bool) (core chosen arity w C U a) (extras source index U)
def heads (arity : Nat) (i : Fin 71):=if i=56 then arity else if i=60 then 1 else 0

theorem core_eq (source : List Bool) (n w C U a : Nat) :
    (fun i : Fin 57=>ZeroPadding.pad (if i=56 then U else 0) (Base.input source n w C U a i))=
      core source (ZeroPadding.pad U (UnaryTemplate.tape n)) w C U a:=by
  funext i;fin_cases i <;>
    simp [core,PCJ45bee56da9f34d5a_CanonicalBaseInput.input,
      PCJ45bee56da9f34d5a_CanonicalBaseInput.ready,PCJ45bee56da9f34d5a_CanonicalBaseInput.caps,
      PCJ45bee56da9f34d5a_CanonicalBaseCell.words,NativeFanout.reusableInput,
      PCJ45bee56da9f34d5a_CellGatePalette.words,Fin.addCases,ZeroPadding.pad_zero]

def aritySlots : Fin 13→Fin 71:=![57,62,63,64,65,66,67,68,69,70,56,55,54]
def childSlots : Fin 9→Fin 71:=![57,58,59,56,60,61,0,54,55]
def wipeSlots : Fin 4→Fin 71:=![0,56,54,55]
def read:=RecoveryFocus.machine aritySlots PCJ45bee56da9f34d5a_TopArity.machine
def select:=RecoveryFocus.machine childSlots PCJ45bee56da9f34d5a_TopChildReady.machine
def evaluate:=TapeEmbedding.machine 14 PCJ45bee56da9f34d5a_CanonicalBasePrepared.machine
def lower:=DecompositionCountPosition.move (fun i : Fin 71=>if i=56 then .left else .stay)
def erase:=RecoveryFocus.machine wipeSlots (RecoveryScratchErase.resetMachine 2)
def wipe:=Composition.machine lower erase
def machine:=Composition.machine (Composition.machine (Composition.machine read select) evaluate) wipe

theorem read_run {n : Nat} (gs : List (ExactThresholdGate n)) (index w C U a : Nat)
    (hu : PCPPQueryNatural.budget n<U) :
    Step read (2*PCPPQueryNatural.budget n+4*U+10)
      (heads 0) (bank (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (List.replicate U false) (List.replicate U false) index w C U a)
      (heads 1) (bank (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (List.replicate U false)
        (ZeroPadding.pad U (UnaryTemplate.tape n)) index w C U a):=by
  let A:=bank (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (List.replicate U false) (List.replicate U false) index w C U a
  have h:=(PCJ45bee56da9f34d5a_TopArity.run n U (exactListWord gs) hu).dock aritySlots (by decide) (heads 0) A
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>first | rfl | exact ZeroPadding.pad_zero _)
  apply h.congr
  · funext i;fin_cases i
    all_goals first
      | exact dockH_slot aritySlots (by decide) _ _ 10
      | exact (dockH_other aritySlots _ _ _ (by decide)).trans rfl
      | exact dockH_slot aritySlots (by decide) _ _ 0
      | exact dockH_slot aritySlots (by decide) _ _ 1
      | exact dockH_slot aritySlots (by decide) _ _ 2
      | exact dockH_slot aritySlots (by decide) _ _ 3
      | exact dockH_slot aritySlots (by decide) _ _ 4
      | exact dockH_slot aritySlots (by decide) _ _ 5
      | exact dockH_slot aritySlots (by decide) _ _ 6
      | exact dockH_slot aritySlots (by decide) _ _ 7
      | exact dockH_slot aritySlots (by decide) _ _ 8
      | exact dockH_slot aritySlots (by decide) _ _ 9
      | exact dockH_slot aritySlots (by decide) _ _ 11
      | exact dockH_slot aritySlots (by decide) _ _ 12
  · apply HierarchyAllocation.install_eq aritySlots (by decide)
    · intro i;fin_cases i <;>first | rfl | exact ZeroPadding.pad_zero _
    · intro i hi;fin_cases i
      all_goals first
        | rfl
        | exact False.elim (hi 10 rfl)

theorem select_run {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w C U a : Nat)
    (hp : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length≤U)
    (hf : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1≤U)
    (hg : (exactWord (gs.get i)).length+2≤U) :
    Step select (PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+C10ThresholdSelectedChild.budget (gs.get i) U+4*U+13)
      (heads 1) (bank (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (List.replicate U false)
        (ZeroPadding.pad U (UnaryTemplate.tape n)) i.val w C U a)
      (heads 1) (bank (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (ZeroPadding.pad U (exactWord (gs.get i)))
        (ZeroPadding.pad U (UnaryTemplate.tape n)) i.val w C U a):=by
  let A:=bank (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (List.replicate U false)
    (ZeroPadding.pad U (UnaryTemplate.tape n)) i.val w C U a
  have h:=(PCJ45bee56da9f34d5a_TopChildReady.run gs i U hp hf hg).dock childSlots (by decide) (heads 1) A
    (by intro j;fin_cases j <;>rfl)
    (by intro j;fin_cases j <;>simp [A,bank,core,extras,childSlots,PCJ45bee56da9f34d5a_TopChildReady.ready,
      PCJ45bee56da9f34d5a_TopChildReady.bank,Fin.addCases,ZeroPadding.pad])
  apply h.congr
  · exact dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
  · apply HierarchyAllocation.install_eq childSlots (by decide)
    · intro j;fin_cases j <;>simp [bank,core,extras,childSlots,PCJ45bee56da9f34d5a_TopChildReady.ready,
        PCJ45bee56da9f34d5a_TopChildReady.bank,Fin.addCases,ZeroPadding.pad]
    · intro j hj;fin_cases j
      all_goals first
        | rfl
        | exact False.elim (hj 6 rfl)

theorem evaluate_run {n : Nat} (g : ExactThresholdGate n) (source : List Bool) (index w C D U a : Nat)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items g,natBitLength x.1.natAbs≤w)
    (hc : 8*w+12≤C) (hm : childMagnitude g<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items g) w C≤D)
    (hC : C+1≤U) (hDU : D≤U) (ha : childMagnitude g+a<2^(w+2))
    (hF : C10ThresholdChildMagnitude.budget g w C+2≤U)
    (hU : ∀ i,(Base.words (ZeroPadding.pad U (exactWord g)) (List.replicate (n+1) true)
      (n+1) w C U a i).length≤U) :
    Step evaluate (4*n+8*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+61)
      (heads 1) (bank source (ZeroPadding.pad U (exactWord g)) (ZeroPadding.pad U (UnaryTemplate.tape n)) index w C U a)
      (heads 1) (bank source (ZeroPadding.pad U (exactWord g)) (ZeroPadding.pad U (UnaryTemplate.tape n)) index w C U (childMagnitude g+a)):=by
  have base:=PCJ45bee56da9f34d5a_CanonicalBasePrepared.run g
    (List.replicate (U-(exactWord g).length) false) w C D U a hw hc hm hD hC hDU ha hF hU
  have padded:=base.pad (fun i : Fin 57=>if i=56 then U else 0)
  rw [core_eq,core_eq] at padded
  have h:=padded.embed (fun j : Fin 14=>if j=3 then 1 else 0) (extras source index U)
  refine (h.congr_in ?_ rfl).congr ?_ rfl
  all_goals funext j;fin_cases j <;>rfl

theorem wipe_run (source chosen arity : List Bool) (index w C U a : Nat)
    (hc : chosen.length≤U) (ha : arity.length≤U) :
    Step wipe (2*U+6) (heads 1) (bank source chosen arity index w C U a)
      (heads 0) (bank source (List.replicate U false) (List.replicate U false) index w C U a):=by
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun j : Fin 71=>if j=56 then .left else .stay) (heads 1) (bank source chosen arity index w C U a)
  have first:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
    (show _=heads 0 by funext j;by_cases h56:j=56 <;>by_cases h60:j=60 <;>simp [heads,h56,h60,HeadMove.apply]) rfl
  let dirty : Fin 2→List Bool:=![chosen,arity]
  have h:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) dirty
    (by intro j;fin_cases j <;>assumption))).dock wipeSlots (by decide) (heads 0)
    (bank source chosen arity index w C U a)
    (by intro j;fin_cases j <;>rfl)
    (by intro j;fin_cases j <;>first | rfl | exact ZeroPadding.pad_zero _)
  have last:Step erase (2*U+4) (heads 0) (bank source chosen arity index w C U a)
      (heads 0) (bank source (List.replicate U false) (List.replicate U false) index w C U a):=by
    apply h.congr
    · exact dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
    · apply HierarchyAllocation.install_eq wipeSlots (by decide)
      · intro j;fin_cases j <;>first
          | exact ZeroPadding.pad_zero _
          | simp only [Nat.max_self];first | rfl | exact ZeroPadding.pad_zero _
      · intro j hj;fin_cases j
        all_goals first
          | rfl
          | exact False.elim (hj 0 rfl)
          | exact False.elim (hj 1 rfl)
  have all:=first.seq last
  simpa only [wipe,lower,show 1+1+(2*U+4)=2*U+6 by omega] using all

end
end PCJ45bee56da9f34d5a_SelectedBase
