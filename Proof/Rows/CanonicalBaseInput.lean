import Proof.Rows.CanonicalBaseCell
import Proof.Rows.FinalThresholdMagnitudeMask

/-! The all-true magnitude mask and field count are produced from the actual
retained arity, on padded reusable tapes, before the canonical-base update. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CanonicalBaseInput
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
noncomputable section
namespace Base
export PCJ45bee56da9f34d5a_CanonicalBaseCell (words run machine)
end Base

def caps (U : Nat) (i : Fin 56) : Nat:=if i=1 ∨ i=5 then U else 0
def ready (source : List Bool) (n w C U a : Nat) : Fin 57→List Bool:=
  Fin.addCases (m:=56) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps U i) (NativeFanout.reusableInput (m:=44)
      (Base.words source (List.replicate (n+1) true) (n+1) w C U a) U i))
    (fun _ : Fin 1=>UnaryTemplate.tape n)
def input (source : List Bool) (n w C U a : Nat) : Fin 57→List Bool:=fun i=>
  if i=1 ∨ i=5 then List.replicate U false else ready source n w C U a i
def heads (count : Nat) : Fin 57→Nat:=fun i=>if i=56 then 1 else if i=5 then count else 0
def slots : Fin 4→Fin 57:=![56,1,5,55]
def prepare:=RecoveryFocus.machine slots C10ThresholdMagnitudeMask.machine
def retreat:=DecompositionCountPosition.move (fun i : Fin 57=>if i=5 then .left else .stay)
def evaluate:=TapeEmbedding.machine 1 Base.machine
def machine:=Composition.machine (Composition.machine prepare retreat) evaluate

theorem prepare_run (source : List Bool) (n w C U a : Nat) (hn : n+1≤U) :
    Step prepare (4*n+17) (heads 0) (input source n w C U a)
      (heads 1) (ready source n w C U a):=by
  have first:=(C10ThresholdMagnitudeMask.mask_count_run n (U+1) (by omega)).pad
    (![0,U,U,0] : Fin 4→Nat)
  have h:=first.dock slots (by decide) (heads 0) (input source n w C U a)
    (by intro i;fin_cases i <;>rfl)
    (by
      intro i;fin_cases i
      · exact (ZeroPadding.pad_zero _).symm
      · simp only [ZeroPadding.pad];rfl
      · simp only [ZeroPadding.pad];rfl
      · rfl)
  apply h.congr
  · funext i
    by_cases hi:∃j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [dockH_slot slots (by decide)]
      fin_cases j <;>rfl
    · rw [dockH_other slots _ _ _ (by simpa using hi)]
      have h5:i≠5:=fun h=>hi ⟨2,h.symm⟩
      simp only [heads,h5,if_false]
  · apply HierarchyAllocation.install_eq slots (by decide)
    · intro i;fin_cases i <;>first |rfl |exact (ZeroPadding.pad_zero _).symm
    · intro i hi
      have h1:i≠1:=fun h=>hi 1 h.symm
      have h5:i≠5:=fun h=>hi 2 h.symm
      simp only [input,h1,h5,or_self,if_false]

theorem items_count {n : Nat} (g : ExactThresholdGate n) :
    (C10ThresholdChildMagnitude.items g).length=n+1:=by
  simp [C10ThresholdChildMagnitude.fields,C10ThresholdChildMagnitude.items]
theorem items_mask {n : Nat} (g : ExactThresholdGate n) :
    CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g)=List.replicate (n+1) true:=by
  simp [C10ThresholdChildMagnitude.fields,C10ThresholdChildMagnitude.items,CloseoutRowsPoolWeight.mask,Function.comp_def]

theorem run {n : Nat} (g : ExactThresholdGate n) (tail : List Bool) (w C D U a : Nat)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items g,natBitLength x.1.natAbs≤w)
    (hc : 8*w+12≤C) (hm : childMagnitude g<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items g) w C≤D)
    (hC : C+1≤U) (hDU : D≤U) (ha : childMagnitude g+a<2^(w+2)) (hn : n+1≤U)
    (hU : ∀ i,(Base.words (exactWord g++tail) (List.replicate (n+1) true)
      (n+1) w C U a i).length≤U) :
    ∃ H A,Step machine
      (4*n+2*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+46)
      (heads 0) (input (exactWord g++tail) n w C U a) H A ∧
      H 9=0 ∧ A 9=MatrixScoreWeight.scalar U (w+2) (childMagnitude g+a):=by
  have first:=prepare_run (exactWord g++tail) n w C U a hn
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 57=>if i=5 then .left else .stay) (heads 1) (ready (exactWord g++tail) n w C U a)
  have second:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
    (show _=heads 0 by
      funext i;by_cases h5:i=5 <;>by_cases h56:i=56 <;>simp [heads,h5,h56,HeadMove.apply]) rfl
  have hb:=Base.run g tail w C D U a hw hc hm hD hC hDU ha
    (by simpa only [items_count,items_mask] using hU)
  obtain ⟨H,A,body,hhead,hvalue⟩:=hb
  rw [items_count,items_mask] at body
  have last:=(body.pad (caps U)).embed (fun _ : Fin 1=>1) (fun _ : Fin 1=>UnaryTemplate.tape n)
  have last':=last.congr_in
    (show _=heads 0 by funext i;fin_cases i <;>rfl)
    (show _=ready (exactWord g++tail) n w C U a by rfl)
  have all:=(first.seq second).seq last'
  rw [show ((4*n+17)+1+1)+1+(2*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+26)=
    4*n+2*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+46 by omega] at all
  refine ⟨_,_,all,?_,?_⟩
  · exact hhead
  · change ZeroPadding.pad 0 (A 9)=_
    simpa only [ZeroPadding.pad_zero] using hvalue

end
end PCJ45bee56da9f34d5a_CanonicalBaseInput
