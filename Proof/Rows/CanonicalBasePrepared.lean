import Proof.Rows.CanonicalBaseInput
import Proof.Rows.CanonicalBaseReentry

/-! A complete base update with paid mask/count production and cleanup.
Only the source, arity and width/cap masters are supplied; both the 44 worker
tapes and the two magnitude mask/count tapes return to their exact cold state. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CanonicalBasePrepared
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open PCJ45bee56da9f34d5a_CanonicalBaseInput
noncomputable section

def wipeSlots : Fin 4→Fin 57:=![1,5,54,55]
def wipe:=RecoveryFocus.machine wipeSlots (RecoveryScratchErase.resetMachine 2)
def evaluate:=TapeEmbedding.machine 1 PCJ45bee56da9f34d5a_CanonicalBaseReentry.machine
def machine:=Composition.machine (Composition.machine (Composition.machine prepare retreat) evaluate) wipe

theorem wipe_run (source : List Bool) (n w C U a : Nat) (hn : n+2≤U) :
    Step wipe (2*U+4) (heads 0) (ready source n w C U a)
      (heads 0) (input source n w C U a):=by
  let dirty : Fin 2→List Bool:=![ZeroPadding.pad U (List.replicate (n+1) true),
    ZeroPadding.pad U (CompareMachine.word (n+1))]
  have hd : ∀ i,(dirty i).length≤U:=by
    intro i;fin_cases i <;>simp [dirty,ZeroPadding.pad_length,CompareMachine.word] <;>omega
  have h:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) dirty hd)).dock
    wipeSlots (by decide) (heads 0) (ready source n w C U a)
    (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>first | rfl | exact ZeroPadding.pad_zero _)
  apply h.congr
  · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
  · apply HierarchyAllocation.install_eq wipeSlots (by decide)
    · intro i;fin_cases i <;>simp only [Nat.max_self]
      all_goals first
        | rfl
        | exact ZeroPadding.pad_zero _
    · intro i hi
      have h1:i≠1:=fun h=>hi 0 h.symm
      have h5:i≠5:=fun h=>hi 1 h.symm
      simp only [input,h1,h5,or_self,if_false]

theorem run {n : Nat} (g : ExactThresholdGate n) (tail : List Bool) (w C D U a : Nat)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items g,natBitLength x.1.natAbs≤w)
    (hc : 8*w+12≤C) (hm : childMagnitude g<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items g) w C≤D)
    (hC : C+1≤U) (hDU : D≤U) (ha : childMagnitude g+a<2^(w+2))
    (hF : C10ThresholdChildMagnitude.budget g w C+2≤U)
    (hU : ∀ i,(Base.words (exactWord g++tail) (List.replicate (n+1) true)
      (n+1) w C U a i).length≤U) :
    Step machine (4*n+8*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+61)
      (heads 0) (input (exactWord g++tail) n w C U a)
      (heads 0) (input (exactWord g++tail) n w C U (childMagnitude g+a)):=by
  have hn : n+2≤U:=by
    have h:=hU 5
    change (CompareMachine.word (n+1)).length≤U at h
    simp [CompareMachine.word] at h
    omega
  have first:=prepare_run (exactWord g++tail) n w C U a (by omega)
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 57=>if i=5 then .left else .stay) (heads 1) (ready (exactWord g++tail) n w C U a)
  have second:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
    (show _=heads 0 by funext i;by_cases h5:i=5 <;>by_cases h56:i=56 <;>simp [heads,h5,h56,HeadMove.apply]) rfl
  have body:=PCJ45bee56da9f34d5a_CanonicalBaseReentry.run g tail w C D U a hw hc hm hD hC hDU ha hF
    (by simpa only [items_count,items_mask] using hU)
  rw [items_count,items_mask] at body
  have last:=(body.pad (caps U)).embed (fun _ : Fin 1=>1) (fun _ : Fin 1=>UnaryTemplate.tape n)
  have last':Step evaluate (6*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+36)
      (heads 0) (ready (exactWord g++tail) n w C U a)
      (heads 0) (ready (exactWord g++tail) n w C U (childMagnitude g+a)):=by
    refine (last.congr_in ?_ rfl).congr ?_ rfl
    all_goals funext i;fin_cases i <;>rfl
  have all:=((first.seq second).seq last').seq (wipe_run (exactWord g++tail) n w C U (childMagnitude g+a) hn)
  simpa only [machine,retreat,show (((4*n+17)+1+1)+1+(6*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+36))+1+(2*U+4)=
    4*n+8*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+61 by omega] using all
end
end PCJ45bee56da9f34d5a_CanonicalBasePrepared
