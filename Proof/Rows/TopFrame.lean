import Proof.Rows.Plan
import Proof.CaseAnalysis.RowsTouchingFrameSeek
import Proof.MachineModel.FrameCopy
import Proof.MachineModel.UInputFields

/-! Physical selection of one outer circuit payload from the framed topWord
request field. The runtime circuit index is read from its retained unary driver. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_TopFrame
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def unwrapSlots : Fin 3→Fin 8:=![0,1,2]
def seekSlots : Fin 2→Fin 8:=![1,3]
def copySlots : Fin 3→Fin 8:=![1,4,5]
def decodeSlots : Fin 3→Fin 8:=![4,6,7]
theorem copy_injective : Function.Injective copySlots:=by decide
def unwrap:=RecoveryFocus.machine unwrapSlots Streaming.machine
def seek:=RecoveryFocus.machine seekSlots CloseoutRowsTouching.FrameSeek.machine
def copy:=RecoveryFocus.machine copySlots FrameCopy.machine
def decode:=RecoveryFocus.machine decodeSlots Streaming.machine
def machine:=Composition.machine unwrap (Composition.machine seek (Composition.machine copy decode))
def heads (pos : Nat) : Fin 8→Nat:=![0,pos,0,1,0,0,0,0]
def input (source : List Bool) (index : Nat) : Fin 8→List Bool:=
  ![frame source,[],[],CompareMachine.word index,[],[],[],[]]
def bank (source : List Bool) (index : Nat) (framed log raw rawLog : List Bool) : Fin 8→List Bool:=
  ![frame source,source,List.replicate source.length false,CompareMachine.word index,framed,log,raw,rawLog]


theorem unwrap_run (source : List Bool) (index : Nat) :
    Step unwrap (4*source.length+2) (heads 0) (input source index)
      (heads 0) (bank source index [] [] [] []) :=by
  obtain ⟨r,hr,ht,hh,_⟩:=UInputFields.unwrap_ready source
  have h:=(Step.of_run hr (funext hh) ht).dock unwrapSlots (by decide)
    (heads 0) (input source index) (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply h.congr
  · funext i;fin_cases i <;>first
      | exact dockH_slot unwrapSlots (by decide) _ _ 0
      | exact dockH_slot unwrapSlots (by decide) _ _ 1
      | exact dockH_slot unwrapSlots (by decide) _ _ 2
      | exact (dockH_other unwrapSlots _ _ _ (by decide)).trans rfl
  · funext i;fin_cases i <;>first
      | exact install_slot unwrapSlots (by decide) _ _ 0
      | exact install_slot unwrapSlots (by decide) _ _ 1
      | exact install_slot unwrapSlots (by decide) _ _ 2
      | exact (install_other unwrapSlots _ _ _ (by decide)).trans rfl

theorem seek_run (words : List (List Bool)) (index B : Nat) (hi : index≤words.length)
    (hb : ∀ x∈words,x.length≤B) :
    Step seek (CloseoutRowsTouching.FrameSeek.budget B index) (heads 0)
      (bank (words.flatMap frame) index [] [] [] [])
      (heads ((words.take index).flatMap frame).length)
      (bank (words.flatMap frame) index [] [] [] []) :=by
  obtain ⟨r,hr,hf,_⟩:=CloseoutRowsTouching.FrameSeek.seek_run (words.take index) []
    ((words.drop index).flatMap frame) B (fun x hx=>hb x (List.mem_of_mem_take hx))
  have hn : (words.take index).length=index:=by simp [List.length_take,Nat.min_eq_left hi]
  have hsource : (words.take index).flatMap frame++(words.drop index).flatMap frame=
      words.flatMap frame:=by rw [←List.flatMap_append,List.take_append_drop]
  have base:=Step.of_run (p:=CloseoutRowsTouching.FrameSeek.machine) hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have raw : Step CloseoutRowsTouching.FrameSeek.machine
      (CloseoutRowsTouching.FrameSeek.budget B index) (![0,1] : Fin 2→Nat)
      ![words.flatMap frame,CompareMachine.word index]
      (![((words.take index).flatMap frame).length,1] : Fin 2→Nat)
      ![words.flatMap frame,CompareMachine.word index] :=by
    rw [hn] at base
    refine (base.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i;fin_cases i <;>
      simp [CloseoutRowsTouching.FrameSeek.entry,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,FrameSkip.cfg,Fin.addCases,
        hsource,List.take_take]
  have h:=raw.dock seekSlots (by decide) (heads 0)
    (bank (words.flatMap frame) index [] [] [] [])
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply h.congr
  · funext i;fin_cases i <;>first
      | exact dockH_slot seekSlots (by decide) _ _ 0
      | exact dockH_slot seekSlots (by decide) _ _ 1
      | exact (dockH_other seekSlots _ _ _ (by decide)).trans rfl
  · funext i;fin_cases i <;>first
      | exact install_slot seekSlots (by decide) _ _ 0
      | exact install_slot seekSlots (by decide) _ _ 1
      | exact (install_other seekSlots _ _ _ (by decide)).trans rfl

def copyHead (pre bits : List Bool):=dockH copySlots (heads pre.length)
  (![pre.length+(frame bits).length,0,0] : Fin 3→Nat)
def copyBank (source bits : List Bool) (index : Nat):=install copySlots
  (bank source index [] [] [] [])
  (![source,frame bits,List.replicate (frame bits).length false] : Fin 3→List Bool)

theorem copy_run (pre bits tail : List Bool) (index : Nat) :
    Step copy (2*(frame bits).length+2) (heads pre.length)
      (bank (pre++frame bits++tail) index [] [] [] [])
      (copyHead pre bits) (copyBank (pre++frame bits++tail) bits index) :=by
  obtain ⟨r,hr,hf,_⟩:=FrameCopy.copy_run pre bits tail
  have base : Step FrameCopy.machine (2*(frame bits).length+2)
      (![pre.length,0,0] : Fin 3→Nat) ![pre++frame bits++tail,[],[]]
      (![pre.length+(frame bits).length,0,0] : Fin 3→Nat)
      ![pre++frame bits++tail,frame bits,List.replicate (frame bits).length false] :=
    Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  exact base.dock copySlots copy_injective (heads pre.length)
    (bank (pre++frame bits++tail) index [] [] [] [])
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)

theorem decode_run (bits : List Bool) (H : Fin 8→Nat) (A : Fin 8→List Bool)
    (hh : ∀ j,H (decodeSlots j)=0)
    (ht : ∀ j,A (decodeSlots j)=(![frame bits,[],[]] : Fin 3→List Bool) j) :
    Step decode (4*bits.length+2) H A (dockH decodeSlots H (fun _=>0))
      (install decodeSlots A (![frame bits,bits,List.replicate bits.length false] : Fin 3→List Bool)) :=by
  obtain ⟨r,hr,rt,rh,_⟩:=UInputFields.unwrap_ready bits
  exact (Step.of_run hr (funext rh) rt).dock decodeSlots (by decide) H A hh ht

end
end PCJ45bee56da9f34d5a_TopFrame
