import Proof.SourceAssembly.SourceLiveMin
import Proof.CaseAnalysis.ScheduleClog

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceLog
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding RepairSource.CloseoutSchedule
noncomputable section

theorem clock_step {t s F : Nat} {p : Machine t s} {I O : Fin t→List Bool}
    (h : ClockJoin.ReadyRun p F I O) : Step p F (fun _=>0) I (fun _=>0) O := by
  obtain ⟨r,hr,rt,rh,rs⟩:=h
  exact ⟨r,hr,funext rh,rt,rs⟩

theorem dock_zero {t u s F : Nat} {p : Machine t s} {I O : Fin t→List Bool}
    (h : Step p F (fun _=>0) I (fun _=>0) O) (slots : Fin t→Fin u)
    (hi : Function.Injective slots) (A : Fin u→List Bool) (ha : ∀i,A (slots i)=I i) :
    Step (RecoveryFocus.machine slots p) F (fun _=>0) A (fun _=>0) (install slots A O) := by
  have hz : dockH slots (fun _=>0) (fun _=>0)=(fun _ : Fin u=>0) := by
    funext i;cases hp:RecoveryFocus.pick slots i <;>simp [dockH,hp]
  exact (h.dock slots hi (fun _=>0) A (fun _=>rfl) ha).congr hz rfl

theorem install_blank {t u cut old : Nat} (slots : Fin t→Fin u) (A : Fin u→List Bool)
    (O : Fin t→List Bool) (ho:old≤cut) (hs:∀j,(slots j).val<cut)
    (ha:∀i,old≤ i.val→A i=[]) : ∀i,cut≤ i.val→install slots A O i=[] := by
  intro i hi
  rw [install_other slots A O i (by intro j he;have hj:=hs j;rw [he] at hj;omega)]
  exact ha i (ho.trans hi)

def oneSlots : Fin 3→Fin 16:=![0,1,2]
def twoSlots : Fin 3→Fin 16:=![1,3,4]
def logSlots (i : Fin 12) : Fin 16:=if i=0 then 3 else ⟨i.val+4,by omega⟩
theorem log_inj : Function.Injective logSlots:=by decide

def one:=RecoveryFocus.machine oneSlots (UWalkUnary.machine true true)
def two:=RecoveryFocus.machine twoSlots (UWalkUnary.machine false true)
def last:=RecoveryFocus.machine logSlots Clog.machine
def machine:=Composition.machine (Composition.machine one two) last
def input (q : Nat) (i : Fin 16):=if i=0 then CompareMachine.word q else []
def budget (q : Nat):=(2*q+6)+1+(2*(q+1)+6)+1+Clog.budget (q+2)

theorem run (q : Nat) : ∃ A,Step machine (budget q) (fun _=>0) (input q) (fun _=>0) A ∧
    A 0=CompareMachine.word q ∧A 14=CompareMachine.word (Nat.clog 2 (q+2)) := by
  have h1:=clock_step (UWalkUnary.ready true true 0 q)
  have first:=dock_zero h1 oneSlots (by decide) (input q) (by
    intro i;fin_cases i <;>simp [oneSlots,input,UWalkUnary.input,UWalkUnary.source,ZeroPadding.pad_zero])
  let A1:=install oneSlots (input q) (UWalkUnary.result true true 0 q)
  have blank1 : ∀i : Fin 16,3≤ i.val→A1 i=[] :=
    install_blank oneSlots (input q) _ (old:=1) (by omega) (by decide)
      (by intro i hi;have hn:i≠0:=by intro h;subst i;contradiction
          simp only [input,if_neg hn])
  have h2:=clock_step (UWalkUnary.ready false true 0 (q+1))
  have second:=dock_zero h2 twoSlots (by decide) A1 (by
    intro i;fin_cases i
    · change A1 (oneSlots 1)=_
      dsimp only [A1]
      rw [install_slot oneSlots (by decide)]
      simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.input,UWalkUnary.source,ZeroPadding.pad_zero,CompareMachine.word]
    · exact blank1 3 (by decide)
    · exact blank1 4 (by decide))
  let A2:=install twoSlots A1 (UWalkUnary.result false true 0 (q+1))
  have blank2 : ∀i : Fin 16,5≤ i.val→A2 i=[] :=
    install_blank twoSlots A1 _ (old:=3) (by omega) (by decide) blank1
  obtain ⟨B,hb,hlog⟩:=Clog.clog_run (q+2) (by omega)
  have third:=dock_zero (clock_step hb) logSlots log_inj A2 (by
    intro i;by_cases hi:i=0
    · subst i
      change A2 (twoSlots 1)=_
      dsimp only [A2]
      rw [install_slot twoSlots (by decide)]
      simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,Clog.input,Nat.add_assoc]
    · have hl : 5≤(logSlots i).val:=by simp only [logSlots,hi,if_false,Fin.val_mk];have:=i.isLt;omega
      rw [blank2 _ hl]
      simp [Clog.input,hi])
  refine ⟨_,(first.seq second).seq third,?_,?_⟩
  · rw [install_other logSlots A2 B 0 (by intro j;unfold logSlots;split_ifs <;>intro h <;>have hv:=congrArg Fin.val h <;>simp at hv)]
    change install twoSlots A1 _ 0=_
    rw [install_other twoSlots A1 _ 0 (by decide)]
    have h:=install_slot oneSlots (by decide) (input q) (UWalkUnary.result true true 0 q) 0
    change A1 0=UWalkUnary.source 0 q at h
    simpa only [UWalkUnary.source,ZeroPadding.pad_zero] using h
  · exact (install_slot logSlots log_inj A2 B 10).trans hlog

end
end PCJ6e421fabe2aa4155_SourceLog
