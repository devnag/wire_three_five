import Proof.SourceAssembly.SourcePoolPreparation
import Proof.SourceAssembly.SourcePoolHeader
import Proof.SourceAssembly.SourcePoolBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolMasters
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open PCJ6e421fabe2aa4155_SourceLog (dock_zero)
noncomputable section

def extra {q : Nat} (live : Finset (Fin q)) (N : Nat) (source : List Bool) (i : Fin 22) : List Bool:=
  if i=0 then CompareMachine.word N else if i=1 then CloseoutRowsGateSupport.gateMembers live else if i=2 then source else []
def input {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) : Fin 84→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (PCJ6e421fabe2aa4155_SourcePoolPreparation.input q B) (extra live N source)
def headerSlots (i : Fin 20) : Fin 84:=if i=0 then 62 else ⟨i.val+64,by omega⟩
theorem header_inj : Function.Injective headerSlots:=by decide
def fields : Fin 9→Fin 84:=![8,39,63,36,0,17,64,82,62]
def first:=TapeEmbedding.machine 22 PCJ6e421fabe2aa4155_SourcePoolPreparation.machine
def last:=RecoveryFocus.machine headerSlots PCJ6e421fabe2aa4155_SourcePoolHeader.machine
def machine:=Composition.machine first last
def budget (B q N : Nat):=PCJ6e421fabe2aa4155_SourcePoolPreparation.budget q B+1+
  PCJ6e421fabe2aa4155_SourcePoolHeader.budget N

theorem run {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) :
    ∃ A,Step machine (budget B q N) (fun _=>0) (input live B N source) (fun _=>0) A ∧
      (∀i,A (fields i)=PCJ6e421fabe2aa4155_SourcePoolBank.data live B N source i) ∧
      A 51=List.replicate (PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q) true := by
  obtain ⟨D,hd,d0,_d1,_d6,d8,d36,d39,d17,d51⟩:=PCJ6e421fabe2aa4155_SourcePoolPreparation.run q B
  let A0 : Fin 84→List Bool:=Fin.addCases (motive:=fun _=>List Bool) D (extra live N source)
  have hz:(Fin.addCases (motive:=fun _ : Fin 84=>Nat) (fun _ : Fin 62=>0) (fun _ : Fin 22=>0))=(fun _=>0):=by
    funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]
  have hfirst:Step first _ (fun _=>0) (input live B N source) (fun _=>0) A0:=
    ((hd.embed (fun _ : Fin 22=>0) (extra live N source)).congr_in hz rfl).congr hz rfl
  obtain ⟨H,hh,h0,h18⟩:=PCJ6e421fabe2aa4155_SourcePoolHeader.run N
  have selected:∀i,A0 (headerSlots i)=PCJ6e421fabe2aa4155_SourcePoolHeader.input N i:=by
    intro i;by_cases hi:i=0
    · subst i;rfl
    rw [headerSlots,if_neg hi]
    have he:(⟨i.val+64,by omega⟩ : Fin 84)=(⟨i.val+2,by omega⟩ : Fin 22).natAdd 62:=Fin.ext (by simp;omega)
    rw [he]
    simp only [A0,Fin.addCases_right]
    have hn:i.val≠0:=by intro h;exact hi (Fin.ext h)
    have h0':(⟨i.val+2,by omega⟩ : Fin 22)≠0:=by intro h;have hv:=congrArg Fin.val h;dsimp at hv;omega
    have h1':(⟨i.val+2,by omega⟩ : Fin 22)≠1:=by intro h;have hv:=congrArg Fin.val h;dsimp at hv;omega
    have h2':(⟨i.val+2,by omega⟩ : Fin 22)≠2:=by intro h;have hv:=congrArg Fin.val h;dsimp at hv;omega
    simp only [extra,if_neg h0',if_neg h1',if_neg h2',PCJ6e421fabe2aa4155_SourcePoolHeader.input,if_neg hi]
  have hlast:=dock_zero hh headerSlots header_inj A0 selected
  refine ⟨_,hfirst.seq hlast,?_,?_⟩
  · intro i;fin_cases i
    · exact (install_other headerSlots A0 H 8 (by decide)).trans d8
    · exact (install_other headerSlots A0 H 39 (by decide)).trans d39
    · exact install_other headerSlots A0 H 63 (by decide)
    · exact (install_other headerSlots A0 H 36 (by decide)).trans d36
    · exact (install_other headerSlots A0 H 0 (by decide)).trans d0
    · exact (install_other headerSlots A0 H 17 (by decide)).trans d17
    · exact install_other headerSlots A0 H 64 (by decide)
    · exact (install_slot headerSlots header_inj A0 H 18).trans h18
    · exact (install_slot headerSlots header_inj A0 H 0).trans h0
  · exact (install_other headerSlots A0 H 51 (by decide)).trans d51

end
end PCJ6e421fabe2aa4155_SourcePoolMasters
