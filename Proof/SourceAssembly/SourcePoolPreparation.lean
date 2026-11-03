import Proof.SourceAssembly.SourcePoolScalars
import Proof.SourceAssembly.SourcePoolCapacity
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolPreparation
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open PCJ6e421fabe2aa4155_SourceLog (clock_step dock_zero install_blank)
noncomputable section
local instance : NeZero (DimensionPolynomial.tapes 3):=⟨by decide⟩

def scalarSlots (i : Fin 14) : Fin 62:=if i=0 then 6 else if i=1 then 8 else ⟨28+i.val,by omega⟩
-- The input dimension is20; the unused slot42 remains blank.
def powerSlots (i : Fin (DimensionPolynomial.tapes 3)) : Fin 62:=if i=0 then 4 else ⟨42+i.val,by have hi:i.val<20:=i.isLt;omega⟩
theorem scalar_inj : Function.Injective scalarSlots:=by decide
theorem power_inj : Function.Injective powerSlots:=by decide

def first:=TapeEmbedding.machine 34 PCJ6e421fabe2aa4155_SourcePoolDrivers.machine
def scalars:=RecoveryFocus.machine scalarSlots PCJ6e421fabe2aa4155_SourcePoolScalars.machine
def power:=RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 3 16777216)
def machine:=Composition.machine (Composition.machine first scalars) power
def input (q B : Nat) : Fin 62→List Bool:=Fin.addCases (motive:=fun _=>List Bool)
  (PCJ6e421fabe2aa4155_SourcePoolDrivers.input q B) (fun _ : Fin 34=>[])
def budget (q B : Nat):=PCJ6e421fabe2aa4155_SourcePoolDrivers.budget q B+1+
  PCJ6e421fabe2aa4155_SourcePoolScalars.budget (B+q+1)+1+
  PCPSerializerCapacity.Power.budget 3 16777216 (B+q)

theorem run (q B : Nat) : ∃ A,Step machine (budget q B) (fun _=>0) (input q B) (fun _=>0) A ∧
    A 0=CompareMachine.word q ∧A 1=List.replicate B true ∧
    A 6=UnaryTemplate.tape (B+q+1) ∧A 8=List.replicate (B+q+1) true ∧
    A 36=List.replicate (8*(B+q+1)+12) true ∧
    A 39=frame (SignedSortKey.binary (B+q+1) 0) ∧
    A 17=List.replicate (65536*(B+q+(B+q+1)+1)^2) true ∧
    A 51=List.replicate (PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q) true := by
  obtain ⟨D,hd,d0,d1,d4,d6,d8,d17⟩:=PCJ6e421fabe2aa4155_SourcePoolDrivers.run q B
  let A1 : Fin 62→List Bool:=Fin.addCases (motive:=fun _=>List Bool) D (fun _ : Fin 34=>[])
  have hf:Step first _ (fun _=>0) (input q B) (fun _=>0) A1:=
    (hd.embed (fun _ : Fin 34=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl |>.congr
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have blank1 : ∀i : Fin 62,28≤ i.val→A1 i=[] := by
    intro i hi
    have he:i=(⟨i.val-28,by omega⟩ : Fin 34).natAdd 28:=Fin.ext (by simp;omega)
    rw [he]
    change Fin.addCases (motive:=fun _=>List Bool) D (fun _ : Fin 34=>[]) _=[]
    rw [Fin.addCases_right]
  obtain ⟨S,hs,s0,s1,s8,s11⟩:=PCJ6e421fabe2aa4155_SourcePoolScalars.run (B+q+1)
  have selected:∀i,A1 (scalarSlots i)=PCJ6e421fabe2aa4155_SourcePoolScalars.input (B+q+1) i := by
    intro i;by_cases h0:i=0
    · subst i;exact d6
    by_cases h1:i=1
    · subst i;exact d8
    rw [scalarSlots,if_neg h0,if_neg h1,blank1 _ (by simp)]
    simp only [PCJ6e421fabe2aa4155_SourcePoolScalars.input,if_neg h0,if_neg h1]
  have hs':=dock_zero hs scalarSlots scalar_inj A1 selected
  let A2:=install scalarSlots A1 S
  have blank2 : ∀i : Fin 62,42≤ i.val→A2 i=[]:=install_blank scalarSlots A1 S (old:=28) (by omega) (by decide) blank1
  obtain ⟨P,hp,_p0,pv⟩:=PCPSerializerCapacity.Power.capacity_run 3 16777216 (B+q)
  have hp':=dock_zero (clock_step hp) powerSlots power_inj A2 (by
    intro i;by_cases hi:i=0
    · subst i
      exact (install_other scalarSlots A1 S 4 (by decide)).trans d4
    · have hv:i.val≠0:=by intro he;exact hi (Fin.ext he)
      rw [powerSlots,if_neg hi,blank2 _ (by change 42≤42+i.val;omega)]
      simp only [DimensionPolynomial.input,hv,if_false])
  refine ⟨_,(hf.seq hs').seq hp',?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other powerSlots A2 P 0 (by decide)).trans ((install_other scalarSlots A1 S 0 (by decide)).trans d0)
  · exact (install_other powerSlots A2 P 1 (by decide)).trans ((install_other scalarSlots A1 S 1 (by decide)).trans d1)
  · exact (install_other powerSlots A2 P 6 (by decide)).trans ((install_slot scalarSlots scalar_inj A1 S 0).trans s0)
  · exact (install_other powerSlots A2 P 8 (by decide)).trans ((install_slot scalarSlots scalar_inj A1 S 1).trans s1)
  · exact (install_other powerSlots A2 P 36 (by decide)).trans ((install_slot scalarSlots scalar_inj A1 S 8).trans s8)
  · exact (install_other powerSlots A2 P 39 (by decide)).trans ((install_slot scalarSlots scalar_inj A1 S 11).trans s11)
  · exact (install_other powerSlots A2 P 17 (by decide)).trans ((install_other scalarSlots A1 S 17 (by decide)).trans d17)
  · exact (install_slot powerSlots power_inj A2 P (PCPSerializerCapacity.Power.outputSlot 3)).trans pv

end
end PCJ6e421fabe2aa4155_SourcePoolPreparation
