import Proof.MachineModel.NativeFanout
import Proof.SourceAssembly.SourceBundle
import Proof.SourceAssembly.SourceCircuitFrame
import Proof.SourceAssembly.SourceLiteralRefs
import Proof.SourceAssembly.SourceLiveCount
import Proof.SourceAssembly.SourceReuse
import Proof.SourceAssembly.SourceSingletonRequest
import Proof.SourceAssembly.SourceTopNative
import Proof.PCP.PCPSerializerCapacityPower
import Proof.MachineModel.ClockUnarySum

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolDrivers
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open PCJ6e421fabe2aa4155_SourceLog (clock_step dock_zero install_blank)
noncomputable section
local instance : NeZero (DimensionPolynomial.tapes 2):=⟨by decide⟩

def qSlots : Fin 3→Fin 28:=![0,2,3]
def sumSlots : Fin 4→Fin 28:=![1,2,4,5]
def templateSlots : Fin 3→Fin 28:=![4,6,7]
def widthSlots : Fin 3→Fin 28:=![6,8,9]
def powerSlots (i : Fin (DimensionPolynomial.tapes 2)) : Fin 28:=if i=0 then 4 else ⟨10+i.val,by have hi:i.val<18:=i.isLt;omega⟩
theorem power_inj : Function.Injective powerSlots:=by decide

def first:=RecoveryFocus.machine qSlots (UWalkUnary.machine false false)
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine true)
def width:=RecoveryFocus.machine widthSlots (UWalkUnary.machine false false)
def power:=RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 2 262144)
def machine:=Composition.machine (Composition.machine (Composition.machine (Composition.machine first sum) template) width) power
def input (q B : Nat) (i : Fin 28) : List Bool:=if i=0 then CompareMachine.word q else if i=1 then List.replicate B true else []
def budget (q B : Nat):=(2*q+6)+1+(2*(B+q)+6)+1+(2*(B+q)+8)+1+(2*(B+q+1)+6)+1+PCPSerializerCapacity.Power.budget 2 262144 (B+q)

theorem run (q B : Nat) : ∃ A,Step machine (budget q B) (fun _=>0) (input q B) (fun _=>0) A ∧
    A 0=CompareMachine.word q ∧A 1=List.replicate B true ∧
    A 4=List.replicate (B+q) true ∧A 6=UnaryTemplate.tape (B+q+1) ∧
    A 8=List.replicate (B+q+1) true ∧A 17=List.replicate (65536*(B+q+(B+q+1)+1)^2) true := by
  have hq:=dock_zero (clock_step (UWalkUnary.ready false false 0 q)) qSlots (by decide) (input q B) (by
    intro i;fin_cases i <;>simp [qSlots,input,UWalkUnary.input,UWalkUnary.source,ZeroPadding.pad_zero])
  let A1:=install qSlots (input q B) (UWalkUnary.result false false 0 q)
  have fresh1 : ∀i : Fin 28,4≤ i.val→A1 i=[]:=
    install_blank qSlots (input q B) _ (old:=2) (by omega) (by decide)
      (by intro i hi;have h0:i≠0:=by intro he;subst i;contradiction
          have h1:i≠1:=by intro he;subst i;contradiction
          simp only [input,if_neg h0,if_neg h1])
  have hq0:A1 0=CompareMachine.word q:=by
    have h:=install_slot qSlots (by decide) (input q B) (UWalkUnary.result false false 0 q) 0
    change A1 0=UWalkUnary.source 0 q at h
    simpa only [UWalkUnary.source,ZeroPadding.pad_zero] using h
  have hB1:A1 1=List.replicate B true:=(install_other qSlots _ _ 1 (by decide)).trans (by simp [input])
  have hs:=dock_zero (clock_step (ClockUnarySum.sum_ready B q)) sumSlots (by decide) A1 (by
    intro i;fin_cases i
    · exact hB1
    · change A1 2=List.replicate q true
      have h:=install_slot qSlots (by decide) (input q B) (UWalkUnary.result false false 0 q) 1
      change A1 2=UWalkUnary.output false false q at h
      simpa only [UWalkUnary.output,UWalkUnary.lead,Bool.toNat_false,Nat.add_zero,Bool.false_eq_true,if_false,List.nil_append] using h
    · exact fresh1 4 (by decide)
    · exact fresh1 5 (by decide))
  let A2:=install sumSlots A1 (![List.replicate B true,List.replicate q true,List.replicate (B+q) true,List.replicate (B+q+2) false])
  have fresh2 : ∀i : Fin 28,6≤ i.val→A2 i=[]:=install_blank sumSlots A1 _ (old:=4) (by omega) (by decide) fresh1
  have ht:=dock_zero (clock_step (DimensionTemplate.ready true (B+q))) templateSlots (by decide) A2 (by
    intro i;fin_cases i
    · exact install_slot sumSlots (by decide) A1 _ 2
    · exact fresh2 6 (by decide)
    · exact fresh2 7 (by decide))
  let A3:=install templateSlots A2 (DimensionTemplate.output true (B+q))
  have fresh3 : ∀i : Fin 28,8≤ i.val→A3 i=[]:=install_blank templateSlots A2 _ (old:=6) (by omega) (by decide) fresh2
  have h6:A3 6=UnaryTemplate.tape (B+q+1):=install_slot templateSlots (by decide) A2 _ 1
  have hw:=dock_zero (clock_step (UWalkUnary.ready false false (B+q+1+2) (B+q+1))) widthSlots (by decide) A3 (by
    intro i;fin_cases i
    · change A3 6=UWalkUnary.source (B+q+1+2) (B+q+1)
      rw [h6,PCJ6e421fabe2aa4155_SourceLiveCount.unary_pad]
      rfl
    · exact fresh3 8 (by decide)
    · exact fresh3 9 (by decide))
  let A4:=install widthSlots A3 (UWalkUnary.result false false (B+q+1+2) (B+q+1))
  have fresh4 : ∀i : Fin 28,10≤ i.val→A4 i=[]:=install_blank widthSlots A3 _ (old:=8) (by omega) (by decide) fresh3
  have h4:A4 4=List.replicate (B+q) true:=
    (install_other widthSlots A3 _ 4 (by decide)).trans (install_slot templateSlots (by decide) A2 _ 0)
  obtain ⟨P,hp,p0,pout⟩:=PCPSerializerCapacity.Power.capacity_run 2 262144 (B+q)
  have hp':=dock_zero (clock_step hp) powerSlots power_inj A4 (by
    intro i;by_cases hi:i=0
    · subst i;exact h4
    · have hv:i.val≠0:=by intro he;exact hi (Fin.ext he)
      rw [powerSlots,if_neg hi,fresh4 _ (by change 10≤10+i.val;omega)]
      simp only [DimensionPolynomial.input,hv,if_false])
  refine ⟨_,(((hq.seq hs).seq ht).seq hw).seq hp',?_,?_,?_,?_,?_,?_⟩
  · rw [install_other powerSlots A4 P 0 (by decide)]
    exact (install_other widthSlots A3 _ 0 (by decide)).trans
      ((install_other templateSlots A2 _ 0 (by decide)).trans
        ((install_other sumSlots A1 _ 0 (by decide)).trans hq0))
  · rw [install_other powerSlots A4 P 1 (by decide)]
    exact (install_other widthSlots A3 _ 1 (by decide)).trans
      ((install_other templateSlots A2 _ 1 (by decide)).trans
        (install_slot sumSlots (by decide) A1 _ 0))
  · exact (install_slot powerSlots power_inj A4 P 0).trans p0
  · rw [install_other powerSlots A4 P 6 (by decide)]
    have h:=install_slot widthSlots (by decide) A3 (UWalkUnary.result false false (B+q+1+2) (B+q+1)) 0
    change A4 6=UWalkUnary.source (B+q+1+2) (B+q+1) at h
    simpa only [UWalkUnary.source,PCJ6e421fabe2aa4155_SourceLiveCount.unary_pad] using h
  · rw [install_other powerSlots A4 P 8 (by decide)]
    have h:=install_slot widthSlots (by decide) A3 (UWalkUnary.result false false (B+q+1+2) (B+q+1)) 1
    change A4 8=UWalkUnary.output false false (B+q+1) at h
    simpa only [UWalkUnary.output,UWalkUnary.lead,Bool.toNat_false,Nat.add_zero,Bool.false_eq_true,if_false,List.nil_append] using h
  · have h:=(install_slot powerSlots power_inj A4 P (PCPSerializerCapacity.Power.outputSlot 2)).trans pout
    have he:262144*(B+q+1)^2=65536*(B+q+(B+q+1)+1)^2:=by ring
    rw [he] at h
    exact h

end
end PCJ6e421fabe2aa4155_SourcePoolDrivers
