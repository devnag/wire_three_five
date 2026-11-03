import Proof.SourceAssembly.SourcePoolDrivers
import Proof.MachineModel.ClockScalarFields

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolScalars
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.ProjectionNormalization
open PCJ6e421fabe2aa4155_SourceLog (clock_step dock_zero install_blank)
noncomputable section
local instance : NeZero (DimensionPower.tapes 1):=⟨by decide⟩

def powerSlots (i : Fin (DimensionPower.tapes 1)) : Fin 14:=if i=0 then 0 else ⟨i.val+1,by have hi:i.val<5:=i.isLt;omega⟩
def fixedSlots : Fin 2→Fin 14:=![6,7]
def sumSlots : Fin 4→Fin 14:=![4,6,8,9]
def zeroSlots : Fin 5→Fin 14:=![1,10,11,12,13]
theorem power_inj : Function.Injective powerSlots:=by decide

def power:=RecoveryFocus.machine powerSlots (DimensionPower.machine 1 8)
def fixed:=RecoveryFocus.machine fixedSlots (HierarchyFixedWord.machine (List.replicate 12 true))
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def zero:=RecoveryFocus.machine zeroSlots ClockNormalize.machine
def machine:=Composition.machine (Composition.machine (Composition.machine power fixed) sum) zero
def input (w : Nat) (i : Fin 14):=if i=0 then UnaryTemplate.tape w else if i=1 then List.replicate w true else []
def budget (w : Nat):=DimensionPower.cost 8 w 1+1+26+1+(2*(8*w+12)+6)+1+(4*w+4)

theorem zero_step (w : Nat) : ∃ A,Step ClockNormalize.machine (4*w+4) (fun _=>0)
    (ClockScalarFields.zeroInput w) (fun _=>0) A ∧A 0=List.replicate w true ∧A 2=frame (SignedSortKey.binary w 0) := by
  obtain ⟨r,hr,h0,_h1,h2,_h3,_h4,hh,hs⟩:=ClockScalarFields.zero_run w
  exact ⟨r.final.tapes,⟨r,hr,funext hh,rfl,hs.le⟩,h0,h2⟩

theorem run (w : Nat) : ∃ A,Step machine (budget w) (fun _=>0) (input w) (fun _=>0) A ∧
    A 0=UnaryTemplate.tape w ∧A 1=List.replicate w true ∧
    A 8=List.replicate (8*w+12) true ∧A 11=frame (SignedSortKey.binary w 0) := by
  obtain ⟨P,hp,p0,pv⟩:=DimensionPower.power_run 1 8 w
  have hp':=dock_zero (clock_step hp) powerSlots power_inj (input w) (by
    intro i;by_cases hi:i=0
    · subst i;rfl
    · have hv:i.val≠0:=by intro he;exact hi (Fin.ext he)
      have h0:powerSlots i≠0:=by unfold powerSlots;rw [if_neg hi];intro he;have h:=congrArg Fin.val he;simp only [Fin.val_zero] at h;omega
      have h1:powerSlots i≠1:=by unfold powerSlots;rw [if_neg hi];intro he;have h:=congrArg Fin.val he;simp only [Fin.val_one] at h;omega
      simp only [input,if_neg h0,if_neg h1,DimensionPower.input,hv,if_false])
  let A1:=install powerSlots (input w) P
  have fresh1 : ∀i : Fin 14,6≤ i.val→A1 i=[]:=
    install_blank powerSlots (input w) P (old:=2) (by omega) (by decide)
      (by intro i hi;have h0:i≠0:=by intro he;subst i;contradiction
          have h1:i≠1:=by intro he;subst i;contradiction
          simp only [input,if_neg h0,if_neg h1])
  have h0:A1 0=UnaryTemplate.tape w:=(install_slot powerSlots power_inj (input w) P 0).trans p0
  have h4:A1 4=List.replicate (8*w) true:=by
    have h:=(install_slot powerSlots power_inj (input w) P (DimensionPower.valueSlot 1 1 le_rfl)).trans pv
    change A1 4=List.replicate (8*w^1) true at h
    simpa only [pow_one] using h
  obtain ⟨r,hr,rt,rh,rs⟩:=HierarchyFixedWord.word_ready (List.replicate 12 true)
  have hf0 : Step (HierarchyFixedWord.machine (List.replicate 12 true)) 26 (fun _=>0) (fun _=>[])
      (fun _=>0) (![List.replicate 12 true,List.replicate 12 false]) := by
    exact ⟨r,hr,funext rh,rt,rs.le⟩
  have hf:=dock_zero hf0 fixedSlots (by decide) A1 (by intro i;fin_cases i <;>exact fresh1 _ (by decide))
  let A2:=install fixedSlots A1 (![List.replicate 12 true,List.replicate 12 false])
  have fresh2 : ∀i : Fin 14,8≤ i.val→A2 i=[]:=install_blank fixedSlots A1 _ (old:=6) (by omega) (by decide) fresh1
  have hs:=dock_zero (clock_step (ClockUnarySum.sum_ready (8*w) 12)) sumSlots (by decide) A2 (by
    intro i;fin_cases i
    · exact (install_other fixedSlots A1 _ 4 (by decide)).trans h4
    · exact install_slot fixedSlots (by decide) A1 _ 0
    · exact fresh2 8 (by decide)
    · exact fresh2 9 (by decide))
  let A3:=install sumSlots A2 (![List.replicate (8*w) true,List.replicate 12 true,List.replicate (8*w+12) true,List.replicate (8*w+12+2) false])
  have fresh3 : ∀i : Fin 14,10≤ i.val→A3 i=[]:=install_blank sumSlots A2 _ (old:=8) (by omega) (by decide) fresh2
  have h1:A3 1=List.replicate w true:=
    (install_other sumSlots A2 _ 1 (by decide)).trans ((install_other fixedSlots A1 _ 1 (by decide)).trans
      ((install_other powerSlots (input w) P 1 (by decide)).trans (by simp [input])))
  obtain ⟨Z,hz,z0,z2⟩:=zero_step w
  have hz':=dock_zero hz zeroSlots (by decide) A3 (by
    intro i;fin_cases i
    · exact h1
    all_goals exact fresh3 _ (by decide))
  refine ⟨_,((hp'.seq hf).seq hs).seq hz',?_,?_,?_,?_⟩
  · exact (install_other zeroSlots A3 Z 0 (by decide)).trans
      ((install_other sumSlots A2 _ 0 (by decide)).trans ((install_other fixedSlots A1 _ 0 (by decide)).trans h0))
  · exact (install_slot zeroSlots (by decide) A3 Z 0).trans z0
  · exact (install_other zeroSlots A3 Z 8 (by decide)).trans (install_slot sumSlots (by decide) A2 _ 2)
  · exact (install_slot zeroSlots (by decide) A3 Z 2).trans z2

end
end PCJ6e421fabe2aa4155_SourcePoolScalars
