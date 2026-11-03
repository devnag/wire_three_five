import Proof.Rows.CanonicalBaseCell
import Proof.Rows.HeaderRewind

/-! A complete reusable canonical-base update: real magnitude and addition,
followed by paid rewind and erase of the 44 private worker tapes. The ten
resident masters, including the updated base, survive at head zero. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CanonicalBaseReentry
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open PCJ45bee56da9f34d5a_CanonicalBaseCell
noncomputable section

def slots (i : Fin 46) : Fin 56:=i.natAdd 10
theorem injective : Function.Injective slots:=by
  intro i j h;apply Fin.ext
  have h:=congrArg Fin.val h
  simp only [slots,Fin.val_natAdd] at h
  omega
def clear:=RecoveryFocus.machine slots (PCJ45bee56da9f34d5a_HeaderRewind.clear 44)
def machine:=Composition.machine PCJ45bee56da9f34d5a_CanonicalBaseCell.machine clear

theorem clear_run (palette : Fin 10→List Bool) (U F : Nat) (H : Fin 56→Nat) (A : Fin 56→List Bool)
    (h : Exit palette U F H A) (hF : F+2≤U) :
    Step clear (4*U+9) H A (fun _=>0) (NativeFanout.reusableInput (m:=44) palette U):=by
  have base:=PCJ45bee56da9f34d5a_HeaderRewind.clear_run 44 (fun i=>H (magSlots i))
    (fun i=>A (magSlots i)) U h.privateHeads (h.privateLength hF)
  have run:=base.dock slots injective H A
    (by
      intro i;fin_cases i
      all_goals first
        | rfl
        | exact h.driverHead
        | exact h.logHead)
    (by
      intro i;fin_cases i
      all_goals first
        | rfl
        | exact h.driverTape
        | exact h.logTape)
  apply run.congr
  · funext i
    by_cases hi:i.val<10
    · let j : Fin 10:=⟨i.val,hi⟩
      have he:masterSlots j=i:=Fin.ext rfl
      rw [←he,dockH_other slots _ _ _ (by
        intro k hk
        have hv:=congrArg Fin.val hk
        simp only [slots,masterSlots,Fin.val_natAdd,Fin.val_castAdd] at hv
        have hj:=j.isLt
        omega)]
      exact h.masterHeads j
    · let j : Fin 46:=⟨i.val-10,by omega⟩
      have he:slots j=i:=Fin.ext (by simp only [slots,Fin.val_natAdd,j];omega)
      rw [←he,dockH_slot slots injective]
  · apply HierarchyAllocation.install_eq slots injective
    · intro i;fin_cases i <;>rfl
    · intro i hi
      have hit:i.val<10:=by
        by_contra hlt
        let j : Fin 46:=⟨i.val-10,by omega⟩
        exact hi j (Fin.ext (by simp only [slots,Fin.val_natAdd,j];omega))
      let j : Fin 10:=⟨i.val,hit⟩
      have he:masterSlots j=i:=Fin.ext rfl
      rw [←he]
      simpa only [NativeFanout.reusableInput,NativeFanout.input,masterSlots,Fin.addCases_left] using (h.masterTapes j).symm

theorem run {n : Nat} (g : ExactThresholdGate n) (tail : List Bool) (w C D U a : Nat)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items g,natBitLength x.1.natAbs≤w)
    (hc : 8*w+12≤C) (hm : childMagnitude g<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items g) w C≤D)
    (hC : C+1≤U) (hDU : D≤U) (ha : childMagnitude g+a<2^(w+2))
    (hF : C10ThresholdChildMagnitude.budget g w C+2≤U)
    (hU : ∀ i,(words (exactWord g++tail) (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g))
      (C10ThresholdChildMagnitude.items g).length w C U a i).length≤U) :
    Step machine (6*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+36)
      (fun _=>0) (NativeFanout.reusableInput (m:=44)
        (words (exactWord g++tail) (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g))
          (C10ThresholdChildMagnitude.items g).length w C U a) U)
      (fun _=>0) (NativeFanout.reusableInput (m:=44)
        (words (exactWord g++tail) (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g))
          (C10ThresholdChildMagnitude.items g).length w C U (childMagnitude g+a)) U):=by
  obtain ⟨H,A,first,shape⟩:=run_details g tail w C D U a hw hc hm hD hC hDU ha hU
  have all:=first.seq (clear_run _ U _ H A shape hF)
  simpa only [machine,show (2*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+26)+1+(4*U+9)=
    6*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+36 by omega] using all
end
end PCJ45bee56da9f34d5a_CanonicalBaseReentry
