import Proof.Rows.CellGatePalette
import Proof.Rows.FinalThresholdMagnitudeBase

/-! One actual canonical-base update. Ten resident words physically fan out
the score bank; native child magnitude is computed, then added to the retained
base accumulator. Private scratch remains explicit for the subsequent cleanup. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CanonicalBaseCell
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
noncomputable section

def choice (i : Fin 44) : Option (Fin 10):=
  (PCJ45bee56da9f34d5a_CellGatePalette.entryChoice i.val).map (fun j=>j.castAdd 2)
def words (source mask : List Bool) (N w C U a : Nat) : Fin 10→List Bool:=
  Fin.addCases (m:=8) (n:=2) (motive:=fun _=>List Bool)
    (PCJ45bee56da9f34d5a_CellGatePalette.words source mask N w C 0)
    (![List.replicate (w+2) true,MatrixScoreWeight.scalar U (w+2) a] : Fin 2→List Bool)
def magSlots (i : Fin 44) : Fin 56:=((i.castAdd 1).natAdd 10).castAdd 1
theorem mag_injective : Function.Injective magSlots:=by
  intro i j h;apply Fin.ext;have hh:=congrArg Fin.val h;simpa only [magSlots,Fin.val_castAdd,Fin.val_natAdd] using Nat.add_left_cancel hh
def addSlots : Fin 9→Fin 56:=![8,24,28,29,55,9,30,31,32]
def fanout:=NativeFanout.machine choice
def advance:=DecompositionCountPosition.move (fun i : Fin 56=>if i=52 then .right else .stay)
def magnitude:=RecoveryFocus.machine magSlots C10ThresholdChildMagnitude.machine
def add:=RecoveryFocus.machine addSlots C10ThresholdMagnitudeBase.machine
def machine:=Composition.machine (Composition.machine (Composition.machine fanout advance) magnitude) add
def head : Fin 56→Nat:=fun i=>if i=52 then 1 else 0

theorem choice_word (source mask : List Bool) (N w C U a : Nat) (i : Fin 44) :
    (choice i).elim [] (words source mask N w C U a)=
      (PCJ45bee56da9f34d5a_CellGatePalette.entryChoice i.val).elim []
        (PCJ45bee56da9f34d5a_CellGatePalette.words source mask N w C 0) :=by
  cases he : PCJ45bee56da9f34d5a_CellGatePalette.entryChoice i.val with
  | none=>simp [choice,he]
  | some j=>simp [choice,he,words,Fin.addCases_left]

theorem entry (source mask : List Bool) (N w C D U a : Nat) (hC : C+1≤U) (hD : D≤U) (i : Fin 44) :
    NativeFanout.output choice (words source mask N w C U a) U (magSlots i)=
      ZeroPadding.pad U (C10NaturalHardwireScoreInputs.data source mask [] w C D N 0 0 i) :=by
  simp only [NativeFanout.output,magSlots,Fin.addCases_left,Fin.addCases_right,NativeFanout.word]
  rw [choice_word]
  by_cases hi:i=34
  · subst i;rfl
  have hi' : i.castAdd 4≠(34 : Fin 48):=by
    intro h
    apply hi
    apply Fin.ext
    exact congrArg (fun j : Fin 48=>j.val) h
  have h:=PCJ45bee56da9f34d5a_CellGatePalette.entry_pad source mask [] N w C D U hC hD (i.castAdd 4) hi'
  simpa only [Fin.addCases_left,Fin.val_castAdd] using h.symm


def masterSlots (i : Fin 10) : Fin 56:=(i.castAdd 45).castAdd 1
structure Exit (palette : Fin 10→List Bool) (U F : Nat) (H : Fin 56→Nat) (A : Fin 56→List Bool) : Prop where
  masterHeads : ∀ i,H (masterSlots i)=0
  masterTapes : ∀ i,A (masterSlots i)=palette i
  privateHeads : ∀ i,H (magSlots i)≤U
  privateLength : F+2≤U→∀ i,(A (magSlots i)).length≤U
  driverHead : H 54=0
  driverTape : A 54=List.replicate U true
  logHead : H 55=0
  logTape : A 55=List.replicate (U+1) false

/-- The native child, true membership mask, and count are resident masters;
the 44 mutable worker tapes are actually populated by paid fanout. -/
theorem run_details {n : Nat} (g : ExactThresholdGate n) (tail : List Bool) (w C D U a : Nat)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items g,natBitLength x.1.natAbs≤w)
    (hc : 8*w+12≤C) (hm : childMagnitude g<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items g) w C≤D)
    (hC : C+1≤U) (hDU : D≤U) (ha : childMagnitude g+a<2^(w+2))
    (hU : ∀ i,(words (exactWord g++tail) (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g))
      (C10ThresholdChildMagnitude.items g).length w C U a i).length≤U) :
    ∃ H A,
      Step machine (2*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+26)
        (fun _=>0)
        (NativeFanout.reusableInput (m:=44)
          (words (exactWord g++tail) (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g))
            (C10ThresholdChildMagnitude.items g).length w C U a) U) H A ∧
      Exit (words (exactWord g++tail) (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g))
        (C10ThresholdChildMagnitude.items g).length w C U (childMagnitude g+a)) U
        (C10ThresholdChildMagnitude.budget g w C) H A :=by
  let palette:=words (exactWord g++tail) (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g))
    (C10ThresholdChildMagnitude.items g).length w C U a
  let bank:=NativeFanout.output choice palette U
  have first:=NativeFanout.reusable choice palette U hU
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 56=>if i=52 then .right else .stay) (fun _=>0) bank
  have up:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
    (show _=head by funext i;by_cases h:i=52 <;>simp [head,h,HeadMove.apply]) rfl
  obtain ⟨result,mag,_,value,spares,_⟩:=C10ThresholdMagnitudeBase.magnitude_spares g tail [] [] w C D hw hc hm hD
  simp only [List.append_nil] at mag
  have worker:=(mag.pad (fun _=>U)).dock magSlots mag_injective head bank
    (by intro i;fin_cases i <;>rfl)
    (by intro i;exact entry _ _ _ _ _ _ _ _ hC hDU i)
  let H:=dockH magSlots head (C10NaturalHardwireScoreInputs.heads [] (exactWord g).length
    (C10ThresholdChildMagnitude.items g).length)
  let A:=install magSlots bank (fun i=>ZeroPadding.pad U (result i))
  have hvalue : A 24=MatrixScoreWeight.scalar U w (childMagnitude g) :=by
    have h:=(install_slot magSlots mag_injective bank (fun i=>ZeroPadding.pad U (result i)) 14)
    change A 24=ZeroPadding.pad U (result 14) at h
    rw [value] at h
    exact h.trans (MatrixBucketRootPower.pad_pad C U _ (by omega))
  have hspares (i : Fin 5) : A (![28,29,30,31,32] i)=List.replicate U false :=by
    have h:=install_slot magSlots mag_injective bank (fun i=>ZeroPadding.pad U (result i)) (![18,19,20,21,22] i)
    have hs:=spares i
    fin_cases i <;>change A _=List.replicate U false
    all_goals exact h.trans ((congrArg (ZeroPadding.pad U) hs).trans (pad_replicate_false U C (by omega)))
  have base:=C10ThresholdMagnitudeBase.run w U (childMagnitude g) a (by omega) hm ha
  have last:=base.dock addSlots (by decide) H A
    (by
      intro i;fin_cases i <;>first
        | exact (dockH_other magSlots _ _ _ (by decide)).trans rfl
        | exact dockH_slot magSlots mag_injective _ _ 14
        | exact dockH_slot magSlots mag_injective _ _ 18
        | exact dockH_slot magSlots mag_injective _ _ 19
        | exact dockH_slot magSlots mag_injective _ _ 20
        | exact dockH_slot magSlots mag_injective _ _ 21
        | exact dockH_slot magSlots mag_injective _ _ 22)
    (by
      intro i;fin_cases i
      · exact (install_other magSlots _ _ _ (by decide)).trans rfl
      · exact hvalue
      · exact hspares 0
      · exact hspares 1
      · exact (install_other magSlots _ _ _ (by decide)).trans rfl
      · exact (install_other magSlots _ _ _ (by decide)).trans rfl
      · exact hspares 2
      · exact hspares 3
      · exact hspares 4)
  have all:=((first.seq up).seq worker).seq last
  rw [show ((2*U+4+1+1)+1+C10ThresholdChildMagnitude.budget g w C)+1+(16*(w+2)+18)=
    2*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+26 by omega] at all
  have hsrc : (exactWord g).length≤U:=by
    have h:=hU 0
    change (exactWord g++tail).length≤U at h
    simp only [List.length_append] at h
    omega
  have hmask : (C10ThresholdChildMagnitude.items g).length≤U:=by
    have h:=hU 1
    change (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g)).length≤U at h
    simpa only [CloseoutRowsPoolWeight.mask,List.length_map] using h
  have hin (i : Fin 44) : (C10NaturalHardwireScoreInputs.data (exactWord g++tail)
      (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g)) [] w C D
      (C10ThresholdChildMagnitude.items g).length 0 0 i).length≤U:=by
    have he:=entry (exactWord g++tail) (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g))
      (C10ThresholdChildMagnitude.items g).length w C D U a hC hDU i
    have hf : (NativeFanout.output choice palette U (magSlots i)).length≤U:=by
      simp only [NativeFanout.output,magSlots,Fin.addCases_left,Fin.addCases_right,NativeFanout.word,
        ZeroPadding.pad_length]
      apply max_le le_rfl
      cases h : choice i with
      | none=>simp
      | some j=>exact hU j
    rw [he,ZeroPadding.pad_length] at hf
    exact (Nat.le_max_right _ _).trans hf
  refine ⟨_,_,all,{masterHeads:=?_,masterTapes:=?_,privateHeads:=?_,privateLength:=?_,driverHead:=?_,driverTape:=?_,logHead:=?_,logTape:=?_}⟩
  · intro i;fin_cases i
    all_goals first
      | exact dockH_slot addSlots (by decide) _ _ 0
      | exact dockH_slot addSlots (by decide) _ _ 5
      | exact (dockH_other addSlots _ _ _ (by decide)).trans
          ((dockH_other magSlots _ _ _ (by decide)).trans rfl)
  · intro i;fin_cases i
    all_goals first
      | exact install_slot addSlots (by decide) _ _ 0
      | exact install_slot addSlots (by decide) _ _ 5
      | exact (install_other addSlots _ _ _ (by decide)).trans
          ((install_other magSlots _ _ _ (by decide)).trans rfl)
  · intro i
    by_cases hi:∃j,addSlots j=magSlots i
    · obtain ⟨j,hj⟩:=hi
      rw [←hj,dockH_slot addSlots (by decide)]
      exact Nat.zero_le _
    · rw [dockH_other addSlots _ _ _ (by simpa using hi)]
      dsimp only [H]
      rw [dockH_slot magSlots mag_injective]
      fin_cases i <;>simp [C10NaturalHardwireScoreInputs.heads] <;>omega
  · intro hF i
    have hraw (j : Fin 44) : (result j).length≤U:=by
      apply LocalSupport.step_fits mag j U (hin j)
      fin_cases j <;>simp [C10NaturalHardwireScoreInputs.heads] <;>omega
    by_cases hi:∃j,addSlots j=magSlots i
    · obtain ⟨j,hj⟩:=hi
      rw [←hj,install_slot addSlots (by decide)]
      have hv:=congrArg Fin.val hj
      have hil:=i.isLt
      fin_cases j <;>norm_num [addSlots,magSlots] at hv
      all_goals first
        | omega
        | simp [C10ThresholdMagnitudeBase.output,MatrixScoreWeight.scalar,MatrixScoreWeight.zeros,
            ZeroPadding.pad_length,frame_length,SignedSortKey.binary_length] <;>omega
    · rw [install_other addSlots _ _ _ (by simpa using hi)]
      dsimp only [A]
      rw [install_slot magSlots mag_injective,ZeroPadding.pad_length]
      exact max_le le_rfl (hraw i)
  · exact (dockH_other addSlots _ _ _ (by decide)).trans
      ((dockH_other magSlots _ _ _ (by decide)).trans rfl)
  · exact (install_other addSlots _ _ _ (by decide)).trans
      ((install_other magSlots _ _ _ (by decide)).trans rfl)
  · exact dockH_slot addSlots (by decide) _ _ 4
  · exact install_slot addSlots (by decide) _ _ 4

theorem run {n : Nat} (g : ExactThresholdGate n) (tail : List Bool) (w C D U a : Nat)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items g,natBitLength x.1.natAbs≤w)
    (hc : 8*w+12≤C) (hm : childMagnitude g<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items g) w C≤D)
    (hC : C+1≤U) (hDU : D≤U) (ha : childMagnitude g+a<2^(w+2))
    (hU : ∀ i,(words (exactWord g++tail) (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g))
      (C10ThresholdChildMagnitude.items g).length w C U a i).length≤U) :
    ∃ H A,
      Step machine (2*U+C10ThresholdChildMagnitude.budget g w C+16*(w+2)+26)
        (fun _=>0)
        (NativeFanout.reusableInput (m:=44)
          (words (exactWord g++tail) (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g))
            (C10ThresholdChildMagnitude.items g).length w C U a) U) H A ∧
      H 9=0 ∧ A 9=MatrixScoreWeight.scalar U (w+2) (childMagnitude g+a) :=by
  obtain ⟨H,A,hr,h⟩:=run_details g tail w C D U a hw hc hm hD hC hDU ha hU
  exact ⟨H,A,hr,h.masterHeads 9,h.masterTapes 9⟩

end
end PCJ45bee56da9f34d5a_CanonicalBaseCell
