import Proof.SourceAssembly.SourceCircuitFrame

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

namespace NearCubicWires.SourceRequest.Gen.ParityQuery
open PCJ6e421fabe2aa4155_SourceParityQuery (slots slots_inj arity_eq)

/-- The generic prefix: only the q-templates (`ParityPrep`) are produced; the bitmap is given. -/
def machine:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourceParityPrep.machine
def input (q Q : Nat) (bm : List Bool) : Fin 137→List Bool:=fun i=>
  if i=3 then ZeroPadding.pad Q bm else if i=13 then UnaryTemplate.tape q else []
def budget (q Q : Nat) (bm : List Bool):=PCJ6e421fabe2aa4155_SourceParityPrep.budget q

theorem run (q Q : Nat) (bm : List Bool) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (fun _=>0) A ∧
      A 3=ZeroPadding.pad Q bm ∧
      A 131=frame (natWord q) ∧A 133=List.replicate (Capacity.value q) false ∧
      A 135=CompareMachine.word q ∧A 101=List.replicate (Capacity.value q) true ∧
      A 13=UnaryTemplate.tape q := by
  obtain ⟨B,hb,b0,b41,b43,b45,b11⟩:=PCJ6e421fabe2aa4155_SourceParityPrep.run q
  have selected : ∀ i,input q Q bm (slots i)=PCJ6e421fabe2aa4155_SourceParityPrep.input q i := by
    intro i
    by_cases hi:i=0
    · subst i
      simp only [input,slots,if_true]
      rw [if_neg (by decide)]
      exact arity_eq q
    · have hv : (slots i).val=90+i.val := by simp [slots,hi]
      have h3 : slots i≠3 := fun e => by have := congrArg Fin.val e; rw [hv] at this; simp at this; omega
      have h13 : slots i≠13 := fun e => by have := congrArg Fin.val e; rw [hv] at this; simp at this; omega
      simp only [input,h3,h13,if_false,PCJ6e421fabe2aa4155_SourceParityPrep.input,hi]
  obtain ⟨s,hs,st,sh,ss⟩:=hb.focus slots slots_inj (input q Q bm) selected
  have stepB : Step machine (PCJ6e421fabe2aa4155_SourceParityPrep.budget q)
      (fun _=>0) (input q Q bm) (fun _=>0) (install slots (input q Q bm) B):=⟨s,hs,funext sh,st,ss⟩
  refine ⟨install slots (input q Q bm) B,stepB,?_,?_,?_,?_,?_,?_⟩
  · rw [install_other slots _ B 3 (by decide)]; simp [input]
  · exact (install_slot slots slots_inj _ B 41).trans b41
  · exact (install_slot slots slots_inj _ B 43).trans b43
  · exact (install_slot slots slots_inj _ B 45).trans b45
  · exact (install_slot slots slots_inj _ B 11).trans b11
  · exact (install_slot slots slots_inj _ B 0).trans (b0.trans (arity_eq q).symm)

end NearCubicWires.SourceRequest.Gen.ParityQuery

namespace NearCubicWires.SourceRequest.Gen.SymmetricQuery
open PCJ6e421fabe2aa4155_SourceSymmetricQuery (slots slots_inj last capacity_fit)

def first:=TapeEmbedding.machine 4 Gen.ParityQuery.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 141→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.ParityQuery.input q Q bm) (fun _ : Fin 4=>[])

def budget (q Q : Nat) (bm : List Bool):=
  Gen.ParityQuery.budget q Q bm+1+PCJ6e421fabe2aa4155_SourceSymmetricCold.budget q

def bitmap (q Q : Nat) (bm : List Bool):=ZeroPadding.pad Q bm

def finalHeads (q Q : Nat) (bm : List Bool):=
  dockH slots (fun _=>0) (PCJ6e421fabe2aa4155_SourceSymmetricCold.heads q (bitmap q Q bm) q)

end NearCubicWires.SourceRequest.Gen.SymmetricQuery

namespace NearCubicWires.SourceRequest.Gen.SymmetricHeaderQuery
open PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery (slots slots_inj fresh slots_fresh last)

def first:=TapeEmbedding.machine 25 Gen.SymmetricQuery.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 166→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.SymmetricQuery.input q Q bm) (fun _ : Fin 25=>[])

def count (q Q : Nat) (bm : List Bool):=
  (PCJ6e421fabe2aa4155_SourceSymmetricScan.selected (Gen.SymmetricQuery.bitmap q Q bm) q).length

def beforeHeads (q Q : Nat) (bm : List Bool) : Fin 166→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (Gen.SymmetricQuery.finalHeads q Q bm) (fun _ : Fin 25=>0)

def finalHeads (q Q : Nat) (bm : List Bool):=dockH slots (beforeHeads q Q bm) (fun _=>0)

def budget (q Q : Nat) (bm : List Bool):=
  Gen.SymmetricQuery.budget q Q bm+1+
    PCJ6e421fabe2aa4155_SourceSymmetricHeader.budget (count q Q bm)

theorem selected_heads (q Q : Nat) (bm : List Bool) (i : Fin 26) :
    beforeHeads q Q bm (slots i)=PCJ6e421fabe2aa4155_SourceSymmetricHeader.heads i := by
  by_cases hi:i=3
  · subst i
    change beforeHeads q Q bm ((140 : Fin 141).castAdd 25)=1
    rw [beforeHeads,Fin.addCases_left]
    change dockH PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots _ _
      (PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots 7)=1
    rw [dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots_inj]
    rfl
  · rw [slots_fresh i hi]
    simp only [beforeHeads,Fin.addCases_right,PCJ6e421fabe2aa4155_SourceSymmetricHeader.heads,hi,if_false]

end NearCubicWires.SourceRequest.Gen.SymmetricHeaderQuery

namespace NearCubicWires.SourceRequest.Gen.ThresholdHeader

open NearCubicWires.SourceRequest.Gen.SymmetricQuery in
open PCJ6e421fabe2aa4155_SourceSymmetricQuery (slots slots_inj last capacity_fit) in
theorem selected_run (q Q : Nat) (bm : List Bool) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm) A ∧
      A 3=bitmap q Q bm ∧A 131=frame (natWord q) ∧A 135=CompareMachine.word q ∧
      A 140=CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 101=List.replicate (Capacity.value q) true := by
  obtain ⟨A,ha,h3,h131,h133,h135,h101,h13⟩:=Gen.ParityQuery.run q Q bm
  let bank : Fin 141→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 4=>[])
  have stepA : Step first (Gen.ParityQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (fun _=>0) bank :=
    ((ha.embed (fun _ : Fin 4=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl).congr
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have selected : ∀ i,bank (slots i)=PCJ6e421fabe2aa4155_SourceSymmetricCold.input
      q (Capacity.value q) (bitmap q Q bm) i := by
    intro i;fin_cases i
    · exact h13
    · rfl
    · exact h131
    · rfl
    · rfl
    · exact h133
    · exact h3
    · rfl
    · exact h135
  have hb:=PCJ6e421fabe2aa4155_SourceSymmetricCold.run q (Capacity.value q)
    (bitmap q Q bm) (capacity_fit q)
  let out:=PCJ6e421fabe2aa4155_SourceSymmetricCold.words q (Capacity.value q) (bitmap q Q bm) q
  have lastStep:=hb.dock slots slots_inj (fun _=>0) bank (by intro i;rfl) selected
  refine ⟨install slots bank out,stepA.seq lastStep,?_,?_,?_,?_,?_⟩
  · exact install_slot slots slots_inj bank out 6
  · exact install_slot slots slots_inj bank out 2
  · exact install_slot slots slots_inj bank out 8
  · exact install_slot slots slots_inj bank out 7
  · exact (install_other slots bank out 101 (by decide)).trans h101

open NearCubicWires.SourceRequest.Gen.SymmetricHeaderQuery in
open PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery (slots slots_inj fresh slots_fresh last) in
theorem run (q Q : Nat) (bm : List Bool) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm) A ∧
      A 3=Gen.SymmetricQuery.bitmap q Q bm ∧A 131=frame (natWord q) ∧
      A 135=CompareMachine.word q ∧A 140=CompareMachine.word (count q Q bm) ∧
      A 101=List.replicate (Capacity.value q) true ∧A 161=natWord (count q Q bm) ∧
      A 164=frame (natWord (count q Q bm)) := by
  obtain ⟨A,ha,h3,h131,h135,h140,h101⟩:=selected_run q Q bm
  let bank : Fin 166→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 25=>[])
  have firstStep : Step first (Gen.SymmetricQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm) bank :=
    (ha.embed (fun _ : Fin 25=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  obtain ⟨B,hb,_top,header,framed,driver⟩:=PCJ6e421fabe2aa4155_SourceSymmetricHeader.run (count q Q bm)
  have selected : ∀ i,bank (slots i)=PCJ6e421fabe2aa4155_SourceSymmetricHeader.input (count q Q bm) i := by
    intro i
    by_cases hi:i=3
    · subst i;exact h140
    · rw [slots_fresh i hi]
      simp only [bank,Fin.addCases_right,PCJ6e421fabe2aa4155_SourceSymmetricHeader.input,hi,if_false]
  have lastStep:=hb.dock slots slots_inj (beforeHeads q Q bm) bank (selected_heads q Q bm) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank B 3 (by decide)).trans h3
  · exact (install_other slots bank B 131 (by decide)).trans h131
  · exact (install_other slots bank B 135 (by decide)).trans h135
  · exact (install_slot slots slots_inj bank B 3).trans driver
  · exact (install_other slots bank B 101 (by decide)).trans h101
  · exact (install_slot slots slots_inj bank B 21).trans header
  · exact (install_slot slots slots_inj bank B 24).trans framed

end NearCubicWires.SourceRequest.Gen.ThresholdHeader

namespace NearCubicWires.SourceRequest.Gen.ThresholdCache
open PCJ6e421fabe2aa4155_SourceThresholdCache (slots last)

def first:=TapeEmbedding.machine 4 Gen.SymmetricHeaderQuery.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 170→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.SymmetricHeaderQuery.input q Q bm) (fun _ : Fin 4=>[])

def beforeHeads (q Q : Nat) (bm : List Bool) : Fin 170→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (Gen.SymmetricHeaderQuery.finalHeads q Q bm) (fun _ : Fin 4=>0)

def finalHeads (q Q : Nat) (bm : List Bool):=dockH slots (beforeHeads q Q bm) PCJ6e421fabe2aa4155_SourceThresholdBitmap.readyHeads

def budget (q Q : Nat) (bm : List Bool):=
  Gen.SymmetricHeaderQuery.budget q Q bm+1+PCJ6e421fabe2aa4155_SourceThresholdBitmap.budget q

def bits (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) := bm

theorem bits_length (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) : (bits q Q bm hbm).length=q:=hbm

theorem before_heads (q Q : Nat) (bm : List Bool) (i : Fin 7) :
    beforeHeads q Q bm (slots i)=PCJ6e421fabe2aa4155_SourceThresholdBitmap.heads q i := by
  fin_cases i
  · change Gen.SymmetricHeaderQuery.finalHeads q Q bm 3=q
    rw [Gen.SymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 3 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((3 : Fin 141).castAdd 25)=_
    rw [Gen.SymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots_inj _ _ 6
  · change Gen.SymmetricHeaderQuery.finalHeads q Q bm 135=1
    rw [Gen.SymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 135 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((135 : Fin 141).castAdd 25)=_
    rw [Gen.SymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots_inj _ _ 8
  · change Gen.SymmetricHeaderQuery.finalHeads q Q bm 101=0
    rw [Gen.SymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 101 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((101 : Fin 141).castAdd 25)=0
    rw [Gen.SymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_other _ _ _ 101 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl

theorem run (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm) A ∧
      A 131=frame (natWord q) ∧A 101=List.replicate (Capacity.value q) true ∧
      A 140=CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 161=natWord (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 164=frame (natWord (Gen.SymmetricHeaderQuery.count q Q bm)) ∧
      A 166=frame (weights (bits q Q bm hbm)) ∧A 167=frame (bits q Q bm hbm) := by
  obtain ⟨A,ha,h3,h131,h135,h140,h101,h161,h164⟩:=Gen.ThresholdHeader.run q Q bm
  let bank : Fin 170→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 4=>[])
  have firstStep : Step first (Gen.SymmetricHeaderQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm) bank :=
    (ha.embed (fun _ : Fin 4=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have selected : ∀ i,bank (slots i)=PCJ6e421fabe2aa4155_SourceThresholdBitmap.input Q q (bits q Q bm hbm) i := by
    intro i;fin_cases i
    · exact h3
    · exact h135
    · exact h101
    · rfl
    · rfl
    · rfl
    · rfl
  obtain ⟨k,_hk,raw⟩:=PCJ6e421fabe2aa4155_SourceThresholdBitmap.run Q q (bits q Q bm hbm) (bits_length q Q bm hbm)
  have lastStep:=raw.dock slots (by decide) (beforeHeads q Q bm) bank (before_heads q Q bm) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank _ 131 (by decide)).trans h131
  · exact install_slot slots (by decide) bank _ 2
  · exact (install_other slots bank _ 140 (by decide)).trans h140
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_other slots bank _ 164 (by decide)).trans h164
  · exact install_slot slots (by decide) bank _ 3
  · exact install_slot slots (by decide) bank _ 4

end NearCubicWires.SourceRequest.Gen.ThresholdCache

namespace NearCubicWires.SourceRequest.Gen.ThresholdQuery
open PCJ6e421fabe2aa4155_SourceThresholdQuery (slots slots_inj oldSlots last)

def first:=TapeEmbedding.machine 33 Gen.ThresholdCache.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 203→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.ThresholdCache.input q Q bm) (fun _ : Fin 33=>[])

def beforeHeads (q Q : Nat) (bm : List Bool) : Fin 203→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (Gen.ThresholdCache.finalHeads q Q bm) (fun _ : Fin 33=>0)

def finalHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q):=
  dockH slots (beforeHeads q Q bm) (PCJ6e421fabe2aa4155_SourceThresholdCold.heads q
    (Gen.ThresholdCache.bits q Q bm hbm) (Gen.SymmetricHeaderQuery.count q Q bm))

def budget (q Q : Nat) (bm : List Bool):=
  Gen.ThresholdCache.budget q Q bm+1+
    PCJ6e421fabe2aa4155_SourceThresholdCold.budget q (Gen.SymmetricHeaderQuery.count q Q bm)

theorem count_le (q Q : Nat) (bm : List Bool) : Gen.SymmetricHeaderQuery.count q Q bm≤q := by
  exact (List.length_filter_le _ _).trans List.length_range.le

theorem old_heads (q Q : Nat) (bm : List Bool) (i : Fin 5) :
    Gen.ThresholdCache.finalHeads q Q bm (oldSlots i)=0 := by
  fin_cases i
  · exact dockH_slot _ (by decide) _ _ 2
  · change Gen.ThresholdCache.finalHeads q Q bm 131=0
    rw [Gen.ThresholdCache.finalHeads,dockH_other _ _ _ 131 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 131=0
    rw [Gen.SymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 131 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((131 : Fin 141).castAdd 25)=0
    rw [Gen.SymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots_inj _ _ 2
  · exact dockH_slot _ (by decide) _ _ 3
  · exact dockH_slot _ (by decide) _ _ 4
  · change Gen.ThresholdCache.finalHeads q Q bm 140=0
    rw [Gen.ThresholdCache.finalHeads,dockH_other _ _ _ 140 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 140=0
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.slots_inj _ _ 3

theorem selected_heads (q Q : Nat) (bm : List Bool) (i : Fin 33) : beforeHeads q Q bm (slots i)=0 := by
  by_cases h22:i=22
  · subst i;exact old_heads q Q bm 0
  by_cases h26:i=26
  · subst i;exact old_heads q Q bm 1
  by_cases h27:i=27
  · subst i;exact old_heads q Q bm 2
  by_cases h28:i=28
  · subst i;exact old_heads q Q bm 3
  by_cases h32:i=32
  · subst i;exact old_heads q Q bm 4
  simp only [slots,h22,h26,h27,h28,h32,if_false,beforeHeads,Fin.addCases_right]

theorem run_retained (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm hbm) A ∧
      A 199=PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs q
        (Gen.ThresholdCache.bits q Q bm hbm) (Gen.SymmetricHeaderQuery.count q Q bm) 0 ∧
      A 200=PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs q
        (Gen.ThresholdCache.bits q Q bm hbm) (Gen.SymmetricHeaderQuery.count q Q bm) 1 ∧
      A 140=CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 161=natWord (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 164=frame (natWord (Gen.SymmetricHeaderQuery.count q Q bm)) ∧
      A 201=List.replicate (Capacity.value q) false ∧A 101=List.replicate (Capacity.value q) true ∧ A 131=frame (natWord q) := by
  obtain ⟨A,ha,h131,h101,h140,h161,h164,h166,h167⟩:=Gen.ThresholdCache.run q Q bm hbm
  let bank : Fin 203→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 33=>[])
  have firstStep : Step first (Gen.ThresholdCache.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm) bank :=
    (ha.embed (fun _ : Fin 33=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have selected : ∀ i,bank (slots i)=PCJ6e421fabe2aa4155_SourceThresholdCold.input q
      (Gen.SymmetricHeaderQuery.count q Q bm) (Gen.ThresholdCache.bits q Q bm hbm) i := by
    intro i
    by_cases h22:i=22
    · subst i;exact h101
    by_cases h26:i=26
    · subst i;exact h131
    by_cases h27:i=27
    · subst i;exact h166
    by_cases h28:i=28
    · subst i;exact h167
    by_cases h32:i=32
    · subst i;exact h140
    simp only [slots,h22,h26,h27,h28,h32,if_false,bank,Fin.addCases_right,PCJ6e421fabe2aa4155_SourceThresholdCold.input]
  have raw:=PCJ6e421fabe2aa4155_SourceThresholdCold.run q (Gen.SymmetricHeaderQuery.count q Q bm)
    (Gen.ThresholdCache.bits q Q bm hbm) (count_le q Q bm)
    (Gen.ThresholdCache.bits_length q Q bm hbm)
  have lastStep:=raw.dock slots slots_inj (beforeHeads q Q bm) bank (selected_heads q Q bm) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot slots slots_inj bank _ 29
  · exact install_slot slots slots_inj bank _ 30
  · exact install_slot slots slots_inj bank _ 32
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_other slots bank _ 164 (by decide)).trans h164
  · exact install_slot slots slots_inj bank _ 31
  · exact install_slot slots slots_inj bank _ 22

  · exact install_slot slots slots_inj bank _ 26

end NearCubicWires.SourceRequest.Gen.ThresholdQuery

namespace NearCubicWires.SourceRequest.Gen.ThresholdTopQuery
open PCJ6e421fabe2aa4155_SourceThresholdTopQuery (slots last)

def first:=TapeEmbedding.machine 3 Gen.ThresholdQuery.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 206→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.ThresholdQuery.input q Q bm) (fun _ : Fin 3=>[])

def beforeHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) : Fin 206→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (Gen.ThresholdQuery.finalHeads q Q bm hbm) (fun _ : Fin 3=>0)

def finalHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q):=
  dockH slots (beforeHeads q Q bm hbm) (PCJ6e421fabe2aa4155_SourceThresholdTop.H
    (PCJ6e421fabe2aa4155_SourceThresholdTop.finalOut (Gen.SymmetricHeaderQuery.count q Q bm)))

def budget (q Q : Nat) (bm : List Bool):=
  Gen.ThresholdQuery.budget q Q bm+1+
    PCJ6e421fabe2aa4155_SourceThresholdTop.budget (Gen.SymmetricHeaderQuery.count q Q bm)

theorem selected_heads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) (i : Fin 6) :
    beforeHeads q Q bm hbm (slots i)=PCJ6e421fabe2aa4155_SourceThresholdTop.inputHeads i := by
  fin_cases i
  · change Gen.ThresholdQuery.finalHeads q Q bm hbm 164=0
    rw [Gen.ThresholdQuery.finalHeads,dockH_other _ _ _ 164 (by decide)]
    change Gen.ThresholdCache.finalHeads q Q bm 164=0
    rw [Gen.ThresholdCache.finalHeads,dockH_other _ _ _ 164 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 164=0
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.slots_inj _ _ 24
  · rfl
  · rfl
  · rfl
  · change Gen.ThresholdQuery.finalHeads q Q bm hbm (PCJ6e421fabe2aa4155_SourceThresholdQuery.slots 32)=1
    rw [Gen.ThresholdQuery.finalHeads,dockH_slot _ PCJ6e421fabe2aa4155_SourceThresholdQuery.slots_inj _ _ 32]
    rfl
  · change Gen.ThresholdQuery.finalHeads q Q bm hbm (PCJ6e421fabe2aa4155_SourceThresholdQuery.slots 31)=0
    rw [Gen.ThresholdQuery.finalHeads,dockH_slot _ PCJ6e421fabe2aa4155_SourceThresholdQuery.slots_inj _ _ 31]
    rfl

theorem run_retained (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm hbm) A ∧
      A 199=PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs q
        (Gen.ThresholdCache.bits q Q bm hbm) (Gen.SymmetricHeaderQuery.count q Q bm) 0 ∧
      A 200=PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs q
        (Gen.ThresholdCache.bits q Q bm hbm) (Gen.SymmetricHeaderQuery.count q Q bm) 1 ∧
      A 140=CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 161=natWord (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 204=frame (PCJ6e421fabe2aa4155_SourceThresholdTop.payload (Gen.SymmetricHeaderQuery.count q Q bm)) ∧
      A 101=List.replicate (Capacity.value q) true ∧ A 131=frame (natWord q) := by
  obtain ⟨A,ha,h199,h200,h140,h161,h164,h201,h101,h131⟩:=Gen.ThresholdQuery.run_retained q Q bm hbm
  let bank : Fin 206→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 3=>[])
  have firstStep : Step first (Gen.ThresholdQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm hbm) bank :=
    (ha.embed (fun _ : Fin 3=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  let n:=Gen.SymmetricHeaderQuery.count q Q bm
  have hn:n≤q:=Gen.ThresholdQuery.count_le q Q bm
  have hlen:2*(natWord n).length+1≤Capacity.value q := by
    have hh:natBitLength n≤n+1:=Nat.add_le_add_right (Nat.log_le_self 2 n) 1
    rw [DecompositionSource.natWord_length];unfold Capacity.value;nlinarith
  have selected : ∀ i,bank (slots i)=PCJ6e421fabe2aa4155_SourceThresholdTop.input n (Capacity.value q) i := by
    intro i;fin_cases i
    · exact h164
    · rfl
    · rfl
    · rfl
    · exact h140
    · exact h201
  have lastStep:=(PCJ6e421fabe2aa4155_SourceThresholdTop.run n (Capacity.value q) hlen).dock slots (by decide)
    (beforeHeads q Q bm hbm) bank (selected_heads q Q bm hbm) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank _ 199 (by decide)).trans h199
  · exact (install_other slots bank _ 200 (by decide)).trans h200
  · exact install_slot slots (by decide) bank _ 4
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_slot slots (by decide) bank _ 2).trans (PCJ6e421fabe2aa4155_SourceThresholdTop.final_exact n)
  · exact (install_other slots bank _ 101 (by decide)).trans h101

  · exact (install_other slots bank _ 131 (by decide)).trans h131

end NearCubicWires.SourceRequest.Gen.ThresholdTopQuery

namespace NearCubicWires.SourceRequest.Gen.ThresholdReady
open PCJ6e421fabe2aa4155_SourceThresholdReady (slots last)

def streams (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) : Fin 3→List Bool:=
  ![PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs q (Gen.ThresholdCache.bits q Q bm hbm)
      (Gen.SymmetricHeaderQuery.count q Q bm) 0,
    PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs q (Gen.ThresholdCache.bits q Q bm hbm)
      (Gen.SymmetricHeaderQuery.count q Q bm) 1,
    frame (PCJ6e421fabe2aa4155_SourceThresholdTop.payload (Gen.SymmetricHeaderQuery.count q Q bm))]

def first:=TapeEmbedding.machine 4 Gen.ThresholdTopQuery.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 210→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.ThresholdTopQuery.input q Q bm) (fun _ : Fin 4=>[])

def beforeHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) : Fin 210→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (Gen.ThresholdTopQuery.finalHeads q Q bm hbm) (fun _ : Fin 4=>0)

def finalHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q):=
  dockH slots (beforeHeads q Q bm hbm) (fun _=>0)

def budget (q Q : Nat) (bm : List Bool):=
  Gen.ThresholdTopQuery.budget q Q bm+1+2*Capacity.value q+2

theorem before_heads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) (i : Fin 5) :
    beforeHeads q Q bm hbm (slots i)=PCJ6e421fabe2aa4155_SourceClear.join
      (fun j=>(streams q Q bm hbm j).length) 0 0 i := by
  fin_cases i
  · change Gen.ThresholdTopQuery.finalHeads q Q bm hbm 199=_
    rw [Gen.ThresholdTopQuery.finalHeads,dockH_other _ _ _ 199 (by decide)]
    change Gen.ThresholdQuery.finalHeads q Q bm hbm (PCJ6e421fabe2aa4155_SourceThresholdQuery.slots 29)=_
    rw [Gen.ThresholdQuery.finalHeads,dockH_slot _ PCJ6e421fabe2aa4155_SourceThresholdQuery.slots_inj _ _ 29]
    rfl
  · change Gen.ThresholdTopQuery.finalHeads q Q bm hbm 200=_
    rw [Gen.ThresholdTopQuery.finalHeads,dockH_other _ _ _ 200 (by decide)]
    change Gen.ThresholdQuery.finalHeads q Q bm hbm (PCJ6e421fabe2aa4155_SourceThresholdQuery.slots 30)=_
    rw [Gen.ThresholdQuery.finalHeads,dockH_slot _ PCJ6e421fabe2aa4155_SourceThresholdQuery.slots_inj _ _ 30]
    rfl
  · change Gen.ThresholdTopQuery.finalHeads q Q bm hbm (PCJ6e421fabe2aa4155_SourceThresholdTopQuery.slots 2)=_
    rw [Gen.ThresholdTopQuery.finalHeads,dockH_slot PCJ6e421fabe2aa4155_SourceThresholdTopQuery.slots (by decide) _ _ 2]
    change (PCJ6e421fabe2aa4155_SourceThresholdTop.finalOut _ 0).length=_
    rw [PCJ6e421fabe2aa4155_SourceThresholdTop.final_exact]
    rfl
  · change Gen.ThresholdTopQuery.finalHeads q Q bm hbm 101=0
    rw [Gen.ThresholdTopQuery.finalHeads,dockH_other _ _ _ 101 (by decide)]
    change Gen.ThresholdQuery.finalHeads q Q bm hbm (PCJ6e421fabe2aa4155_SourceThresholdQuery.slots 22)=0
    rw [Gen.ThresholdQuery.finalHeads,dockH_slot _ PCJ6e421fabe2aa4155_SourceThresholdQuery.slots_inj _ _ 22]
    rfl
  · rfl

theorem run_retained (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm hbm) A ∧
      A 199=streams q Q bm hbm 0 ∧A 200=streams q Q bm hbm 1 ∧A 204=streams q Q bm hbm 2 ∧
      A 140=CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 161=natWord (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 207=[] ∧A 208=[] ∧A 209=[] ∧ A 131=frame (natWord q) := by
  obtain ⟨A,ha,h199,h200,h140,h161,h204,h101,h131⟩:=Gen.ThresholdTopQuery.run_retained q Q bm hbm
  let bank : Fin 210→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 4=>[])
  have firstStep : Step first (Gen.ThresholdTopQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm hbm) bank :=
    (ha.embed (fun _ : Fin 4=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have hlen : ∀ i,(streams q Q bm hbm i).length≤Capacity.value q := by
    intro i;fin_cases i
    · exact PCJ6e421fabe2aa4155_SourceThresholdBounds.outputs_bound _ _ _
        (Gen.ThresholdQuery.count_le q Q bm) (Gen.ThresholdCache.bits_length q Q bm hbm) 0
    · exact PCJ6e421fabe2aa4155_SourceThresholdBounds.outputs_bound _ _ _
        (Gen.ThresholdQuery.count_le q Q bm) (Gen.ThresholdCache.bits_length q Q bm hbm) 1
    · exact PCJ6e421fabe2aa4155_SourceThresholdBounds.top_bound _ _ (Gen.ThresholdQuery.count_le q Q bm)
  have selected : ∀ i,bank (slots i)=PCJ6e421fabe2aa4155_SourceClear.join (streams q Q bm hbm)
      (List.replicate (Capacity.value q) true) [] i := by
    intro i;fin_cases i
    · exact h199
    · exact h200
    · exact h204
    · exact h101
    · rfl
  have raw:=PCJ6e421fabe2aa4155_SourceClear.raw_rewind (streams q Q bm hbm) (fun i=>(streams q Q bm hbm i).length)
    (Capacity.value q) hlen
  have lastStep:=raw.dock slots (by decide) (beforeHeads q Q bm hbm) bank (before_heads q Q bm hbm) selected
  refine ⟨_,(firstStep.seq lastStep).enlarge (by unfold budget;omega),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot slots (by decide) bank _ 0
  · exact install_slot slots (by decide) bank _ 1
  · exact install_slot slots (by decide) bank _ 2
  · exact (install_other slots bank _ 140 (by decide)).trans h140
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact install_other slots bank _ 207 (by decide)
  · exact install_other slots bank _ 208 (by decide)
  · exact install_other slots bank _ 209 (by decide)

  · exact (install_other slots bank _ 131 (by decide)).trans h131

end NearCubicWires.SourceRequest.Gen.ThresholdReady

namespace NearCubicWires.SourceRequest.Gen.ThresholdPhysical
open PCJ6e421fabe2aa4155_SourceThresholdPhysical (gates gates_length gates_native gates_support native slots slots_inj writer)

def machine:=Composition.machine Gen.ThresholdReady.machine writer

def finalHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q):=
  dockH slots (Gen.ThresholdReady.finalHeads q Q bm hbm)
    (PCJ6e421fabe2aa4155_SourceSymmetricAssemble.H
      (PCJ6e421fabe2aa4155_SourceThresholdTop.payload (Gen.SymmetricHeaderQuery.count q Q bm))
      (gates q (Gen.SymmetricHeaderQuery.count q Q bm)
        (Gen.ThresholdCache.bits q Q bm hbm)) 3)

def budget (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q):=
  Gen.ThresholdReady.budget q Q bm+1+
    PCJ6e421fabe2aa4155_SourceSymmetricAssemble.budget
      (PCJ6e421fabe2aa4155_SourceThresholdTop.payload (Gen.SymmetricHeaderQuery.count q Q bm))
      (gates q (Gen.SymmetricHeaderQuery.count q Q bm)
        (Gen.ThresholdCache.bits q Q bm hbm))

theorem selected_heads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) (i : Fin 8) :
    Gen.ThresholdReady.finalHeads q Q bm hbm (slots i)=
      PCJ6e421fabe2aa4155_SourceSymmetricAssemble.H
        (PCJ6e421fabe2aa4155_SourceThresholdTop.payload (Gen.SymmetricHeaderQuery.count q Q bm))
        (gates q (Gen.SymmetricHeaderQuery.count q Q bm)
          (Gen.ThresholdCache.bits q Q bm hbm)) 0 i := by
  fin_cases i
  · change Gen.ThresholdReady.finalHeads q Q bm hbm 161=0
    rw [Gen.ThresholdReady.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change Gen.ThresholdTopQuery.finalHeads q Q bm hbm 161=0
    rw [Gen.ThresholdTopQuery.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change Gen.ThresholdQuery.finalHeads q Q bm hbm 161=0
    rw [Gen.ThresholdQuery.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change Gen.ThresholdCache.finalHeads q Q bm 161=0
    rw [Gen.ThresholdCache.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 161=0
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.slots_inj _ _ 21
  · exact dockH_slot _ (by decide) _ _ 2
  · exact dockH_slot _ (by decide) _ _ 0
  · exact dockH_slot _ (by decide) _ _ 1
  · change Gen.ThresholdReady.finalHeads q Q bm hbm 140=1
    rw [Gen.ThresholdReady.finalHeads,dockH_other _ _ _ 140 (by decide)]
    change Gen.ThresholdTopQuery.finalHeads q Q bm hbm 140=1
    exact dockH_slot _ (by decide) _ _ 4
  · exact dockH_other _ _ _ 207 (by decide)
  · exact dockH_other _ _ _ 208 (by decide)
  · exact dockH_other _ _ _ 209 (by decide)

theorem run_retained (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) :
    ∃ A,Step machine (budget q Q bm hbm) (fun _=>0)
      (Gen.ThresholdReady.input q Q bm) (finalHeads q Q bm hbm) A ∧
      A 207=native q (Gen.SymmetricHeaderQuery.count q Q bm)
        (Gen.ThresholdCache.bits q Q bm hbm) ∧
      A 208=CloseoutRowsTupleSeek.supportWord (gates q (Gen.SymmetricHeaderQuery.count q Q bm)
        (Gen.ThresholdCache.bits q Q bm hbm)) ∧ A 131=frame (natWord q) := by
  obtain ⟨A,ha,h199,h200,h204,h140,h161,h207,h208,h209,h131⟩:=Gen.ThresholdReady.run_retained q Q bm hbm
  let n:=Gen.SymmetricHeaderQuery.count q Q bm
  let bits:=Gen.ThresholdCache.bits q Q bm hbm
  have selected : ∀ i,A (slots i)=PCJ6e421fabe2aa4155_SourceSymmetricAssemble.A
      (PCJ6e421fabe2aa4155_SourceThresholdTop.payload n) (gates q n bits) 0 i := by
    intro i;fin_cases i
    · change A 161=natWord (gates q n bits).length
      rw [gates_length];exact h161
    · exact h204
    · exact h199.trans (gates_native _ _ _).symm
    · exact h200.trans (gates_support _ _ _).symm
    · change A 140=CompareMachine.word (gates q n bits).length
      rw [gates_length];exact h140
    · exact h207
    · exact h208
    · exact h209
  have lastStep:=(PCJ6e421fabe2aa4155_SourceSymmetricAssemble.run
      (PCJ6e421fabe2aa4155_SourceThresholdTop.payload n) (gates q n bits)).dock slots slots_inj
        (Gen.ThresholdReady.finalHeads q Q bm hbm) A (selected_heads q Q bm hbm) selected
  exact ⟨_,ha.seq lastStep,install_slot slots slots_inj A _ 5,install_slot slots slots_inj A _ 6,
    (install_other slots A _ 131 (by decide)).trans h131⟩

end NearCubicWires.SourceRequest.Gen.ThresholdPhysical

namespace NearCubicWires.SourceRequest.Gen.ThresholdCanonical
open PCJ6e421fabe2aa4155_SourceThresholdPhysical (native gates slots slots_inj)
open SupplierPipeline CompilerSemantics

/-- The generic chain's native word is the THR parity circuit of the support whose bitmap it reads. -/
theorem native_eq {q : Nat} (S : Finset (Fin q)) (Q : Nat) :
    native q (Gen.SymmetricHeaderQuery.count q Q (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S))
      (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)
      = PCJd4d1d9d7d1fa4313_Production.thrWord (normalizedThresholdParityCircuit S) := by
  unfold Gen.SymmetricHeaderQuery.count
  rw [show Gen.SymmetricQuery.bitmap q Q (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)
      = ZeroPadding.pad Q (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S) from rfl,
    PCJ6e421fabe2aa4155_SourceSymmetricMeaning.count_eq]
  exact PCJ6e421fabe2aa4155_SourceThresholdCanonical.bytes_eq S

theorem bitmap_length {q : Nat} (S : Finset (Fin q)) :
    (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S).length = q := by
  simp [PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap]

theorem native_head {q : Nat} (S : Finset (Fin q)) (Q : Nat) :
    Gen.ThresholdPhysical.finalHeads q Q (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)
      (bitmap_length S) 207
      = (PCJd4d1d9d7d1fa4313_Production.thrWord (normalizedThresholdParityCircuit S)).length := by
  change Gen.ThresholdPhysical.finalHeads q Q _ (bitmap_length S) (slots 5)=_
  rw [Gen.ThresholdPhysical.finalHeads,dockH_slot _ slots_inj _ _ 5]
  change (native q (Gen.SymmetricHeaderQuery.count q Q (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S))
    (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)).length=_
  rw [native_eq]

end NearCubicWires.SourceRequest.Gen.ThresholdCanonical

namespace NearCubicWires.SourceRequest.Gen.CircuitFrame
open RepairSource.ProjectionNormalization SupplierPipeline CompilerSemantics

theorem threshold_forward : CursorRestore.NoLeft Gen.ThresholdPhysical.machine 207 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (PCJ6e421fabe2aa4155_SourceCircuitFrame.fresh_forward _ (1 : Fin 4))
      (EquationRowCuts.unselected_forward _ _ 207 (by decide)))
    (CursorRestore.focus_forward _ PCJ6e421fabe2aa4155_SourceThresholdPhysical.slots_inj _ 5
      PCJ6e421fabe2aa4155_SourceCircuitFrame.assembler_forward)

def machine:=AppendOutputFrame.machine Gen.ThresholdPhysical.machine 207

theorem run {q : Nat} (S : Finset (Fin q)) (Q : Nat) :
    let c:=normalizedThresholdParityCircuit S
    let bm:=PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S
    ∃ A,Step machine (2*Gen.ThresholdPhysical.budget q Q bm (Gen.ThresholdCanonical.bitmap_length S)+
        4*(PCJd4d1d9d7d1fa4313_Production.thrWord c).length+7) (fun _=>0)
      (AppendOutputFrame.input (Gen.ThresholdReady.input q Q bm)) (fun _=>0) A ∧
      A 212=frame (PCJd4d1d9d7d1fa4313_Production.thrWord c) ∧
      A 207=PCJd4d1d9d7d1fa4313_Production.thrWord c ∧
      A 208=CloseoutRowsTupleSeek.supportWord (PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates q S.card bm) ∧
      A 131=frame (natWord q) := by
  intro c bm
  have hbm : bm.length = q := Gen.ThresholdCanonical.bitmap_length S
  obtain ⟨A,⟨source,hr,rh,rt,rs⟩,hn,hs,h131⟩:=Gen.ThresholdPhysical.run_retained q Q bm hbm
  have hn' : A 207=PCJd4d1d9d7d1fa4313_Production.thrWord c :=
    hn.trans (Gen.ThresholdCanonical.native_eq S Q)
  obtain ⟨s,sr,st,sh,sk,ss⟩:=PCPPNativeFrame.frame_run
    Gen.ThresholdPhysical.machine 207 threshold_forward
    (Gen.ThresholdPhysical.budget q Q bm hbm) (Gen.ThresholdReady.input q Q bm) source hr
    (PCJd4d1d9d7d1fa4313_Production.thrWord c)
    (by rw [rt];exact hn') (by rw [rh];exact Gen.ThresholdCanonical.native_head S Q)
  have hcount : Gen.SymmetricHeaderQuery.count q Q bm = S.card :=
    PCJ6e421fabe2aa4155_SourceSymmetricMeaning.count_eq S Q
  refine ⟨s.final.tapes,(Step.of_run sr (funext sh) rfl).enlarge (by omega),st,?_,?_,?_⟩
  · exact (sk 207).trans (by rw [rt];exact hn')
  · exact (sk 208).trans (by rw [rt,hs,hcount];rfl)
  · exact (sk 131).trans (by rw [rt];exact h131)

end NearCubicWires.SourceRequest.Gen.CircuitFrame


end
