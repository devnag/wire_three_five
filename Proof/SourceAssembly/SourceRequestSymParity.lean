import Proof.SourceAssembly.SourceRequestThrKinds
import Proof.SourceAssembly.SourceRequestThrSwitch
import Proof.SourceAssembly.SourceSymmetricCanonical

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization SupplierPipeline
noncomputable section

namespace NearCubicWires.SourceRequest.Gen.SymQuery

open NearCubicWires.SourceRequest.Gen.SymmetricQuery in
open PCJ6e421fabe2aa4155_SourceSymmetricQuery (slots slots_inj last capacity_fit) in
/-- The SYM query stage, generic: the two bottom streams, the count driver and the reserve. -/
theorem run (q Q : Nat) (bm : List Bool) :
    ∃ A, Step machine (budget q Q bm) (fun _ => 0) (input q Q bm) (finalHeads q Q bm) A ∧
      A 138 = PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs q (bitmap q Q bm) q 0 ∧
      A 139 = PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs q (bitmap q Q bm) q 1 ∧
      A 140 = CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 101 = List.replicate (Capacity.value q) true := by
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
  refine ⟨install slots bank out,stepA.seq lastStep,?_,?_,?_,?_⟩
  · exact install_slot slots slots_inj bank out 3
  · exact install_slot slots slots_inj bank out 4
  · exact install_slot slots slots_inj bank out 7
  · exact (install_other slots bank out 101 (by decide)).trans h101

end NearCubicWires.SourceRequest.Gen.SymQuery

namespace NearCubicWires.SourceRequest.Gen.SymHeader

open NearCubicWires.SourceRequest.Gen.SymmetricHeaderQuery in
open PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery (slots slots_inj fresh slots_fresh last) in
/-- The SYM header stage, generic (the original `SymmetricHeaderQuery.run` at the generic bank). -/
theorem run (q Q : Nat) (bm : List Bool) :
    ∃ A, Step machine (budget q Q bm) (fun _ => 0) (input q Q bm) (finalHeads q Q bm) A ∧
      A 138 = PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs q (Gen.SymmetricQuery.bitmap q Q bm) q 0 ∧
      A 139 = PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs q (Gen.SymmetricQuery.bitmap q Q bm) q 1 ∧
      A 140 = CompareMachine.word (count q Q bm) ∧
      A 142 = frame (PCJ6e421fabe2aa4155_SourceSymmetricTop.table (count q Q bm)) ∧
      A 161 = natWord (count q Q bm) ∧ A 101 = List.replicate (Capacity.value q) true := by
  obtain ⟨A,ha,h138,h139,h140,h101⟩:=Gen.SymQuery.run q Q bm
  let bank : Fin 166→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 25=>[])
  have stepA : Step first (Gen.SymmetricQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm) bank :=
    (ha.embed (fun _ : Fin 25=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  obtain ⟨B,hb,top,header,_framed,driver⟩:=PCJ6e421fabe2aa4155_SourceSymmetricHeader.run (count q Q bm)
  have selected : ∀ i,bank (slots i)=PCJ6e421fabe2aa4155_SourceSymmetricHeader.input (count q Q bm) i := by
    intro i
    by_cases hi:i=3
    · subst i;exact h140
    · rw [slots_fresh i hi]
      simp only [bank,Fin.addCases_right,PCJ6e421fabe2aa4155_SourceSymmetricHeader.input,hi,if_false]
  have lastStep:=hb.dock slots slots_inj (beforeHeads q Q bm) bank (selected_heads q Q bm) selected
  refine ⟨install slots bank B,stepA.seq lastStep,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank B 138 (by decide)).trans h138
  · exact (install_other slots bank B 139 (by decide)).trans h139
  · exact (install_slot slots slots_inj bank B 3).trans driver
  · exact (install_slot slots slots_inj bank B 1).trans top
  · exact (install_slot slots slots_inj bank B 21).trans header
  · exact (install_other slots bank B 101 (by decide)).trans h101

end NearCubicWires.SourceRequest.Gen.SymHeader

namespace NearCubicWires.SourceRequest.Gen.SymReset
open PCJ6e421fabe2aa4155_SourceSymmetricReset (slots last)

def first := TapeEmbedding.machine 4 Gen.SymmetricHeaderQuery.machine
def machine := Composition.machine first last
def input (q Q : Nat) (bm : List Bool) : Fin 170 → List Bool :=
  Fin.addCases (motive := fun _ => List Bool) (Gen.SymmetricHeaderQuery.input q Q bm) (fun _ : Fin 4 => [])
def beforeHeads (q Q : Nat) (bm : List Bool) : Fin 170 → Nat :=
  Fin.addCases (motive := fun _ => Nat) (Gen.SymmetricHeaderQuery.finalHeads q Q bm) (fun _ : Fin 4 => 0)
def finalHeads (q Q : Nat) (bm : List Bool) := dockH slots (beforeHeads q Q bm) (fun _ => 0)
def budget (q Q : Nat) (bm : List Bool) :=
  Gen.SymmetricHeaderQuery.budget q Q bm + 1 + 2 * Capacity.value q + 2

theorem before_heads (q Q : Nat) (bm : List Bool) (i : Fin 4) :
    beforeHeads q Q bm (slots i) = PCJ6e421fabe2aa4155_SourceClear.join
      (fun j => (PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs q
        (Gen.SymmetricQuery.bitmap q Q bm) q j).length) 0 0 i := by
  fin_cases i
  · change Gen.SymmetricHeaderQuery.finalHeads q Q bm 138 = _
    rw [Gen.SymmetricHeaderQuery.finalHeads, dockH_other _ _ _ 138 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((138 : Fin 141).castAdd 25) = _
    rw [Gen.SymmetricHeaderQuery.beforeHeads, Fin.addCases_left]
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots_inj _ _ 3
  · change Gen.SymmetricHeaderQuery.finalHeads q Q bm 139 = _
    rw [Gen.SymmetricHeaderQuery.finalHeads, dockH_other _ _ _ 139 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((139 : Fin 141).castAdd 25) = _
    rw [Gen.SymmetricHeaderQuery.beforeHeads, Fin.addCases_left]
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots_inj _ _ 4
  · change Gen.SymmetricHeaderQuery.finalHeads q Q bm 101 = 0
    rw [Gen.SymmetricHeaderQuery.finalHeads, dockH_other _ _ _ 101 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((101 : Fin 141).castAdd 25) = 0
    rw [Gen.SymmetricHeaderQuery.beforeHeads, Fin.addCases_left]
    exact dockH_other _ _ _ 101 (by decide)
  · rfl

theorem run (q Q : Nat) (bm : List Bool) :
    ∃ A, Step machine (budget q Q bm) (fun _ => 0) (input q Q bm) (finalHeads q Q bm) A ∧
      A 138 = PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs q (Gen.SymmetricQuery.bitmap q Q bm) q 0 ∧
      A 139 = PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs q (Gen.SymmetricQuery.bitmap q Q bm) q 1 ∧
      A 140 = CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 142 = frame (PCJ6e421fabe2aa4155_SourceSymmetricTop.table (Gen.SymmetricHeaderQuery.count q Q bm)) ∧
      A 161 = natWord (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 167 = [] ∧ A 168 = [] ∧ A 169 = [] := by
  obtain ⟨A, ha, h138, h139, h140, h142, h161, h101⟩ := Gen.SymHeader.run q Q bm
  let bank : Fin 170 → List Bool := Fin.addCases (motive := fun _ => List Bool) A (fun _ : Fin 4 => [])
  let out := PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs q (Gen.SymmetricQuery.bitmap q Q bm) q
  have firstStep : Step first (Gen.SymmetricHeaderQuery.budget q Q bm)
      (fun _ => 0) (input q Q bm) (beforeHeads q Q bm) bank :=
    (ha.embed (fun _ : Fin 4 => 0) (fun _ => [])).congr_in
      (by funext i; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp only [Fin.addCases_left, Fin.addCases_right]) rfl
  have raw := PCJ6e421fabe2aa4155_SourceClear.raw_rewind out (fun i => (out i).length)
    (Capacity.value q) (fun i => PCJ6e421fabe2aa4155_SourceSymmetricBound.output_bound q _ i)
  have selected : ∀ i, bank (slots i) = PCJ6e421fabe2aa4155_SourceClear.join out
      (List.replicate (Capacity.value q) true) [] i := by
    intro i; fin_cases i
    · exact h138
    · exact h139
    · exact h101
    · rfl
  have lastStep := raw.dock slots (by decide) (beforeHeads q Q bm) bank (before_heads q Q bm) selected
  refine ⟨_, (firstStep.seq lastStep).enlarge (by unfold budget; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact install_slot slots (by decide) bank _ 0
  · exact install_slot slots (by decide) bank _ 1
  · exact (install_other slots bank _ 140 (by decide)).trans h140
  · exact (install_other slots bank _ 142 (by decide)).trans h142
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact install_other slots bank _ 167 (by decide)
  · exact install_other slots bank _ 168 (by decide)
  · exact install_other slots bank _ 169 (by decide)

end NearCubicWires.SourceRequest.Gen.SymReset

namespace NearCubicWires.SourceRequest.Gen.SymPhysical
open PCJ6e421fabe2aa4155_SourceSymmetricPhysical (gates gates_length gates_native gates_support slots slots_inj
  direction bump writer)

def selectedGates (q Q : Nat) (bm : List Bool) := gates q (Gen.SymmetricQuery.bitmap q Q bm)
def top (q Q : Nat) (bm : List Bool) :=
  PCJ6e421fabe2aa4155_SourceSymmetricTop.table (Gen.SymmetricHeaderQuery.count q Q bm)
def native (q Q : Nat) (bm : List Bool) :=
  PCJ6e421fabe2aa4155_SourceSymmetricAssemble.circuitWord (top q Q bm) (selectedGates q Q bm)
def machine := Composition.machine Gen.SymReset.machine (Composition.machine bump writer)
def bumpedHeads (q Q : Nat) (bm : List Bool) := fun i => HeadMove.apply (direction i)
  (Gen.SymReset.finalHeads q Q bm i)
def finalHeads (q Q : Nat) (bm : List Bool) := dockH slots (bumpedHeads q Q bm)
  (PCJ6e421fabe2aa4155_SourceSymmetricAssemble.H (top q Q bm) (selectedGates q Q bm) 3)
def budget (q Q : Nat) (bm : List Bool) :=
  Gen.SymReset.budget q Q bm + 3 +
    PCJ6e421fabe2aa4155_SourceSymmetricAssemble.budget (top q Q bm) (selectedGates q Q bm)

theorem reset_heads (q Q : Nat) (bm : List Bool) (i : Fin 8) :
    Gen.SymReset.finalHeads q Q bm (slots i) = 0 := by
  fin_cases i
  · change Gen.SymReset.finalHeads q Q bm 161 = 0
    rw [Gen.SymReset.finalHeads, dockH_other _ _ _ 161 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 161 = 0
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.slots_inj _ _ 21
  · change Gen.SymReset.finalHeads q Q bm 142 = 0
    rw [Gen.SymReset.finalHeads, dockH_other _ _ _ 142 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 142 = 0
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.slots_inj _ _ 1
  · exact dockH_slot _ (by decide) _ _ 0
  · exact dockH_slot _ (by decide) _ _ 1
  · change Gen.SymReset.finalHeads q Q bm 140 = 0
    rw [Gen.SymReset.finalHeads, dockH_other _ _ _ 140 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 140 = 0
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.slots_inj _ _ 3
  · exact dockH_other _ _ _ 167 (by decide)
  · exact dockH_other _ _ _ 168 (by decide)
  · exact dockH_other _ _ _ 169 (by decide)

theorem selected_heads (q Q : Nat) (bm : List Bool) (i : Fin 8) :
    bumpedHeads q Q bm (slots i)
      = PCJ6e421fabe2aa4155_SourceSymmetricAssemble.H (top q Q bm) (selectedGates q Q bm) 0 i := by
  unfold bumpedHeads
  rw [reset_heads]
  fin_cases i <;> simp [direction, slots, HeadMove.apply, PCJ6e421fabe2aa4155_SourceSymmetricAssemble.H]

/-- **The SYM parity writer, generic**: from the generic bank, the native circuit word on 167 and its support
stream on 168. -/
theorem run (q Q : Nat) (bm : List Bool) :
    ∃ A, Step machine (budget q Q bm) (fun _ => 0) (Gen.SymReset.input q Q bm) (finalHeads q Q bm) A ∧
      A 167 = native q Q bm ∧ A 168 = CloseoutRowsTupleSeek.supportWord (selectedGates q Q bm) := by
  obtain ⟨A, ha, h138, h139, h140, h142, h161, h167, h168, h169⟩ := Gen.SymReset.run q Q bm
  obtain ⟨br, hr, hf, _⟩ := DecompositionCountPosition.move_run direction (Gen.SymReset.finalHeads q Q bm) A
  have stepB : Step bump 1 (Gen.SymReset.finalHeads q Q bm) A (bumpedHeads q Q bm) A :=
    Step.of_run hr (by rw [hf]; rfl) (by rw [hf])
  have hlen : (selectedGates q Q bm).length = Gen.SymmetricHeaderQuery.count q Q bm := gates_length _ _
  have selected : ∀ i, A (slots i)
      = PCJ6e421fabe2aa4155_SourceSymmetricAssemble.A (top q Q bm) (selectedGates q Q bm) 0 i := by
    intro i; fin_cases i
    · change A 161 = natWord (selectedGates q Q bm).length
      rw [hlen]; exact h161
    · exact h142
    · exact h138.trans (gates_native _ _).symm
    · exact h139.trans (gates_support _ _).symm
    · change A 140 = CompareMachine.word (selectedGates q Q bm).length
      rw [hlen]; exact h140
    · exact h167
    · exact h168
    · exact h169
  have writeStep := (PCJ6e421fabe2aa4155_SourceSymmetricAssemble.run (top q Q bm) (selectedGates q Q bm)).dock
    slots slots_inj (bumpedHeads q Q bm) A (selected_heads q Q bm) selected
  refine ⟨_, (ha.seq (stepB.seq writeStep)).enlarge (by unfold budget; omega), ?_, ?_⟩
  · exact install_slot slots slots_inj A _ 5
  · exact install_slot slots slots_inj A _ 6

theorem native_head (q Q : Nat) (bm : List Bool) : finalHeads q Q bm 167 = (native q Q bm).length :=
  dockH_slot slots slots_inj _ _ 5

theorem support_head (q Q : Nat) (bm : List Bool) :
    finalHeads q Q bm 168 = (CloseoutRowsTupleSeek.supportWord (selectedGates q Q bm)).length :=
  dockH_slot slots slots_inj _ _ 6

/-- The generic writer's native word at the parity bitmap is the canonical parity circuit (`symWord`). -/
theorem native_eq {q : Nat} (S : Finset (Fin q)) :
    native q 0 (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)
      = PCJd4d1d9d7d1fa4313_Production.symWord (normalizedParityCircuit S) :=
  PCJ6e421fabe2aa4155_SourceSymmetricCanonical.bytes_eq S 0

theorem support_eq {q : Nat} (S : Finset (Fin q)) :
    CloseoutRowsTupleSeek.supportWord (selectedGates q 0 (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S))
      = CloseoutRowsSupportStream.supportWord (List.ofFn (normalizedParityCircuit S).bottom) :=
  (gates_support _ _).trans (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.supports_eq S 0)

end NearCubicWires.SourceRequest.Gen.SymPhysical

namespace NearCubicWires.SourceRequest.Gen.SymFrame
open PCJ6e421fabe2aa4155_SourceSymmetricPhysical (slots slots_inj direction bump writer)

theorem reset_forward (i : Fin 4) (hi : ∀ j, PCJ6e421fabe2aa4155_SourceSymmetricReset.slots j ≠ i.natAdd 166) :
    CursorRestore.NoLeft Gen.SymReset.machine (i.natAdd 166) :=
  CursorRestore.composition_forward _ _ _ (EquationRowRaw.embedded_extra_forward _ i)
    (EquationRowCuts.unselected_forward _ _ _ hi)

theorem native_forward : CursorRestore.NoLeft Gen.SymPhysical.machine 167 :=
  CursorRestore.composition_forward _ _ _ (reset_forward 1 (by decide))
    (CursorRestore.composition_forward _ _ _ (ThrOriginalForward.position_forward _ _ (by decide))
      (CursorRestore.focus_forward _ slots_inj _ 5 PCJ6e421fabe2aa4155_SourceCircuitFrame.assembler_forward))

theorem support_forward : CursorRestore.NoLeft Gen.SymPhysical.machine 168 :=
  CursorRestore.composition_forward _ _ _ (reset_forward 2 (by decide))
    (CursorRestore.composition_forward _ _ _ (ThrOriginalForward.position_forward _ _ (by decide))
      (CursorRestore.focus_forward _ slots_inj _ 6 Gen.SupportFrame.assembler_support_forward))

def nativeMachine := AppendOutputFrame.machine Gen.SymPhysical.machine 167
def supportMachine := AppendOutputFrame.machine Gen.SymPhysical.machine 168

theorem native_run (q Q : Nat) (bm : List Bool) :
    ∃ A, Step nativeMachine (2 * Gen.SymPhysical.budget q Q bm + 4 * (Gen.SymPhysical.native q Q bm).length + 7)
        (fun _ => 0) (AppendOutputFrame.input (Gen.SymReset.input q Q bm)) (fun _ => 0) A ∧
      A 172 = frame (Gen.SymPhysical.native q Q bm) := by
  obtain ⟨A, ⟨source, hr, rh, rt, rs⟩, hn, hs⟩ := Gen.SymPhysical.run q Q bm
  obtain ⟨s, sr, st, sh, sk, ss⟩ := PCPPNativeFrame.frame_run Gen.SymPhysical.machine 167 native_forward
    _ _ source hr (Gen.SymPhysical.native q Q bm) (by rw [rt]; exact hn)
    (by rw [rh]; exact Gen.SymPhysical.native_head q Q bm)
  exact ⟨s.final.tapes, (Step.of_run sr (funext sh) rfl).enlarge (by omega), st⟩

theorem support_run (q Q : Nat) (bm : List Bool) :
    ∃ A, Step supportMachine (2 * Gen.SymPhysical.budget q Q bm +
        4 * (CloseoutRowsTupleSeek.supportWord (Gen.SymPhysical.selectedGates q Q bm)).length + 7)
        (fun _ => 0) (AppendOutputFrame.input (Gen.SymReset.input q Q bm)) (fun _ => 0) A ∧
      A 172 = frame (CloseoutRowsTupleSeek.supportWord (Gen.SymPhysical.selectedGates q Q bm)) := by
  obtain ⟨A, ⟨source, hr, rh, rt, rs⟩, hn, hs⟩ := Gen.SymPhysical.run q Q bm
  obtain ⟨s, sr, st, sh, sk, ss⟩ := PCPPNativeFrame.frame_run Gen.SymPhysical.machine 168 support_forward
    _ _ source hr (CloseoutRowsTupleSeek.supportWord (Gen.SymPhysical.selectedGates q Q bm))
    (by rw [rt]; exact hs) (by rw [rh]; exact Gen.SymPhysical.support_head q Q bm)
  exact ⟨s.final.tapes, (Step.of_run sr (funext sh) rfl).enlarge (by omega), st⟩

theorem input_at (q Q : Nat) (bm : List Bool) (i : Fin 174) :
    AppendOutputFrame.input (Gen.SymReset.input q Q bm) i = Gen.ChainIn.chainAt q Q bm i.val := by
  have l3 : ∀ j : Fin 170, Gen.SymReset.input q Q bm j = Gen.ChainIn.chainAt q Q bm j.val :=
    Gen.ChainIn.step (n := 4) _ q Q bm (by omega) (Gen.ChainIn.lvl2 q Q bm)
  have l4 : ∀ j : Fin 171, AppendOutputLength.input (Gen.SymReset.input q Q bm) j
      = Gen.ChainIn.chainAt q Q bm j.val :=
    Gen.ChainIn.step (n := 1) _ q Q bm (by omega) l3
  have l5 : ∀ j : Fin 172, AppendOutputLength.input (AppendOutputLength.input (Gen.SymReset.input q Q bm)) j
      = Gen.ChainIn.chainAt q Q bm j.val :=
    Gen.ChainIn.step (n := 1) _ q Q bm (by omega) l4
  exact Gen.ChainIn.step (n := 2) _ q Q bm (by omega) l5 i

end NearCubicWires.SourceRequest.Gen.SymFrame

namespace NearCubicWires.SourceRequest.SymSystematic
open PCJd4d1d9d7d1fa4313_Production
open PCJ6e421fabe2aa4155_SourceSymmetricMeaning (bitmap)
open ThrSystematic (away fo_input zeroH desc)

def bVal (i : Nat) : Nat := if i = 0 then 172 else 173 + i
def dVal (i : Nat) : Nat := 179 + i
def descVal (k : Nat) : Nat := if k = 0 then 3 else if k = 1 then 13 else if k = 2 then 182 else 192

def slotA (i : Fin 174) : Fin 354 := ⟨i.val, by omega⟩
def slotB (i : Fin 6) : Fin 354 := ⟨bVal i.val, by have := i.isLt; unfold bVal; split_ifs <;> omega⟩
def slotD (i : Fin 174) : Fin 354 := ⟨dVal i.val, by have := i.isLt; unfold dVal; omega⟩
def descSlots (k : Fin 4) : Fin 354 := ⟨descVal k.val, by have := k.isLt; unfold descVal; split_ifs <;> omega⟩

theorem slotA_inj : Function.Injective slotA := by
  intro i j h
  have hv : (slotA i).val = (slotA j).val := congrArg Fin.val h
  exact Fin.ext hv
theorem slotB_inj : Function.Injective slotB := by
  intro i j h
  have hv : bVal i.val = bVal j.val := congrArg Fin.val h
  apply Fin.ext
  unfold bVal at hv
  split_ifs at hv <;> omega
theorem slotD_inj : Function.Injective slotD := by
  intro i j h
  have hv : dVal i.val = dVal j.val := congrArg Fin.val h
  apply Fin.ext
  unfold dVal at hv
  omega
theorem descSlots_inj : Function.Injective descSlots := by
  intro i j h
  have hv : descVal i.val = descVal j.val := congrArg Fin.val h
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  unfold descVal at hv
  split_ifs at hv <;> omega

def entryVal (q : Nat) (bm : List Bool) (x : Nat) : List Bool :=
  if x < 174 then Gen.ChainIn.chainAt q 0 bm x
  else if 179 ≤ x then Gen.ChainIn.chainAt q 0 bm (x - 179) else []

def st0 (q : Nat) (bm : List Bool) : Fin 354 → List Bool := fun x => entryVal q bm x.val

theorem entry_eq (q : Nat) (bm : List Bool) :
    install descSlots (fun _ => []) (desc q bm) = st0 q bm := by
  funext x
  by_cases hx : ∃ k, descSlots k = x
  · obtain ⟨k, rfl⟩ := hx
    rw [install_slot _ descSlots_inj]
    have hk := k.isLt
    show desc q bm k = entryVal q bm (descVal k.val)
    unfold desc descVal entryVal Gen.ChainIn.chainAt
    by_cases h0 : k.val = 0
    · rw [if_pos (Or.inl h0), if_pos h0, if_pos (by omega), if_pos rfl, ZeroPadding.pad_zero]
    · by_cases h1 : k.val = 1
      · rw [if_neg (by omega), if_neg h0, if_pos h1, if_pos (by omega), if_neg (by omega), if_pos rfl]
      · by_cases h2 : k.val = 2
        · rw [if_pos (Or.inr h2), if_neg h0, if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega),
            show 182 - 179 = 3 by omega, if_pos rfl, ZeroPadding.pad_zero]
        · rw [if_neg (by omega), if_neg h0, if_neg h1, if_neg h2, if_neg (by omega), if_pos (by omega),
            show 192 - 179 = 13 by omega, if_neg (by omega), if_pos rfl]
  · rw [install_other _ _ _ _ (fun k e => hx ⟨k, e⟩)]
    have n0 : x.val ≠ 3 := fun e => hx ⟨0, Fin.ext e.symm⟩
    have n1 : x.val ≠ 13 := fun e => hx ⟨1, Fin.ext e.symm⟩
    have n2 : x.val ≠ 182 := fun e => hx ⟨2, Fin.ext e.symm⟩
    have n3 : x.val ≠ 192 := fun e => hx ⟨3, Fin.ext e.symm⟩
    show [] = entryVal q bm x.val
    unfold entryVal Gen.ChainIn.chainAt
    split_ifs <;> first | rfl | omega

theorem A_entry (q : Nat) (bm : List Bool) (j : Fin 174) :
    st0 q bm (slotA j) = AppendOutputFrame.input (Gen.SymReset.input q 0 bm) j := by
  rw [Gen.SymFrame.input_at]
  show entryVal q bm j.val = _
  unfold entryVal
  rw [if_pos j.isLt]

theorem B_entry (q : Nat) (bm : List Bool) (A1 : Fin 174 → List Bool) (w : List Bool) (h172 : A1 172 = w)
    (j : Fin 6) :
    install slotA (st0 q bm) A1 (slotB j) = AppendOutputFrame.input (![w, []] : Fin 2 → List Bool) j := by
  rw [fo_input]
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show slotB j = slotA 172 from Fin.ext (by show bVal j.val = 172; unfold bVal; rw [if_pos h0]),
      install_slot _ slotA_inj, h172]
  · have hj := j.isLt
    rw [if_neg h0, install_other _ _ _ _ (away _ _ (fun k => by
      have := k.isLt; show k.val ≠ bVal j.val; unfold bVal; rw [if_neg h0]; omega))]
    show entryVal q bm (bVal j.val) = []
    unfold bVal entryVal
    rw [if_neg h0, if_neg (by omega), if_neg (by omega)]

theorem D_entry (q : Nat) (bm : List Bool) (A1 : Fin 174 → List Bool) (B1 : Fin 6 → List Bool) (j : Fin 174) :
    install slotB (install slotA (st0 q bm) A1) B1 (slotD j) = AppendOutputFrame.input (Gen.SymReset.input q 0 bm) j := by
  have hj := j.isLt
  rw [install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show bVal k.val ≠ dVal j.val; unfold bVal dVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show k.val ≠ dVal j.val; unfold dVal; omega)),
      Gen.SymFrame.input_at]
  show entryVal q bm (dVal j.val) = _
  unfold dVal entryVal
  rw [if_neg (by omega), if_pos (by omega), show 179 + j.val - 179 = j.val by omega]

def outN : Fin 354 := slotB 4
def outS : Fin 354 := slotD 172
def outT : Fin 354 := ⟨353, by omega⟩

def machine :=
  Composition.machine (RecoveryFocus.machine slotA Gen.SymFrame.nativeMachine)
    (Composition.machine (RecoveryFocus.machine slotB PCJ6e421fabe2aa4155_SourceFrameOuter.machine)
      (RecoveryFocus.machine slotD Gen.SymFrame.supportMachine))

def cost {q : Nat} (S : Finset (Fin q)) : Nat :=
  let bm := bitmap S
  (2 * Gen.SymPhysical.budget q 0 bm + 4 * (Gen.SymPhysical.native q 0 bm).length + 7) + 1 +
    ((12 * (Gen.SymPhysical.native q 0 bm).length + 13) + 1 +
      (2 * Gen.SymPhysical.budget q 0 bm +
        4 * (CloseoutRowsTupleSeek.supportWord (Gen.SymPhysical.selectedGates q 0 bm)).length + 7))

/-- **The SYM systematic factor, exact.** -/
theorem exact_run {q : Nat} (S : Finset (Fin q)) :
    ∃ F, Step machine (cost S) (fun _ => 0) (st0 q (bitmap S)) (fun _ => 0) F ∧
      F outN = frame (frame (symWord (normalizedParityCircuit S))) ∧
      F outS = frame (CloseoutRowsSupportStream.supportWord (List.ofFn (normalizedParityCircuit S).bottom)) ∧
      F outT = [] := by
  obtain ⟨A1, sA, a172⟩ := Gen.SymFrame.native_run q 0 (bitmap S)
  obtain ⟨B1, sB, b4⟩ := PCJ6e421fabe2aa4155_SourceFrameOuter.run (Gen.SymPhysical.native q 0 (bitmap S))
  obtain ⟨D1, sD, d172⟩ := Gen.SymFrame.support_run q 0 (bitmap S)
  have dA := sA.dock slotA slotA_inj (fun _ => 0) (st0 q (bitmap S)) (fun _ => rfl) (A_entry q (bitmap S))
  rw [zeroH] at dA
  have dB := sB.dock slotB slotB_inj (fun _ => 0) (install slotA (st0 q (bitmap S)) A1) (fun _ => rfl)
    (B_entry q (bitmap S) A1 _ a172)
  rw [zeroH] at dB
  have dD := sD.dock slotD slotD_inj (fun _ => 0) (install slotB (install slotA (st0 q (bitmap S)) A1) B1)
    (fun _ => rfl) (D_entry q (bitmap S) A1 B1)
  rw [zeroH] at dD
  refine ⟨_, dA.seq (dB.seq dD), ?_, ?_, ?_⟩
  · rw [outN,
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show dVal k.val ≠ 177; unfold dVal; omega)),
      install_slot _ slotB_inj, b4, Gen.SymPhysical.native_eq]
  · rw [outS, install_slot _ slotD_inj, d172, Gen.SymPhysical.support_eq]
  · rw [outT,
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show dVal k.val ≠ 353; unfold dVal; omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show bVal k.val ≠ 353; unfold bVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show k.val ≠ 353; omega))]
    show entryVal q (bitmap S) 353 = []
    unfold entryVal
    rw [if_neg (by omega), if_pos (by omega)]
    exact Gen.ChainIn.chainAt_high q 0 (bitmap S) _ (by omega)

section normal
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- **The SYM systematic factor producer, in `FactorProducer` normal form** (`R ≥ 1` for the blank TOP). -/
theorem produce (a : DecompositionAlgorithm) (idx : Fin pcpp.systematicBits) (R : Nat) (hR : 1 ≤ R) :
    ∃ F, Step machine (cost (pcpp.systematicSupport idx)) (fun _ => 0)
      (install descSlots (fun _ => List.replicate R false)
        (fun k => ZeroPadding.pad R (desc q (bitmap (pcpp.systematicSupport idx)) k)))
      (fun _ => 0) F ∧
      F outN = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segN true (some (C10TotalDecode.Atom.systematic idx : C10TotalDecode.Atom pcpp)))) ∧
      F outS = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segS true (some (C10TotalDecode.Atom.systematic idx : C10TotalDecode.Atom pcpp)))) ∧
      F outT = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segT a true (some (C10TotalDecode.Atom.systematic idx : C10TotalDecode.Atom pcpp)))) := by
  obtain ⟨F, hF, hN, hS, hT⟩ := exact_run (pcpp.systematicSupport idx)
  have hnil : (fun _ : Fin 354 => ZeroPadding.pad R ([] : List Bool)) = fun _ => List.replicate R false := by
    funext i
    simp [ZeroPadding.pad]
  refine ⟨_, (hF.pad (fun _ => R)).congr_in rfl ?_, ?_, ?_, ?_⟩
  · rw [← entry_eq]
    refine (PCJ6e421fabe2aa4155_SourceReuse.pad_install descSlots (fun _ => R) (fun _ => [])
      (desc q (bitmap (pcpp.systematicSupport idx)))).trans ?_
    show install descSlots (fun _ => ZeroPadding.pad R []) _ = _
    rw [hnil]
  · show ZeroPadding.pad R (F outN) = _
    rw [hN]
    rfl
  · show ZeroPadding.pad R (F outS) = _
    rw [hS]
    rfl
  · show ZeroPadding.pad R (F outT) = ZeroPadding.pad R (RepairOrdinary.frame [])
    rw [hT, ← ThrSwitch.frame_nil_pad R hR]
    simp [ZeroPadding.pad]

end normal
end NearCubicWires.SourceRequest.SymSystematic

