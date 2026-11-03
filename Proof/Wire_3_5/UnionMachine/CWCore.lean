import Proof.Wire_3_5.UnionMachine.CWRoundB
import Proof.PCP.PCPTraversalWhole
import Proof.MachineModel.BlockUnaryCalc
import Proof.Amplification.RecoveryScratchErase

/-! # C6 front, U5, the code writers: the carrier core

"It then selects the common star translation, constructs the shared coordinate filters" (P3:3673-3674): each call
names its carriers by their codes, and a carrier is "the union of a named variable's atoms' bottom gates" (P3:3401-3410)
with the code "the balanced list of atom codes" (`Stars.Carrier.code`, P3:3071-3094). This module assembles the
carrier writer's core machine from the two loops and base's balanced-list serializer:
* the input's length `1^|u|` and the circuit count `false :: 1^c` (`CWWords.lenW`, `countW`);
* base's polynomial `1^T`, `T = C₀·(|u|+1)^24` (`BlockPlatform.UnaryCalc.poly_step`), the loops' capacity;
* loop A (`CWRoundA.foldA`): every circuit's bottoms, then loop B (`CWRoundB.foldB`): every bottom's atom code;
* base's balanced-list serializer (`PCPTraversal`, run after one head move, rewound): the code of the list;
* the `natWord` writer (`CWWords.natW`) on the output tape.

This file: the serializer and the count accumulator's init as Steps (`serStage`, `initNStage`).

Paper quantity of the main types: the balanced list code of the bottoms' atom codes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWCore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.WireExponent3_5.PrimT (emitW)
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready FrontKit.ready_of_step)

/-! ## The serializer -/

/-- One head move on the count tape, then base's balanced-list serializer, all heads rewound. -/
noncomputable def serM :=
  Rewind.machine (Composition.machine (CompetitorCountTable.moveMachine (2 : Fin 128)) PCPTraversal.machine)

/-- The serializer's entry bank: the framed fields, the count word, the log. -/
def serIn (G : List Bool) (N : ℕ) : Fin 129 → List Bool :=
  Fin.addCases (m := 128) (n := 1) (motive := fun _ => List Bool) (PCPTraversal.input G N) (fun _ => [])

theorem stream_eq (gs : List (List Bool)) : RepairSource.ProjectionNormalization.FieldList.stream gs = gs.flatMap frame := by
  simp [RepairSource.ProjectionNormalization.FieldList.stream, List.flatMap]

def serCost (gs : List (List Bool)) : ℕ := 2 * (1 + 1 + PCPTraversal.budget (PCPSerializerMass.mass gs)) + 2

/-- **The serializer as a Step**: the balanced list code of the fields' values, framed, on tape `77`. -/
theorem serStage (gs : List (List Bool)) : ∃ o : Fin 129 → List Bool,
    Step serM (serCost gs) (fun _ => 0) (serIn (gs.flatMap frame) gs.length) (fun _ => 0) o ∧
    o 0 = gs.flatMap frame ∧ o 2 = CompareMachine.word gs.length ∧
    o 77 = ZeroPadding.pad (PCPPairReusable.capacity (PCPSerializerMass.mass gs)) (frame (PCPTraversal.code gs).bits) := by
  obtain ⟨r1, hr1, h1, t1, -⟩ := CompetitorCountTable.move_run (2 : Fin 128) (fun _ => 0)
    (PCPTraversal.input (gs.flatMap frame) gs.length)
  have st1 : Step (CompetitorCountTable.moveMachine (2 : Fin 128)) 1 (fun _ => 0)
      (PCPTraversal.input (gs.flatMap frame) gs.length) (PCPTraversal.heads 0)
      (PCPTraversal.input (gs.flatMap frame) gs.length) := by
    refine Step.of_run hr1 ?_ t1
    rw [h1]; funext i; unfold PCPTraversal.heads
    by_cases h2 : i = 2 <;> by_cases h0 : i = 0 <;> simp_all
  obtain ⟨rc, hrc, c77, c78, c0, c2, -, -, -⟩ := PCPTraversal.cold_run [] gs []
  have e0 : ([] : List Bool) ++ RepairSource.ProjectionNormalization.FieldList.stream gs ++ [] = gs.flatMap frame := by rw [stream_eq]; simp
  rw [e0] at hrc c0
  have st2 : Step PCPTraversal.machine (PCPTraversal.budget (PCPSerializerMass.mass gs)) (PCPTraversal.heads 0)
      (PCPTraversal.input (gs.flatMap frame) gs.length) rc.final.heads rc.final.tapes :=
    Step.of_run hrc rfl rfl
  obtain ⟨r, hr, -, ht, -⟩ := st1.seq st2
  obtain ⟨r', hr', ht', hh', hs', -⟩ := Rewind.reset_run _ _ (PCPTraversal.input (gs.flatMap frame) gs.length) r hr
  have steps : r.steps ≤ 1 + 1 + PCPTraversal.budget (PCPSerializerMass.mass gs) := by
    exact runFrom_steps_le _ _ _ r hr
  refine ⟨r'.final.tapes, (Step.of_run hr' (funext hh') rfl).enlarge (by unfold serCost; omega), ?_, ?_, ?_⟩
  · rw [show (0 : Fin 129) = Fin.castAdd 1 (0 : Fin 128) from rfl, ht', ht, c0]
  · rw [show (2 : Fin 129) = Fin.castAdd 1 (2 : Fin 128) from rfl, ht', ht, c2]
  · rw [show (77 : Fin 129) = Fin.castAdd 1 (77 : Fin 128) from rfl, ht', ht, c77]

/-! ## The count accumulator's init -/

/-- Writes `[false]` on an empty stream. -/
def initNW : WM 0 0 := emitW 0 false

def σI : WState 0 0 := ⟨fun _ => 0, fun _ => [], fun r => r.elim0, false⟩

def initNIn : Fin 3 → List Bool :=
  Fin.addCases (m := 0 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 σI).A (fun _ => [])

theorem initNIn_val (j : Fin 3) : initNIn j = if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

theorem initNStage : ∃ o : Fin 3 → List Bool,
    Step (Rewind.machine initNW.toProg.compile) (2 * 3 + 2) (fun _ => 0) initNIn (fun _ => 0) o ∧
    o 0 = [false] ∧ o 1 = [false] := by
  obtain ⟨τ, hw, e0, -, -, -, ec⟩ := NearCubicWires.WireExponent3_5.PrimT.emit_facts 0 (0 : Fin 1) false σI rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 initNW σI τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_⟩
  · rw [show (0 : Fin 3) = Fin.castAdd 1 (0 : Fin 2) from rfl, ho]; exact e0
  · rw [show (1 : Fin 3) = Fin.castAdd 1 (1 : Fin 2) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl


/-! ## The core machine's layout (913 tapes)

`0` the input `frame u`, `1` the output, `2` the cell, `3` the ruler `1^|u|`, `4` its log, `5` the circuit count,
`6`, `7` the count's ruler and log, `8..68` the polynomial's tapes (its output `1^T` on `58`), `69` the count
accumulator, `70` its log, `71` loop A's counter, `72` the bottom accumulator, `73..491` loop A's scratch, `492` the
loops' capacity tape, `493` loop B's counter, `494` the atom-code accumulator, `495..783` loop B's scratch, `784..910` the
serializer's tapes (its framed code on `859`), `911`, `912` the `natWord` writer's ruler and log. -/

def cellSl : Fin 1 → Fin 913 := fun _ => 2
def lenSl : Fin 4 → Fin 913 := ![0, 2, 3, 4]
def cntSl : Fin 5 → Fin 913 := ![0, 2, 5, 6, 7]
def polySl (j : Fin 62) : Fin 913 := ⟨if j.val = 0 then 3 else j.val + 7, by split_ifs <;> omega⟩
def initSl : Fin 3 → Fin 913 := ![69, 2, 70]
def erASl (j : Fin (420 + 1 + 1)) : Fin 913 :=
  ⟨if j.val = 0 then 71 else if j.val < 420 then j.val + 72 else if j.val = 420 then 58 else 492, by split_ifs <;> omega⟩
def foldASl (j : Fin (423 + 2 + 1)) : Fin 913 :=
  ⟨if j.val = 0 then 0 else if j.val = 1 then 71 else if j.val = 2 then 72 else if j.val = 3 then 69
    else if j.val < 423 then j.val + 69 else if j.val = 423 then 58 else if j.val = 424 then 492 else 5,
    by split_ifs <;> omega⟩
def erBSl (j : Fin (290 + 1 + 1)) : Fin 913 :=
  ⟨if j.val = 0 then 493 else if j.val < 290 then j.val + 494 else if j.val = 290 then 58 else 492, by split_ifs <;> omega⟩
def foldBSl (j : Fin (292 + 2 + 1)) : Fin 913 :=
  ⟨if j.val = 0 then 72 else if j.val = 1 then 493 else if j.val = 2 then 494
    else if j.val < 292 then j.val + 492 else if j.val = 292 then 58 else if j.val = 293 then 492 else 69,
    by split_ifs <;> omega⟩
def serSl (j : Fin 129) : Fin 913 :=
  ⟨if j.val = 0 then 494 else if j.val = 2 then 69 else if j.val = 1 then 784 else j.val + 782, by split_ifs <;> omega⟩
def natSl : Fin 5 → Fin 913 := ![859, 2, 1, 911, 912]

theorem cellSl_inj : Function.Injective cellSl := fun a b _ => Subsingleton.elim a b
theorem lenSl_inj : Function.Injective lenSl := by decide
theorem cntSl_inj : Function.Injective cntSl := by decide
theorem initSl_inj : Function.Injective initSl := by decide
theorem natSl_inj : Function.Injective natSl := by decide
theorem polySl_inj : Function.Injective polySl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [polySl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem erASl_inj : Function.Injective erASl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [erASl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem foldASl_inj : Function.Injective foldASl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [foldASl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem erBSl_inj : Function.Injective erBSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [erBSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem foldBSl_inj : Function.Injective foldBSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [foldBSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem serSl_inj : Function.Injective serSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [serSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega

theorem lenSl_val (j : Fin 4) : (lenSl j).val = [0, 2, 3, 4].getD j.val 0 := by fin_cases j <;> rfl
theorem cntSl_val (j : Fin 5) : (cntSl j).val = [0, 2, 5, 6, 7].getD j.val 0 := by fin_cases j <;> rfl
theorem initSl_val (j : Fin 3) : (initSl j).val = [69, 2, 70].getD j.val 0 := by fin_cases j <;> rfl
theorem natSl_val (j : Fin 5) : (natSl j).val = [859, 2, 1, 911, 912].getD j.val 0 := by fin_cases j <;> rfl

/-! ## Misses -/

section Miss
variable (A : Fin 913 → List Bool) (t : Fin 913)

theorem miss_cell (h : t.val ≠ 2) (o : Fin 1 → List Bool) : install cellSl A o t = A t :=
  install_other _ _ _ _ (fun _ e => h (by rw [← e]; rfl))
theorem miss_len (h : t.val ≠ 0 ∧ t.val ≠ 2 ∧ t.val ≠ 3 ∧ t.val ≠ 4) (o : Fin 4 → List Bool) : install lenSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [lenSl_val] at hv; fin_cases j <;> simp at hv <;> omega)
theorem miss_cnt (h : t.val ≠ 0 ∧ t.val ≠ 2 ∧ t.val ≠ 5 ∧ t.val ≠ 6 ∧ t.val ≠ 7) (o : Fin 5 → List Bool) :
    install cntSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [cntSl_val] at hv; fin_cases j <;> simp at hv <;> omega)
theorem miss_poly (h : t.val ≠ 3 ∧ (t.val < 8 ∨ 69 ≤ t.val)) (o : Fin 62 → List Bool) : install polySl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [polySl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_init (h : t.val ≠ 69 ∧ t.val ≠ 2 ∧ t.val ≠ 70) (o : Fin 3 → List Bool) : install initSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [initSl_val] at hv; fin_cases j <;> simp at hv <;> omega)
theorem miss_erA (h : t.val ≠ 71 ∧ t.val ≠ 58 ∧ t.val ≠ 492 ∧ (t.val < 73 ∨ 492 ≤ t.val))
    (o : Fin (420 + 1 + 1) → List Bool) : install erASl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [erASl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_foldA (h : t.val ≠ 0 ∧ t.val ≠ 5 ∧ t.val ≠ 58 ∧ t.val ≠ 69 ∧ t.val ≠ 492 ∧ (t.val < 71 ∨ 492 ≤ t.val))
    (o : Fin (423 + 2 + 1) → List Bool) : install foldASl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [foldASl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_erB (h : t.val ≠ 493 ∧ t.val ≠ 58 ∧ t.val ≠ 492 ∧ (t.val < 495 ∨ 784 ≤ t.val))
    (o : Fin (290 + 1 + 1) → List Bool) : install erBSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [erBSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_foldB (h : t.val ≠ 72 ∧ t.val ≠ 58 ∧ t.val ≠ 69 ∧ t.val ≠ 492 ∧ (t.val < 493 ∨ 784 ≤ t.val))
    (o : Fin (292 + 2 + 1) → List Bool) : install foldBSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [foldBSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_ser (h : t.val ≠ 494 ∧ t.val ≠ 69 ∧ (t.val < 784 ∨ 911 ≤ t.val)) (o : Fin 129 → List Bool) :
    install serSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [serSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_nat (h : t.val ≠ 859 ∧ t.val ≠ 2 ∧ t.val ≠ 1 ∧ t.val ≠ 911 ∧ t.val ≠ 912) (o : Fin 5 → List Bool) :
    install natSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [natSl_val] at hv; fin_cases j <;> simp at hv <;> omega)

end Miss


/-! ## The erase's banks -/

/-- The erase's entry: `t` blank scratch tapes, the driver `1^T`, the capacity tape `0^c`. -/
def erIn (t T c : ℕ) : Fin (t + 1 + 1) → List Bool :=
  Fin.addCases (m := t + 1) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := t) (n := 1) (motive := fun _ => List Bool) (fun _ => ([] : List Bool))
      (fun _ => List.replicate T true)) (fun _ => List.replicate c false)
def erOut (t T c : ℕ) : Fin (t + 1 + 1) → List Bool :=
  Fin.addCases (m := t + 1) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := t) (n := 1) (motive := fun _ => List Bool) (fun _ => List.replicate T false)
      (fun _ => List.replicate T true)) (fun _ => List.replicate (max c (T + 1)) false)

theorem erIn_val (t T c : ℕ) (j : Fin (t + 1 + 1)) :
    erIn t T c j = if j.val < t then [] else if j.val = t then List.replicate T true else List.replicate c false := by
  refine Fin.addCases (m := t + 1) (n := 1) (fun a => ?_) (fun b => ?_) j
  · refine Fin.addCases (m := t) (n := 1) (fun a' => ?_) (fun b' => ?_) a
    · simp only [erIn, Fin.addCases_left]; rw [if_pos (by simp)]
    · simp only [erIn, Fin.addCases_left, Fin.addCases_right]; rw [if_neg (by simp), if_pos (by simp)]
  · simp only [erIn, Fin.addCases_right]; rw [if_neg (by simp), if_neg (by simp)]

theorem erOut_val (t T c : ℕ) (j : Fin (t + 1 + 1)) :
    erOut t T c j = if j.val < t then List.replicate T false else if j.val = t then List.replicate T true
      else List.replicate (max c (T + 1)) false := by
  refine Fin.addCases (m := t + 1) (n := 1) (fun a => ?_) (fun b => ?_) j
  · refine Fin.addCases (m := t) (n := 1) (fun a' => ?_) (fun b' => ?_) a
    · simp only [erOut, Fin.addCases_left]; rw [if_pos (by simp)]
    · simp only [erOut, Fin.addCases_left, Fin.addCases_right]; rw [if_neg (by simp), if_pos (by simp)]
  · simp only [erOut, Fin.addCases_right]; rw [if_neg (by simp), if_neg (by simp)]

theorem erase_step (t T c : ℕ) :
    Step (RecoveryScratchErase.resetMachine t) (2 * T + 4) (fun _ => 0) (erIn t T c) (fun _ => 0) (erOut t T c) := by
  obtain ⟨re, hre, hte, hhe, hse⟩ := RecoveryScratchErase.erase_ready T c (fun _ : Fin t => ([] : List Bool))
    (fun _ => Nat.zero_le _)
  exact FrontLoopKit.step_of_ready ⟨re, hre, hte, hhe, hse.le⟩

/-! ## The loops' banks -/

open NearCubicWires.WireExponent3_5.Transfer

theorem addCases_val {m k : ℕ} {β : Type} (f : Fin m → β) (g : Fin k → β) (j : Fin (m + k)) :
    Fin.addCases (motive := fun _ => β) f g j = if h : j.val < m then f ⟨j.val, h⟩ else g ⟨j.val - m, by omega⟩ := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · simp [a.isLt]
  · simp

/-- Loop A's bank at circuit `i`, by tape. -/
theorem foldBankA_val (xs : List ℕ) (T i c : ℕ) (j : Fin (423 + 2 + 1)) :
    Fin.addCases (m := 423 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch CWRoundA.scrA T (CWRoundA.Qa xs T i)) T (T + 1)) (fun _ => CompareMachine.word c) j =
    if j.val = 0 then (xs.map nf).flatten ++ [false]
    else if j.val = 1 then ZeroPadding.pad T (List.replicate i true)
    else if j.val = 2 then (CWRoundA.bacc xs i).flatMap frame
    else if j.val = 3 then false :: List.replicate (CWRoundA.bacc xs i).length true
    else if j.val < 423 then List.replicate T false
    else if j.val = 423 then List.replicate T true
    else if j.val = 424 then List.replicate (T + 1) false
    else CompareMachine.word c := by
  rw [addCases_val]
  by_cases h1 : j.val < 423 + 2
  · rw [dif_pos h1]; unfold roundTapes; rw [addCases_val]
    by_cases h2 : j.val < 423
    · rw [dif_pos h2]
      unfold padScratch scratchCap
      by_cases h3 : 4 ≤ j.val
      · rw [if_pos ((CWRoundA.scrA_iff ⟨j.val, h2⟩).mpr h3)]
        simp only [CWRoundA.Qa, CWRoundA.roundAIn]
        have e0 : j.val ≠ 0 := by omega
        have e1 : j.val ≠ 1 := by omega
        have e2 : j.val ≠ 2 := by omega
        have e3 : j.val ≠ 3 := by omega
        simp [e0, e1, e2, e3, h2, ZeroPadding.pad]
      · rw [if_neg (fun hh => h3 ((CWRoundA.scrA_iff ⟨j.val, h2⟩).mp hh))]
        simp only [CWRoundA.Qa, CWRoundA.roundAIn, ZeroPadding.pad_zero]
        have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
        rcases this with e | e | e | e <;> simp [e]
    · rw [dif_neg h2]
      have : j.val = 423 ∨ j.val = 424 := by omega
      rcases this with e | e <;> simp [e]
  · rw [dif_neg h1]
    have e : j.val = 425 := by omega
    simp [e]

/-- Loop B's bank at bottom `j`, by tape. -/
theorem foldBankB_val (ys : List (List Bool)) (T i c : ℕ) (j : Fin (292 + 2 + 1)) :
    Fin.addCases (m := 292 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch CWRoundB.scrB T (CWRoundB.Qb ys T i)) T (T + 1)) (fun _ => CompareMachine.word c) j =
    if j.val = 0 then ys.flatMap frame
    else if j.val = 1 then ZeroPadding.pad T (List.replicate i true)
    else if j.val = 2 then (CWRoundB.gacc ys i).flatMap frame
    else if j.val < 292 then List.replicate T false
    else if j.val = 292 then List.replicate T true
    else if j.val = 293 then List.replicate (T + 1) false
    else CompareMachine.word c := by
  rw [addCases_val]
  by_cases h1 : j.val < 292 + 2
  · rw [dif_pos h1]; unfold roundTapes; rw [addCases_val]
    by_cases h2 : j.val < 292
    · rw [dif_pos h2]
      unfold padScratch scratchCap
      by_cases h3 : 3 ≤ j.val
      · rw [if_pos ((CWRoundB.scrB_iff ⟨j.val, h2⟩).mpr h3)]
        simp only [CWRoundB.Qb, CWRoundB.roundBIn]
        have e0 : j.val ≠ 0 := by omega
        have e1 : j.val ≠ 1 := by omega
        have e2 : j.val ≠ 2 := by omega
        simp [e0, e1, e2, h2, ZeroPadding.pad]
      · rw [if_neg (fun hh => h3 ((CWRoundB.scrB_iff ⟨j.val, h2⟩).mp hh))]
        simp only [CWRoundB.Qb, CWRoundB.roundBIn, ZeroPadding.pad_zero]
        have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
        rcases this with e | e | e <;> simp [e]
    · rw [dif_neg h2]
      have : j.val = 292 ∨ j.val = 293 := by omega
      rcases this with e | e <;> simp [e]
  · rw [dif_neg h1]
    have e : j.val = 294 := by omega
    simp [e]

end NearCubicWires.WireExponent3_5.UnionMachine.CWCore
