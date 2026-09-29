import Proof.Wire_3_5.UnionMachine.CWCoreT
import Proof.Wire_3_5.UnionMachine.CWMain

/-! # C6 front, U5, the code writers: the `THR∘THR` carrier core's run

The `THR∘THR` carrier core (`coreTM`, 1233 tapes; layout in `CWCoreT`) is FP's carrier core (`CWMain.coreM`) with loop
A replaced by the `THR∘THR` loop (`CWRoundT.foldT`): from `frame u` on tape `0` (`u = (xs.map natWord).flatten`) it
runs the cell, the ruler `1^|u|`, the circuit count, the capacity `1^T` (FP's `T = C₀·(|u|+1)^24`), the count
accumulator, the erase and the `THR∘THR` loop (every circuit's RETAINED bottoms), the erase and loop B (every retained
bottom's atom code), the serializer and the `natWord` writer. **`coreT_step`**: the output tape holds
`frame (natWord (PCPTraversal.code (codesT xs)))`, the input is kept, every head returns to `0`.

Paper quantity of the main type: the balanced list code of the atom codes of the circuits' charged gates, the carrier
code of `P3:3071-3094` for a list of `THR∘THR` circuits (the bridge is `CWThr`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWMainT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords NearCubicWires.WireExponent3_5.UnionMachine.CWCoreT
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (serM serIn serCost serStage initNW initNIn initNIn_val initNStage erIn erOut
  erIn_val erOut_val erase_step foldBankB_val)
open NearCubicWires.WireExponent3_5.UnionMachine.CWMain (C0 cap serIn_val polyIn_val)
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready FrontKit.ready_of_step)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.WireExponent3_5.Transfer

/-! ## The machine -/

noncomputable def cellC := RecoveryFocus.machine cellSl NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def lenC := RecoveryFocus.machine lenSl (Rewind.machine lenW.toProg.compile)
noncomputable def cntC := RecoveryFocus.machine cntSl (Rewind.machine countW.toProg.compile)
noncomputable def polyC := RecoveryFocus.machine polySl (PCPSerializerCapacity.Power.machine 24 C0)
noncomputable def initC := RecoveryFocus.machine initSl (Rewind.machine initNW.toProg.compile)
noncomputable def erAC := RecoveryFocus.machine erTSl (RecoveryScratchErase.resetMachine 740)
noncomputable def foldAC := RecoveryFocus.machine foldTSl CWRoundT.foldT
noncomputable def erBC := RecoveryFocus.machine erBSl (RecoveryScratchErase.resetMachine 290)
noncomputable def foldBC := RecoveryFocus.machine foldBSl CWRoundB.foldB
noncomputable def serC := RecoveryFocus.machine serSl serM
noncomputable def natC := RecoveryFocus.machine natSl (Rewind.machine natW.toProg.compile)

/-- **The `THR∘THR` carrier writer's core machine.** -/
noncomputable def coreTM :=
  Composition.machine cellC (Composition.machine lenC (Composition.machine cntC (Composition.machine polyC
    (Composition.machine initC (Composition.machine erAC (Composition.machine foldAC (Composition.machine erBC
      (Composition.machine foldBC (Composition.machine serC natC)))))))))

/-- The core machine's entry: `frame u` on tape `0`, every other tape blank. -/
def coreTIn (u : List Bool) : Fin 1233 → List Bool := fun t => if t.val = 0 then frame u else []

/-! ## The quantities -/

/-- The bottoms of all circuits (unfiltered, FP's). -/
def bots (xs : List ℕ) : List (List Bool) := CWRoundA.bacc xs xs.length

/-- The retained bottoms of all circuits. -/
def botsT (xs : List ℕ) : List (List Bool) := CWRoundT.bacT xs xs.length

/-- The atom codes of all retained bottoms, in canonical binary. -/
def codesT (xs : List ℕ) : List (List Bool) := CWRoundB.gacc (botsT xs) (botsT xs).length

/-- **What the capacity must dominate.** -/
structure CapsT (xs : List ℕ) (T : ℕ) : Prop where
  w : ∀ x ∈ xs, natBitLength x ≤ ((xs.map natWord).flatten).length
  wy : ∀ y ∈ botsT xs, y.length ≤ ((xs.map natWord).flatten).length
  a1 : xs.length ≤ T
  a2 : ((xs.map nf).flatten ++ [false]).length ≤ T
  a3 : ((bots xs).flatMap frame).length ≤ T
  a4 : (bots xs).length + 1 ≤ T
  a5 : CWRoundT.foldCwT ((xs.map natWord).flatten).length xs.length ((bots xs).flatMap frame).length
    (bots xs).length + 1 ≤ T
  b3 : ((codesT xs).flatMap frame).length ≤ T
  b4 : CWRoundB.foldCwB ((xs.map natWord).flatten).length (botsT xs).length ((codesT xs).flatMap frame).length + 1 ≤ T

/-- The core's fuel. -/
noncomputable def coreTCost (xs : List ℕ) : ℕ :=
  let n := ((xs.map natWord).flatten).length
  let T := cap n
  1 + 1 + ((2 * (n * 9 + 1) + 2) + 1 + ((2 * (xs.length * (18 * n + 16) + 5) + 2) + 1 +
    (PCPSerializerCapacity.Power.budget 24 C0 n + 1 + ((2 * 3 + 2) + 1 + ((2 * T + 4) + 1 +
      ((1 + 1 + (xs.length * (CWRoundT.foldCwT n xs.length ((bots xs).flatMap frame).length (bots xs).length + 1 +
        (2 * T + 4 + 1 + 0) + 2) + xs.length + 3 + 1 + 1)) + 1 + ((2 * T + 4) + 1 +
      ((1 + 1 + ((botsT xs).length * (CWRoundB.foldCwB n (botsT xs).length ((codesT xs).flatMap frame).length + 1 +
        (2 * T + 4 + 1 + 0) + 2) + (botsT xs).length + 3 + 1 + 1)) + 1 +
      (serCost (codesT xs) + 1 + (2 * natCost (PCPTraversal.code (codesT xs)) + 2))))))))))

/-! ## The loops' entries -/

theorem foldT_entry (xs : List ℕ) (T c : ℕ) (B : Fin 1233 → List Bool) (hIn : B 0 = (xs.map nf).flatten ++ [false])
    (hK : B 71 = List.replicate T false) (hB : B 72 = []) (hN : B 69 = [false])
    (hscr : ∀ t : Fin 1233, 73 ≤ t.val → t.val ≤ 491 → B t = List.replicate T false)
    (hscr2 : ∀ t : Fin 1233, 913 ≤ t.val → B t = List.replicate T false)
    (hT : B 58 = List.replicate T true) (hC : B 492 = List.replicate (T + 1) false) (hW : B 5 = CompareMachine.word c)
    (j : Fin (743 + 2 + 1)) :
    B (foldTSl j) = Fin.addCases (m := 743 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch CWRoundT.scrT T (CWRoundT.Qt xs T 0)) T (T + 1)) (fun _ => CompareMachine.word c) j := by
  rw [foldBankT_val]
  have hj := j.isLt
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show foldTSl j = (0 : Fin 1233) from Fin.ext (by simp [foldTSl, h0]), hIn]
  rw [if_neg h0]
  by_cases h1 : j.val = 1
  · rw [if_pos h1, show foldTSl j = (71 : Fin 1233) from Fin.ext (by simp [foldTSl, h1]), hK]
    simp [ZeroPadding.pad]
  rw [if_neg h1]
  by_cases h2 : j.val = 2
  · rw [if_pos h2, show foldTSl j = (72 : Fin 1233) from Fin.ext (by simp [foldTSl, h2]), hB]
    simp [CWRoundT.bacT]
  rw [if_neg h2]
  by_cases h3 : j.val = 3
  · rw [if_pos h3, show foldTSl j = (69 : Fin 1233) from Fin.ext (by simp [foldTSl, h3]), hN]
    simp [CWRoundT.bacT]
  rw [if_neg h3]
  by_cases h4 : j.val < 423
  · rw [if_pos (by omega), hscr _ (by simp only [foldTSl]; split_ifs; omega) (by simp only [foldTSl]; split_ifs; omega)]
  by_cases h4' : j.val < 743
  · rw [if_pos h4', hscr2 _ (by simp only [foldTSl]; split_ifs <;> omega)]
  rw [if_neg h4']
  by_cases h5 : j.val = 743
  · rw [if_pos h5, show foldTSl j = (58 : Fin 1233) from Fin.ext (by simp [foldTSl, h5]), hT]
  rw [if_neg h5]
  by_cases h6 : j.val = 744
  · rw [if_pos h6, show foldTSl j = (492 : Fin 1233) from Fin.ext (by simp [foldTSl, h6]), hC]
  rw [if_neg h6, show foldTSl j = (5 : Fin 1233) from Fin.ext (by simp only [foldTSl]; split_ifs <;> omega), hW]

theorem foldB_entryT (ys : List (List Bool)) (T c : ℕ) (B : Fin 1233 → List Bool) (hIn : B 72 = ys.flatMap frame)
    (hK : B 493 = List.replicate T false) (hG : B 494 = [])
    (hscr : ∀ t : Fin 1233, 495 ≤ t.val → t.val ≤ 783 → B t = List.replicate T false)
    (hT : B 58 = List.replicate T true) (hC : B 492 = List.replicate (T + 1) false) (hW : B 69 = CompareMachine.word c)
    (j : Fin (292 + 2 + 1)) :
    B (foldBSl j) = Fin.addCases (m := 292 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch CWRoundB.scrB T (CWRoundB.Qb ys T 0)) T (T + 1)) (fun _ => CompareMachine.word c) j := by
  rw [foldBankB_val]
  have hj := j.isLt
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show foldBSl j = (72 : Fin 1233) from Fin.ext (by simp [foldBSl, h0]), hIn]
  rw [if_neg h0]
  by_cases h1 : j.val = 1
  · rw [if_pos h1, show foldBSl j = (493 : Fin 1233) from Fin.ext (by simp [foldBSl, h1]), hK]
    simp [ZeroPadding.pad]
  rw [if_neg h1]
  by_cases h2 : j.val = 2
  · rw [if_pos h2, show foldBSl j = (494 : Fin 1233) from Fin.ext (by simp [foldBSl, h2]), hG]
    simp [CWRoundB.gacc]
  rw [if_neg h2]
  by_cases h4 : j.val < 292
  · rw [if_pos h4, hscr _ (by simp only [foldBSl]; split_ifs; omega) (by simp only [foldBSl]; split_ifs; omega)]
  rw [if_neg h4]
  by_cases h5 : j.val = 292
  · rw [if_pos h5, show foldBSl j = (58 : Fin 1233) from Fin.ext (by simp [foldBSl, h5]), hT]
  rw [if_neg h5]
  by_cases h6 : j.val = 293
  · rw [if_pos h6, show foldBSl j = (492 : Fin 1233) from Fin.ext (by simp [foldBSl, h6]), hC]
  rw [if_neg h6, show foldBSl j = (69 : Fin 1233) from Fin.ext (by simp only [foldBSl]; split_ifs; omega), hW]

/-! ## The run -/

/-- **The `THR∘THR` carrier writer's core run.** -/
theorem coreT_step (xs : List ℕ) (hsel : ∀ x ∈ xs, (CWRoundT.sels x).length = (CWRoundA.bw x).length)
    (hc : CapsT xs (cap ((xs.map natWord).flatten).length)) :
    ∃ tout : Fin 1233 → List Bool,
      Step coreTM (coreTCost xs) (fun _ => 0) (coreTIn (xs.map natWord).flatten) (fun _ => 0) tout ∧
      tout 0 = frame (xs.map natWord).flatten ∧
      tout 1 = frame (natWord (PCPTraversal.code (codesT xs))) := by
  set u := (xs.map natWord).flatten with hu
  set n := u.length with hn
  set T := cap n with hT
  have hS : frame u = (xs.map nf).flatten ++ [false] := frame_fields xs
  have zH : ∀ {t : ℕ} (sl : Fin t → Fin 1233), dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
    fun sl => dockH_existing sl _ _ (fun _ => rfl)
  set B0 := coreTIn u with hB0
  have b0 : ∀ t : Fin 1233, 1 ≤ t.val → B0 t = [] := fun t ht => by simp only [hB0, coreTIn]; rw [if_neg (by omega)]
  -- 1: the cell
  have d1 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock cellSl cellSl_inj (fun _ => 0) B0 (fun _ => rfl)
    (fun _ => b0 2 (by decide))
  rw [zH] at d1
  set B1 := install cellSl B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 1233, t.val ≠ 2 → B1 t = B0 t := fun t h => miss_cell B0 t h _
  have b12 : B1 2 = [false] := install_slot cellSl cellSl_inj _ _ 0
  -- 2: the ruler `1^|u|`
  obtain ⟨o2, s2, l0, l1, l2⟩ := lenStage u
  have d2 := s2.dock lenSl lenSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [lenIn_val]
    fin_cases j
    · show B1 0 = _; rw [b1 _ (by decide)]; simp [hB0, coreTIn]
    · show B1 2 = _; rw [b12]; rfl
    · show B1 3 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 4 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl)
  rw [zH] at d2
  set B2 := install lenSl B1 o2 with hB2
  have b2 : ∀ t : Fin 1233, (t.val ≠ 0 ∧ t.val ≠ 2 ∧ t.val ≠ 3 ∧ t.val ≠ 4) → B2 t = B1 t := fun t h => miss_len B1 t h _
  have b2h : ∀ j, B2 (lenSl j) = o2 j := fun j => install_slot lenSl lenSl_inj B1 o2 j
  -- 3: the circuit count
  have hw := hc.w
  obtain ⟨o3, s3, k0, k1, k2, -⟩ := countStage xs n hw
  have d3 := s3.dock cntSl cntSl_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro j; rw [countIn_val]
    fin_cases j
    · show B2 0 = _; rw [show (0 : Fin 1233) = lenSl 0 from rfl, b2h, l0]; rfl
    · show B2 2 = _; rw [show (2 : Fin 1233) = lenSl 1 from rfl, b2h, l1]; rfl
    · show B2 5 = _; rw [b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B2 6 = _; rw [b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B2 7 = _; rw [b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl)
  rw [zH] at d3
  set B3 := install cntSl B2 o3 with hB3
  have b3 : ∀ t : Fin 1233, (t.val ≠ 0 ∧ t.val ≠ 2 ∧ t.val ≠ 5 ∧ t.val ≠ 6 ∧ t.val ≠ 7) → B3 t = B2 t :=
    fun t h => miss_cnt B2 t h _
  have b3h : ∀ j, B3 (cntSl j) = o3 j := fun j => install_slot cntSl cntSl_inj B2 o3 j
  -- 4: the capacity `1^T`
  obtain ⟨o4, s4, -, q4⟩ := BlockPlatform.UnaryCalc.poly_step 24 C0 n
  have d4 := s4.dock polySl polySl_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro j; rw [polyIn_val]
    by_cases h0 : j.val = 0
    · rw [if_pos h0, show polySl j = lenSl 2 from Fin.ext (by simp [polySl, h0]; rfl), b3 _ (by decide), b2h, l2]
    · rw [if_neg h0]
      have hj := j.isLt
      rw [b3 _ (by simp only [polySl, if_neg h0]; omega), b2 _ (by simp only [polySl, if_neg h0]; omega),
        b1 _ (by simp only [polySl, if_neg h0]; omega), b0 _ (by simp only [polySl, if_neg h0]; omega)])
  rw [zH] at d4
  set B4 := install polySl B3 o4 with hB4
  have b4 : ∀ t : Fin 1233, (t.val ≠ 3 ∧ (t.val < 8 ∨ 69 ≤ t.val)) → B4 t = B3 t := fun t h => miss_poly B3 t h _
  have b4T : B4 58 = List.replicate T true := (install_slot polySl polySl_inj B3 o4 51).trans q4
  -- 5: the count accumulator `[false]`
  obtain ⟨o5, s5, n0, n1⟩ := initNStage
  have d5 := s5.dock initSl initSl_inj (fun _ => 0) B4 (fun _ => rfl) (by
    intro j; rw [initNIn_val]
    fin_cases j
    · show B4 69 = _; rw [b4 _ (by decide), b3 _ (by decide), b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B4 2 = _; rw [b4 _ (by decide), show (2 : Fin 1233) = cntSl 1 from rfl, b3h, k1]; rfl
    · show B4 70 = _; rw [b4 _ (by decide), b3 _ (by decide), b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl)
  rw [zH] at d5
  set B5 := install initSl B4 o5 with hB5
  have b5 : ∀ t : Fin 1233, (t.val ≠ 69 ∧ t.val ≠ 2 ∧ t.val ≠ 70) → B5 t = B4 t := fun t h => miss_init B4 t h _
  have b5N : B5 69 = [false] := (install_slot initSl initSl_inj B4 o5 0).trans n0
  have b5C : B5 2 = [false] := (install_slot initSl initSl_inj B4 o5 1).trans n1
  -- the untouched region `71..`
  have fresh5 : ∀ t : Fin 1233, 71 ≤ t.val → B5 t = [] := by
    intro t ht
    rw [b5 _ (by omega), b4 _ (by omega), b3 _ (by omega), b2 _ (by omega), b1 _ (by omega), b0 _ (by omega)]
  have b5in : B5 0 = frame u := by
    rw [b5 _ (by decide), b4 _ (by decide), show (0 : Fin 1233) = cntSl 0 from rfl, b3h, k0]
  have b5cw : B5 5 = CompareMachine.word xs.length := by
    rw [b5 _ (by decide), b4 _ (by decide), show (5 : Fin 1233) = cntSl 2 from rfl, b3h, k2]; rfl
  -- 6: the loop's erase
  have d6 := (erase_step 740 T 0).dock erTSl erTSl_inj (fun _ => 0) B5 (fun _ => rfl) (by
    intro j; rw [erIn_val]
    have hj := j.isLt
    by_cases h1 : j.val < 740
    · rw [if_pos h1, fresh5 _ (by simp only [erTSl]; split_ifs <;> omega)]
    · rw [if_neg h1]
      by_cases h2 : j.val = 740
      · rw [if_pos h2, show erTSl j = (58 : Fin 1233) from Fin.ext (by simp [erTSl, h2]), b5 _ (by decide), b4T]
      · rw [if_neg h2, show erTSl j = (492 : Fin 1233) from Fin.ext (by simp only [erTSl]; split_ifs <;> omega),
          fresh5 _ (by decide)]; rfl)
  rw [zH] at d6
  set B6 := install erTSl B5 (erOut 740 T 0) with hB6
  have b6 : ∀ t : Fin 1233, (t.val ≠ 71 ∧ t.val ≠ 58 ∧ t.val ≠ 492 ∧ (t.val < 73 ∨ (492 ≤ t.val ∧ t.val < 913))) →
      B6 t = B5 t := fun t h => miss_erT B5 t h _
  have b6h : ∀ j, B6 (erTSl j) = erOut 740 T 0 j := fun j => install_slot erTSl erTSl_inj B5 _ j
  -- 7: the `THR∘THR` loop
  have fA := CWRoundT.foldT_run xs n hw hsel T (T + 1) (le_refl _) hc.a1 hc.a2 hc.a3 hc.a4 hc.a5
  have e6K : B6 71 = List.replicate T false := by
    rw [show (71 : Fin 1233) = erTSl 0 from rfl, b6h, erOut_val]; simp
  have e6scr : ∀ t : Fin 1233, 73 ≤ t.val → t.val ≤ 491 → B6 t = List.replicate T false := by
    intro t h1 h2
    rw [show t = erTSl ⟨t.val - 72, by omega⟩ from Fin.ext (by simp only [erTSl]; split_ifs <;> omega), b6h, erOut_val,
      if_pos (by simp; omega)]
  have e6scr2 : ∀ t : Fin 1233, 913 ≤ t.val → B6 t = List.replicate T false := by
    intro t h1
    have ht := t.isLt
    rw [show t = erTSl ⟨t.val - 493, by omega⟩ from Fin.ext (by simp only [erTSl]; split_ifs <;> omega), b6h,
      erOut_val, if_pos (by simp; omega)]
  have e6T : B6 58 = List.replicate T true := by
    rw [show (58 : Fin 1233) = erTSl 740 from rfl, b6h, erOut_val]; simp
  have e6C : B6 492 = List.replicate (T + 1) false := by
    rw [show (492 : Fin 1233) = erTSl 741 from rfl, b6h, erOut_val]; simp
  have d7 := (FrontLoopKit.step_of_ready fA).dock foldTSl foldTSl_inj (fun _ => 0) B6 (fun _ => rfl)
    (foldT_entry xs T xs.length B6 (by rw [b6 _ (by decide), b5in, hS]) e6K
      (by rw [b6 _ (by decide), fresh5 _ (by decide)]) (by rw [b6 _ (by decide), b5N]) e6scr e6scr2 e6T e6C
      (by rw [b6 _ (by decide), b5cw]))
  rw [zH] at d7
  set OA := Fin.addCases (m := 743 + 2) (n := 1) (motive := fun _ => List Bool)
    (roundTapes (padScratch CWRoundT.scrT T (CWRoundT.Qt xs T xs.length)) T (T + 1))
    (fun _ => CompareMachine.word xs.length) with hOA
  set B7 := install foldTSl B6 OA with hB7
  have b7 : ∀ t : Fin 1233, (t.val ≠ 0 ∧ t.val ≠ 5 ∧ t.val ≠ 58 ∧ t.val ≠ 69 ∧ t.val ≠ 492 ∧
      (t.val < 71 ∨ (492 ≤ t.val ∧ t.val < 913))) → B7 t = B6 t := fun t h => miss_foldT B6 t h _
  have b7h : ∀ j, B7 (foldTSl j) = OA j := fun j => install_slot foldTSl foldTSl_inj B6 OA j
  have b7B : B7 72 = (botsT xs).flatMap frame := by
    rw [show (72 : Fin 1233) = foldTSl 2 from rfl, b7h, hOA, foldBankT_val, if_neg (by decide), if_neg (by decide),
      if_pos (by decide)]; rfl
  have b7N : B7 69 = CompareMachine.word (botsT xs).length := by
    rw [show (69 : Fin 1233) = foldTSl 3 from rfl, b7h, hOA, foldBankT_val, if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_pos (by decide)]; rfl
  have b7T : B7 58 = List.replicate T true := by
    rw [show (58 : Fin 1233) = foldTSl 743 from rfl, b7h, hOA, foldBankT_val, if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  have b7C : B7 492 = List.replicate (T + 1) false := by
    rw [show (492 : Fin 1233) = foldTSl 744 from rfl, b7h, hOA, foldBankT_val, if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  have b7in : B7 0 = frame u := by
    rw [show (0 : Fin 1233) = foldTSl 0 from rfl, b7h, hOA, foldBankT_val, if_pos (by decide), hS]
  have fresh7 : ∀ t : Fin 1233, 493 ≤ t.val → t.val < 913 → B7 t = [] := by
    intro t ht ht'
    rw [b7 _ (by omega), b6 _ (by omega), fresh5 _ (by omega)]
  -- 8: loop B's erase
  have d8 := (erase_step 290 T (T + 1)).dock erBSl erBSl_inj (fun _ => 0) B7 (fun _ => rfl) (by
    intro j; rw [erIn_val]
    have hj := j.isLt
    by_cases h1 : j.val < 290
    · rw [if_pos h1, fresh7 _ (by simp only [erBSl]; split_ifs <;> omega) (by simp only [erBSl]; split_ifs <;> omega)]
    · rw [if_neg h1]
      by_cases h2 : j.val = 290
      · rw [if_pos h2, show erBSl j = (58 : Fin 1233) from Fin.ext (by simp [erBSl, h2]), b7T]
      · rw [if_neg h2, show erBSl j = (492 : Fin 1233) from Fin.ext (by simp only [erBSl]; split_ifs <;> omega), b7C])
  rw [zH] at d8
  set B8 := install erBSl B7 (erOut 290 T (T + 1)) with hB8
  have b8 : ∀ t : Fin 1233, (t.val ≠ 493 ∧ t.val ≠ 58 ∧ t.val ≠ 492 ∧ (t.val < 495 ∨ 784 ≤ t.val)) → B8 t = B7 t :=
    fun t h => miss_erB B7 t h _
  have b8h : ∀ j, B8 (erBSl j) = erOut 290 T (T + 1) j := fun j => install_slot erBSl erBSl_inj B7 _ j
  -- 9: loop B
  have hTB3 : ((botsT xs).flatMap frame).length ≤ T :=
    (CWRoundT.flat_sub_le (CWRoundT.bacT_sub xs hsel xs.length)).trans hc.a3
  have fB := CWRoundB.foldB_run n (botsT xs) hc.wy T (T + 1) (le_refl _) (by have := hc.a4; have := (CWRoundT.bacT_sub xs hsel xs.length).length_le; unfold bots at *; unfold botsT; omega) hTB3 hc.b3 hc.b4
  have e8K : B8 493 = List.replicate T false := by
    rw [show (493 : Fin 1233) = erBSl 0 from rfl, b8h, erOut_val]; simp
  have e8scr : ∀ t : Fin 1233, 495 ≤ t.val → t.val ≤ 783 → B8 t = List.replicate T false := by
    intro t h1 h2
    rw [show t = erBSl ⟨t.val - 494, by omega⟩ from Fin.ext (by simp only [erBSl]; split_ifs <;> omega), b8h, erOut_val,
      if_pos (by simp; omega)]
  have e8T : B8 58 = List.replicate T true := by
    rw [show (58 : Fin 1233) = erBSl 290 from rfl, b8h, erOut_val]; simp
  have e8C : B8 492 = List.replicate (T + 1) false := by
    rw [show (492 : Fin 1233) = erBSl 291 from rfl, b8h, erOut_val]; simp
  have d9 := (FrontLoopKit.step_of_ready fB).dock foldBSl foldBSl_inj (fun _ => 0) B8 (fun _ => rfl)
    (foldB_entryT (botsT xs) T (botsT xs).length B8 (by rw [b8 _ (by decide), b7B]) e8K
      (by rw [b8 _ (by decide), fresh7 _ (by decide) (by decide)]) e8scr e8T e8C (by rw [b8 _ (by decide), b7N]))
  rw [zH] at d9
  set OB := Fin.addCases (m := 292 + 2) (n := 1) (motive := fun _ => List Bool)
    (roundTapes (padScratch CWRoundB.scrB T (CWRoundB.Qb (botsT xs) T (botsT xs).length)) T (T + 1))
    (fun _ => CompareMachine.word (botsT xs).length) with hOB
  set B9 := install foldBSl B8 OB with hB9
  have b9 : ∀ t : Fin 1233, (t.val ≠ 72 ∧ t.val ≠ 58 ∧ t.val ≠ 69 ∧ t.val ≠ 492 ∧ (t.val < 493 ∨ 784 ≤ t.val)) →
      B9 t = B8 t := fun t h => miss_foldB B8 t h _
  have b9h : ∀ j, B9 (foldBSl j) = OB j := fun j => install_slot foldBSl foldBSl_inj B8 OB j
  have b9G : B9 494 = (codesT xs).flatMap frame := by
    rw [show (494 : Fin 1233) = foldBSl 2 from rfl, b9h, hOB, foldBankB_val, if_neg (by decide), if_neg (by decide),
      if_pos (by decide)]; rfl
  have b9N : B9 69 = CompareMachine.word (codesT xs).length := by
    rw [show (69 : Fin 1233) = foldBSl 294 from rfl, b9h, hOB, foldBankB_val, if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    simp [codesT, CWRoundB.gacc]
  have fresh9 : ∀ t : Fin 1233, 784 ≤ t.val → t.val < 913 → B9 t = [] := by
    intro t ht ht'
    rw [b9 _ (by omega), b8 _ (by omega), fresh7 _ (by omega) (by omega)]
  -- 10: the serializer
  obtain ⟨o10, s10, z0, z2, z77⟩ := serStage (codesT xs)
  have d10 := s10.dock serSl serSl_inj (fun _ => 0) B9 (fun _ => rfl) (by
    intro j; rw [serIn_val]
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · rw [if_pos h0, show serSl j = (494 : Fin 1233) from Fin.ext (by simp [serSl, h0]), b9G]
    · rw [if_neg h0]
      by_cases h2 : j.val = 2
      · rw [if_pos h2, show serSl j = (69 : Fin 1233) from Fin.ext (by simp [serSl, h2]), b9N]
      · rw [if_neg h2, fresh9 _ (by simp only [serSl]; split_ifs <;> omega) (by simp only [serSl]; split_ifs <;> omega)])
  rw [zH] at d10
  set B10 := install serSl B9 o10 with hB10
  have b10 : ∀ t : Fin 1233, (t.val ≠ 494 ∧ t.val ≠ 69 ∧ (t.val < 784 ∨ 911 ≤ t.val)) → B10 t = B9 t :=
    fun t h => miss_ser B9 t h _
  have b10F : B10 859 = ZeroPadding.pad (PCPPairReusable.capacity (PCPSerializerMass.mass (codesT xs)))
      (frame (PCPTraversal.code (codesT xs)).bits) := (install_slot serSl serSl_inj B9 o10 77).trans z77
  -- 11: the `natWord` writer
  have hpad : ZeroPadding.pad (PCPPairReusable.capacity (PCPSerializerMass.mass (codesT xs)))
      (frame (PCPTraversal.code (codesT xs)).bits) = frame (PCPTraversal.code (codesT xs)).bits ++
        List.replicate (PCPPairReusable.capacity (PCPSerializerMass.mass (codesT xs)) -
          (frame (PCPTraversal.code (codesT xs)).bits).length) false := rfl
  obtain ⟨o11, s11, w0, w1, w2⟩ := natStage (PCPTraversal.code (codesT xs)) (List.replicate
    (PCPPairReusable.capacity (PCPSerializerMass.mass (codesT xs)) - (frame (PCPTraversal.code (codesT xs)).bits).length) false)
  have d11 := s11.dock natSl natSl_inj (fun _ => 0) B10 (fun _ => rfl) (by
    intro j; rw [natIn_val]
    fin_cases j
    · show B10 859 = _; rw [b10F, hpad]; rfl
    · show B10 2 = _; rw [b10 _ (by decide), b9 _ (by decide), b8 _ (by decide), b7 _ (by decide), b6 _ (by decide),
        b5C]; rfl
    · show B10 1 = _; rw [b10 _ (by decide), b9 _ (by decide), b8 _ (by decide), b7 _ (by decide), b6 _ (by decide),
        b5 _ (by decide), b4 _ (by decide), b3 _ (by decide), b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B10 911 = _; rw [b10 _ (by decide), fresh9 _ (by decide) (by decide)]; rfl
    · show B10 912 = _; rw [b10 _ (by decide), fresh9 _ (by decide) (by decide)]; rfl)
  rw [zH] at d11
  set B11 := install natSl B10 o11 with hB11
  have b11 : ∀ t : Fin 1233, (t.val ≠ 859 ∧ t.val ≠ 2 ∧ t.val ≠ 1 ∧ t.val ≠ 911 ∧ t.val ≠ 912) → B11 t = B10 t :=
    fun t h => miss_nat B10 t h _
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq (d7.seq (d8.seq (d9.seq (d10.seq d11)))))))))
  have run' : Step coreTM _ (fun _ => 0) B0 (fun _ => 0) B11 := run
  refine ⟨B11, run'.enlarge (by unfold coreTCost; exact le_refl _), ?_, ?_⟩
  · rw [b11 _ (by decide), b10 _ (by decide), b9 _ (by decide), b8 _ (by decide), b7in]
  · exact (install_slot natSl natSl_inj B10 o11 2).trans w2

end NearCubicWires.WireExponent3_5.UnionMachine.CWMainT
