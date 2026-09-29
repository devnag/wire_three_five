import Proof.Wire_3_5.Primitive.SeedFix.CarTable
import Proof.SourceAssembly.SourceFactorSelRunBound

/-! # C6 front, the C1 dock: a carrier's native gate region (the carrier table, stages 1–7)

C1's request lists the carriers' gates (`Plan.selWord`, P3:1326-1330, 3673); a variable's carrier arrives as its code
`natWord (Carrier.code X)` (the writers' fold, `FrontFoldSem.crs_get`). The carrier table (`CarTable.carTableM`) decodes that code in ten stages; its first seven (the cell, the preparation, base's balanced-list traversal,
the capacity, the accumulator's header, the erase, the atom loop) leave the framed native gate words
`accHdr ++ tabSeg X` on tape `304`. This module runs exactly those seven stages (**`carPreM`**, the same docked
machines) and restates the proof up to that point (**`carPre_step`**, `carTable_step`'s lines for stages 1–7, the
arity tape `1^m` free). **`Step.len_le`**: every tape a step leaves is bounded by its entry and the fuel (base
`RunBound.runFrom_bound`).

Paper quantity of the main type: the carrier's gates (`tabSeg X`, its framed native gate words). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1CarPre
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.CarWM
open NearCubicWires.WireExponent3_5.PrimT.CarStages NearCubicWires.WireExponent3_5.PrimT.CarFold
open NearCubicWires.WireExponent3_5.PrimT.CarBounds NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.PrimT.CarTable
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-- **A step's tapes are bounded** by their entry lengths and the fuel. -/
theorem Step.len_le {t s : ℕ} {p : Machine t s} {n : ℕ} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step p n H A H' A') (i : Fin t) : (A' i).length ≤ max (A i).length (H i + n + 1) := by
  obtain ⟨r, hr, -, ht, -⟩ := h
  have hb := (SourceFactorSel.RunBound.runFrom_bound p n _ r hr i).2
  rw [ht] at hb
  exact hb

/-- **The carrier table's stages 1–7** (the docked machines). -/
noncomputable def carPreM :=
  Composition.machine cellC (Composition.machine prepC (Composition.machine ctC (Composition.machine powC
    (Composition.machine initC (Composition.machine eraseC foldC)))))

/-- The fuel of stages 1–7 (`carTableCost`'s prefix). -/
noncomputable def carPreCost {n : ℕ} (X : Stars.Carrier n) (m L : ℕ) : ℕ :=
  let W := natBitLength X.code
  let T := BlockPlatform.UnaryCalc.value 50 cC2 (W + 1)
  1 + 1 + ((2 * prepCost W m L + 2) + 1 + (CloseoutWitness.CanonicalTest.budget (binary W X.code) + 1 +
    (PCPSerializerCapacity.Power.budget 50 cC2 (W + 1) + 1 + ((2 * 15 + 2) + 1 + ((2 * T + 4) + 1 +
    (1 + 1 + (X.length * (foldCw W X.length (tabSeg X).length + 1 + (2 * T + 4 + 1 + 0) + 2) + X.length + 3 + 1 +
      1)))))))

/-- **The carrier's native gate region**: from `frame (natWord (Carrier.code X))`, `1^m`, `1^L` (every other tape
blank), stages 1–7 leave `accHdr ++ tabSeg X` on tape `304`, keep the code on tape `0`, and return every head to `0`. -/
theorem carPre_step {n : ℕ} (X : Stars.Carrier n) (m L : ℕ) :
    ∃ tout : Fin 1357 → List Bool,
      Step carPreM (carPreCost X m L) (fun _ => 0) (carIn X.code m L) (fun _ => 0) tout ∧
      tout 0 = frame (natWord X.code) ∧ tout 304 = accHdr ++ tabSeg X := by
  set code := X.code with hcode
  set W := natBitLength code with hWdef
  set bits := binary W code with hbits
  set T := BlockPlatform.UnaryCalc.value 50 cC2 (W + 1) with hT
  set c := X.length with hc
  have hcodeW : code < 2 ^ W := CompilerMachine.Pool.lt_pow_natBitLength code
  have hval : RadixSemantics.value bits = code := binary_value _ _ hcodeW
  have hatoms : (PCPPNativeCanonicalTree.tree code).atoms = X.map CarrierFormat.gateCode :=
    CarrierFormat.tree_atoms_code X
  have hW : ∀ g ∈ X, CarrierFormat.gateCode g < 2 ^ W := fun g hg =>
    SourceRequest.TermBridge.atom_lt W code _ hcodeW (by rw [hatoms]; exact List.mem_map_of_mem hg)
  have zH : ∀ {t : ℕ} (sl : Fin t → Fin 1357), dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
    fun sl => dockH_existing sl _ _ (fun _ => rfl)
  set B0 := carIn code m L with hB0
  have b0 : ∀ t : Fin 1357, 3 ≤ t.val → B0 t = [] := fun t ht => carIn_blank code m L t ht
  -- 1: the cell
  have d1 := cell_step.dock cellSl cellSl_inj (fun _ => 0) B0 (fun _ => rfl) (fun _ => b0 6 (by decide))
  rw [zH] at d1
  set B1 := install cellSl B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 1357, t.val ≠ 6 → B1 t = B0 t := fun t h => miss_cell B0 t h _
  -- 2: the preparation
  obtain ⟨o2, s2, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := SymTab.prepStage code m L
  have d2 := s2.dock prepSl prepSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [SymTab.prepIn_val]
    fin_cases j
    · show B1 0 = _; rw [b1 _ (by decide)]; rfl
    · show B1 6 = _; exact install_slot cellSl cellSl_inj B0 _ 0
    · show B1 1 = _; rw [b1 _ (by decide)]; rfl
    · show B1 2 = _; rw [b1 _ (by decide)]; rfl
    all_goals (show B1 _ = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl))
  rw [zH] at d2
  set B2 := install prepSl B1 o2 with hB2
  have b2 : ∀ t : Fin 1357, (16 ≤ t.val ∨ (3 ≤ t.val ∧ t.val ≤ 5)) → B2 t = B1 t := fun t h => miss_prep B1 t h _
  have b2h : ∀ j, B2 (prepSl j) = o2 j := fun j => install_slot prepSl prepSl_inj B1 o2 j
  -- 3: the traversal
  obtain ⟨o3, r3, t30, t41, -⟩ := CloseoutWitness.CanonicalTest.fields_run bits
  have d3 := (CarRound.step_of_ready r3).dock ctSl ctSl_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro j
    show B2 (ctSl j) = (if j.val = 0 then frame bits else [])
    by_cases hj : j.val = 0
    · rw [if_pos hj, show ctSl j = prepSl 4 from Fin.ext (by simp [ctSl, hj]; rfl), b2h, p4]
    · rw [if_neg hj, b2 _ (by simp [ctSl, hj]; omega), b1 _ (by simp [ctSl, hj]; omega),
        b0 _ (by simp [ctSl, hj]; omega)])
  rw [zH] at d3
  set B3 := install ctSl B2 o3 with hB3
  have b3 : ∀ t : Fin 1357, (t.val ≠ 7 ∧ (t.val < 16 ∨ 189 ≤ t.val)) → B3 t = B2 t := fun t h => miss_ct B2 t h _
  have b3h : ∀ j, B3 (ctSl j) = o3 j := fun j => install_slot ctSl ctSl_inj B2 o3 j
  -- 4: the capacity
  obtain ⟨o4, s4, -, q103⟩ := BlockPlatform.UnaryCalc.poly_step 50 cC2 (W + 1)
  have d4 := s4.dock powSl powSl_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro j
    show B3 (powSl j) = (if j.val = 0 then List.replicate (W + 1) true else [])
    by_cases hj : j.val = 0
    · rw [if_pos hj, b3 _ (by simp [powSl, hj]), show powSl j = prepSl 5 from Fin.ext (by simp [powSl, hj]; rfl),
        b2h, p5]
    · rw [if_neg hj, b3 _ (by simp [powSl, hj]; omega), b2 _ (by simp [powSl, hj]; omega),
        b1 _ (by simp [powSl, hj]; omega), b0 _ (by simp [powSl, hj]; omega)])
  rw [zH] at d4
  set B4 := install powSl B3 o4 with hB4
  have b4 : ∀ t : Fin 1357, (t.val ≠ 8 ∧ (t.val < 189 ∨ 302 ≤ t.val)) → B4 t = B3 t := fun t h => miss_pow B3 t h _
  have b4T : B4 291 = List.replicate T true := (install_slot powSl powSl_inj B3 o4 103).trans q103
  -- 5: the accumulator's header
  obtain ⟨o5, s5, e50, e51⟩ := initStage
  have d5 := s5.dock initSl initSl_inj (fun _ => 0) B4 (fun _ => rfl) (by
    intro j; rw [initIn_val]
    fin_cases j
    · show B4 304 = _; rw [b4 _ (by decide), b3 _ (by decide), b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B4 6 = _; rw [b4 _ (by decide), b3 _ (by decide), show (6 : Fin 1357) = prepSl 1 from rfl, b2h, p1]; rfl
    · show B4 1344 = _; rw [b4 _ (by decide), b3 _ (by decide), b2 _ (by decide), b1 _ (by decide),
        b0 _ (by decide)]; rfl)
  rw [zH] at d5
  set B5 := install initSl B4 o5 with hB5
  have b5 : ∀ t : Fin 1357, (t.val ≠ 304 ∧ t.val ≠ 6 ∧ t.val ≠ 1344) → B5 t = B4 t := fun t h => miss_init B4 t h _
  have b5h : ∀ j, B5 (initSl j) = o5 j := fun j => install_slot initSl initSl_inj B4 o5 j
  -- 6: the erase
  have er := RecoveryScratchErase.erase_ready T 0 (fun _ : Fin 1039 => ([] : List Bool)) (fun _ => Nat.zero_le _)
  obtain ⟨re, hre, hte, hhe, hse⟩ := er
  have er' : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 1039) (2 * T + 4) (erIn T) (erOut T) :=
    ⟨re, hre, hte, hhe, hse.le⟩
  have d6 := (CarRound.step_of_ready er').dock eraseSl eraseSl_inj (fun _ => 0) B5 (fun _ => rfl) (by
    intro j; rw [erIn_val]
    have hjl := j.isLt
    by_cases hj : j.val = 1039
    · rw [if_pos hj, show eraseSl j = (291 : Fin 1357) from Fin.ext (by simp [eraseSl, hj]),
        b5 _ (by decide), b4T]
    · rw [if_neg hj]
      have hv : (eraseSl j).val = 303 ∨ (eraseSl j).val = 1343 ∨ (305 ≤ (eraseSl j).val ∧ (eraseSl j).val ≤ 1342) := by
        simp only [eraseSl]; split_ifs <;> omega
      rw [b5 _ (by omega), b4 _ (by omega), b3 _ (by omega), b2 _ (by omega), b1 _ (by omega), b0 _ (by omega)])
  rw [zH] at d6
  set B6 := install eraseSl B5 (erOut T) with hB6
  have b6 : ∀ t : Fin 1357, (t.val ≠ 303 ∧ t.val ≠ 291 ∧ t.val ≠ 1343 ∧ (t.val < 305 ∨ 1343 ≤ t.val)) → B6 t = B5 t :=
    fun t h => miss_erase B5 t h _
  have b6h : ∀ j, B6 (eraseSl j) = erOut T j := fun j => install_slot eraseSl eraseSl_inj B5 _ j
  -- the loop's capacity
  have hcount : c * (2 * W + 1) ≤ max (2 * W + 1) (16 * 1000000000000000000 * (W + 1) ^ 24 + 1) := by
    have hl := ready_lengths r3 (2 * W + 1) (fun i => by
      show (if i.val = 0 then frame bits else []).length ≤ _
      split_ifs
      · rw [frame_length, hbits, binary_length]
      · simp) 30
    rw [t30, binary_length, hval, stream_eq W X, rawAtoms_len] at hl
    have hb : CloseoutWitness.CanonicalTest.budget bits = 16 * 1000000000000000000 * (W + 1) ^ 24 := by
      simp only [CloseoutWitness.CanonicalTest.budget, CloseoutWitness.Reencode.polynomialBudget, hbits, binary_length]
      ring
    rw [hb] at hl
    exact hl
  obtain ⟨cap1, cap2, cap3, cap4⟩ := capacity_ok W c (tabSeg X).length hcount (tabSeg_len_le W X hW)
  rw [← value_eq] at cap1 cap2 cap3 cap4
  -- 7: the atom loop
  have fr := fold_run W X hW T (T + 1) (le_refl _) cap1 (by rw [rawAtoms_len]; exact cap2)
    (by rw [show accHdr.length = 4 from rfl]; exact cap3) cap4
  have f45 : B6 45 = (CarRound.rawAtoms W X).flatMap frame := by
    rw [b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), show (45 : Fin 1357) = ctSl 30 from rfl, b3h, t30,
      binary_length, hval, stream_eq]
  have f303 : B6 303 = List.replicate T false := by
    rw [show (303 : Fin 1357) = eraseSl 0 from rfl, b6h, erOut_val]; simp
  have f304 : B6 304 = accHdr := by
    rw [b6 _ (by decide), show (304 : Fin 1357) = initSl 0 from rfl, b5h, e50]
  have fscr : ∀ t : Fin 1357, 305 ≤ t.val → t.val ≤ 1342 → B6 t = List.replicate T false := by
    intro t h1 h2
    rw [show t = eraseSl ⟨t.val - 304, by omega⟩ from Fin.ext (by simp only [eraseSl]; split_ifs <;> omega), b6h,
      erOut_val, if_pos (by simp; omega)]
  have f291 : B6 291 = List.replicate T true := by
    rw [show (291 : Fin 1357) = eraseSl 1039 from rfl, b6h, erOut_val]; simp
  have f1343 : B6 1343 = List.replicate (T + 1) false := by
    rw [show (1343 : Fin 1357) = eraseSl 1040 from rfl, b6h, erOut_val]; simp
  have f56 : B6 56 = RepairSource.VerifierDecoding.CompareMachine.word X.length := by
    rw [b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), show (56 : Fin 1357) = ctSl 41 from rfl, b3h, t41, hval,
      hatoms, List.length_map]
  have d7 := (CarRound.step_of_ready fr).dock foldSl foldSl_inj (fun _ => 0) B6 (fun _ => rfl)
    (fold_entry W T X B6 f45 f303 f304 fscr f291 f1343 f56)
  rw [zH] at d7
  set B7 := install foldSl B6 (Fin.addCases (m := 1041 + 2) (n := 1) (motive := fun _ => List Bool)
    (roundTapes (padScratch CarFold.scr T (Qc W T X c)) T (T + 1))
    (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c)) with hB7
  have b7 : ∀ t : Fin 1357, (t.val ≠ 45 ∧ t.val ≠ 56 ∧ t.val ≠ 291 ∧ t.val ≠ 1343 ∧ (t.val < 303 ∨ 1343 ≤ t.val)) →
      B7 t = B6 t := fun t h => miss_fold B6 t h _
  have b7A : B7 304 = accHdr ++ tabSeg X := by
    have := install_slot foldSl foldSl_inj B6 (Fin.addCases (m := 1041 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch CarFold.scr T (Qc W T X c)) T (T + 1))
      (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c)) 2
    rw [foldBank_val] at this
    simp [hc] at this
    exact this

  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq d7)))))
  have run' : Step carPreM _ (fun _ => 0) B0 (fun _ => 0) B7 := run
  refine ⟨B7, run'.enlarge (by unfold carPreCost; exact le_refl _), ?_, b7A⟩
  rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
    show (0 : Fin 1357) = prepSl 0 from rfl, b2h, p0]

end NearCubicWires.WireExponent3_5.UnionMachine.C1CarPre
