import Proof.Wire_3_5.UnionMachine.FrontFoldLoop

/-! # C6 front, U5, the writers' fold (b): the fold with its rulers

The fold of the writers (P3:3092-3094, 3409-3410, 3432-3433, 3083-3094) runs on padded round tapes. This stage
computes, by base's unary polynomial, the envelope ruler `1^((q+1)^deg)` (from `1^q`), the capacity `1^tot` and the
fold's driver `1^tot` (`tot = Ct·(n0+1)^Dt`, from `1^n0`), erases the counters and the round's scratch to `0^tot`, and
runs the fold driven by the count word of `nv`:
* bank: the fold's `1220 + tP + tC + 3` tapes (kept tapes `0..9`, scratch, driver, capacity, count word), then `1^q`,
  `1^n0`, and the three polynomial runs' own tapes.
**`stage_step`**: from the bitmaps (tape `0`), the atoms' codes (`2`), `1^sys` (`4`), the count word, `1^q`, `1^n0`, the
kept tapes `5`, `6`, `7` end with every variable's parity code, carrier code and envelope bit.

Paper quantity of the main type: the per-variable codes and envelope bits the table writer reads. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Transfer (roundTapes padScratch scratchCap)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldLoop
open NearCubicWires.WireExponent3_5.UnionMachine.CWIface (ParityWriterJ CarrierWriterJ)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.BlockPlatform.UnaryCalc (tapes inputTape outputTape value output_ne_input)

/-! ## The layout -/

section Layout
variable (tw a b : ℕ)

/-- The stage's tape count: the fold's `tw + 3`, `1^q`, `1^n0`, the three polynomial runs. -/
def NS : ℕ := tw + 5 + a + 2 * b

theorem lt_NS {v : ℕ} (h : v < tw + 5) : v < NS tw a b := by unfold NS; omega

/-- A polynomial run's slots: its input on `inT`, its output on `outT`, its other tapes from `base`. -/
def polyS {D : ℕ} (inT outT base : ℕ) (hin : inT < NS tw a b) (hout : outT < NS tw a b)
    (hb : base + tapes D ≤ NS tw a b) (j : Fin (tapes D)) : Fin (NS tw a b) :=
  if j = inputTape D then ⟨inT, hin⟩ else if j = outputTape D then ⟨outT, hout⟩ else ⟨base + j.val, by omega⟩

theorem polyS_val {D : ℕ} (inT outT base : ℕ) (hin : inT < NS tw a b) (hout : outT < NS tw a b)
    (hb : base + tapes D ≤ NS tw a b) (j : Fin (tapes D)) :
    (polyS tw a b inT outT base hin hout hb j).val =
      if j = inputTape D then inT else if j = outputTape D then outT else base + j.val := by
  unfold polyS; split_ifs <;> rfl

theorem polyS_inj {D : ℕ} (inT outT base : ℕ) (hin : inT < NS tw a b) (hout : outT < NS tw a b)
    (hb : base + tapes D ≤ NS tw a b) (hio : inT ≠ outT) (hlo : inT < base ∧ outT < base) :
    Function.Injective (polyS (D := D) tw a b inT outT base hin hout hb) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [polyS_val, polyS_val] at hv
  by_cases hx : x = inputTape D
  · by_cases hy : y = inputTape D
    · rw [hx, hy]
    · rw [if_pos hx, if_neg hy] at hv; split_ifs at hv <;> omega
  · by_cases hy : y = inputTape D
    · rw [if_neg hx, if_pos hy] at hv; split_ifs at hv <;> omega
    · rw [if_neg hx, if_neg hy] at hv
      by_cases hx' : x = outputTape D
      · by_cases hy' : y = outputTape D
        · rw [hx', hy']
        · rw [if_pos hx', if_neg hy'] at hv; omega
      · by_cases hy' : y = outputTape D
        · rw [if_neg hx', if_pos hy'] at hv; omega
        · rw [if_neg hx', if_neg hy'] at hv; exact Fin.ext (by omega)

/-- The fold's slots: the first `tw + 3` tapes. -/
def foldS (i : Fin (tw + 2 + 1)) : Fin (NS tw a b) := ⟨i.val, by unfold NS; omega⟩

theorem foldS_inj : Function.Injective (foldS tw a b) := fun x y h => Fin.ext (by
  have := congrArg Fin.val h; simpa [foldS] using this)

/-- The erase's slots: the counters `1`, `3` and the scratch `10..tw-1`, then the driver and the capacity. -/
def erS (hw : 10 ≤ tw) (j : Fin ((tw - 8) + 1 + 1)) : Fin (NS tw a b) :=
  ⟨if j.val = 0 then 1 else if j.val = 1 then 3 else if j.val < tw - 8 then j.val + 8
    else if j.val = tw - 8 then tw else tw + 1, by unfold NS; have := j.isLt; split_ifs <;> omega⟩

theorem erS_inj (hw : 10 ≤ tw) : Function.Injective (erS tw a b hw) := by
  intro x y h; have hv := congrArg Fin.val h; simp only [erS] at hv
  have := x.isLt; have := y.isLt; apply Fin.ext; split_ifs at hv <;> omega

theorem inst_ne {a N : ℕ} (sl : Fin a → Fin N) (B : Fin N → List Bool) (o : Fin a → List Bool) (t : Fin N)
    (h : ∀ j, (sl j).val ≠ t.val) : install sl B o t = B t :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))

theorem polyIn_val (D n : ℕ) (j : Fin (tapes D)) :
    RepairSource.ProjectionNormalization.DimensionPolynomial.input D n j =
      if j = inputTape D then List.replicate n true else [] := by
  unfold RepairSource.ProjectionNormalization.DimensionPolynomial.input
  by_cases h : j = inputTape D
  · rw [if_pos h, if_pos (by rw [h]; rfl)]
  · rw [if_neg h, if_neg (fun e => h (Fin.ext (by rw [e]; rfl)))]

theorem pad_zero' (l : List Bool) : ZeroPadding.pad 0 l = l := by simp [ZeroPadding.pad]
theorem pad_nil (n : ℕ) : ZeroPadding.pad n ([] : List Bool) = List.replicate n false := by simp [ZeroPadding.pad]

/-- The fold's entry bank, by tape. -/
theorem foldIn_val {tw ks : ℕ} (scr : Fin ks → Fin tw) (T capT : ℕ) (X : Fin tw → List Bool) (w : List Bool)
    (i : Fin (tw + 2 + 1)) :
    Fin.addCases (m := tw + 2) (n := 1) (motive := fun _ => List Bool) (roundTapes (padScratch scr T X) T capT)
      (fun _ => w) i =
    if h : i.val < tw then ZeroPadding.pad (scratchCap scr T ⟨i.val, h⟩) (X ⟨i.val, h⟩)
    else if i.val = tw then List.replicate T true else if i.val = tw + 1 then List.replicate capT false else w := by
  rw [CWCore.addCases_val]
  by_cases h1 : i.val < tw + 2
  · rw [dif_pos h1]; unfold roundTapes; rw [CWCore.addCases_val]
    by_cases h2 : i.val < tw
    · rw [dif_pos h2, dif_pos h2]; rfl
    · rw [dif_neg h2, dif_neg h2]
      have : i.val = tw ∨ i.val = tw + 1 := by omega
      rcases this with e | e
      · rw [if_pos e]; simp [e]
      · rw [if_neg (by omega), if_pos e]; simp [e]
  · rw [dif_neg h1, dif_neg (by omega), if_neg (by omega), if_neg (by omega)]

end Layout

/-! ## The stage -/

section Stage
variable (tP tC deg De Dt : ℕ)

/-- The envelope ruler's run: `1^q` on `tw + 3`, `1^((q+1)^deg)` on `8`. -/
def sL := polyS (D := deg) (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (1220 + tP + tC + 3) 8 (1220 + tP + tC + 5)
  (by unfold NS; omega) (by unfold NS; omega) (by unfold NS; omega)
/-- The capacity's run: `1^n0` on `tw + 4`, `1^tot` on `9`. -/
def sT1 := polyS (D := De) (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (1220 + tP + tC + 4) 9
  (1220 + tP + tC + 5 + tapes deg) (by unfold NS; omega) (by unfold NS; omega) (by unfold NS; omega)
/-- The driver's run: `1^n0` on `tw + 4`, `1^tot` on the driver `tw`. -/
def sT2 := polyS (D := Dt) (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (1220 + tP + tC + 4) (1220 + tP + tC)
  (1220 + tP + tC + 5 + tapes deg + (tapes De + tapes Dt)) (by unfold NS; omega) (by unfold NS; omega)
  (by unfold NS; omega)

theorem sL_inj : Function.Injective (sL tP tC deg De Dt) :=
  polyS_inj _ _ _ _ _ _ _ _ _ (by omega) (by omega)
theorem sT1_inj : Function.Injective (sT1 tP tC deg De Dt) :=
  polyS_inj _ _ _ _ _ _ _ _ _ (by omega) (by omega)
theorem sT2_inj : Function.Injective (sT2 tP tC deg De Dt) :=
  polyS_inj _ _ _ _ _ _ _ _ _ (by omega) (by omega)

/-- The stage's entry: the bitmaps, the atoms' codes, `1^sys`, the count word, `1^q`, `1^n0`. -/
def stIn (BM CA SY W Qu Nu : List Bool) : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)) → List Bool := fun t =>
  if t.val = 0 then BM else if t.val = 2 then CA else if t.val = 4 then SY else if t.val = 1220 + tP + tC + 2 then W
  else if t.val = 1220 + tP + tC + 3 then Qu else if t.val = 1220 + tP + tC + 4 then Nu else []

end Stage

section StageM
variable {m : Mode} {q : ℕ}

/-- The stage's setup: the envelope ruler, the capacity, the driver, the erase of the counters and the scratch. -/
noncomputable def setupM (tP tC deg De Ce Dt Ct : ℕ) :=
  Composition.machine (RecoveryFocus.machine (sL tP tC deg De Dt) (PCPSerializerCapacity.Power.machine deg 1))
  (Composition.machine (RecoveryFocus.machine (sT1 tP tC deg De Dt) (PCPSerializerCapacity.Power.machine De Ce))
  (Composition.machine (RecoveryFocus.machine (sT2 tP tC deg De Dt) (PCPSerializerCapacity.Power.machine Dt Ct))
    (RecoveryFocus.machine (erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega))
      (RecoveryScratchErase.resetMachine (1220 + tP + tC - 8)))))

/-- **The writers' fold with its rulers.** -/
noncomputable def stageM (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (deg De Ce Dt Ct : ℕ) :=
  Composition.machine (setupM Pw.t Cw.t deg De Ce Dt Ct)
    (RecoveryFocus.machine (foldS (1220 + Pw.t + Cw.t) (tapes deg) (tapes De + tapes Dt)) (foldM Pw Cw))

/-- The setup's fuel. -/
noncomputable def setupCost (deg De Ce Dt Ct q n0 : ℕ) : ℕ :=
  PCPSerializerCapacity.Power.budget deg 1 q + 1 + (PCPSerializerCapacity.Power.budget De Ce n0 + 1 +
    (PCPSerializerCapacity.Power.budget Dt Ct n0 + 1 + (2 * value Dt Ct n0 + 4)))

/-- The stage's fuel. -/
noncomputable def stageCost (deg De Ce Dt Ct q n0 nv cw : ℕ) : ℕ :=
  setupCost deg De Ce Dt Ct q n0 + 1 +
    (1 + 1 + (nv * (cw + 1 + (2 * value Dt Ct n0 + 4 + 1 + 0) + 2) + nv + 3 + 1 + 1))

end StageM

section StageRun
variable {m : Mode} {q : ℕ}

theorem sL_val (tP tC deg De Dt : ℕ) (j : Fin (tapes deg)) : (sL tP tC deg De Dt j).val =
    if j = inputTape deg then 1220 + tP + tC + 3 else if j = outputTape deg then 8 else 1220 + tP + tC + 5 + j.val :=
  polyS_val _ _ _ _ _ _ _ _ _ j
theorem sT1_val (tP tC deg De Dt : ℕ) (j : Fin (tapes De)) : (sT1 tP tC deg De Dt j).val =
    if j = inputTape De then 1220 + tP + tC + 4 else if j = outputTape De then 9
    else 1220 + tP + tC + 5 + tapes deg + j.val :=
  polyS_val _ _ _ _ _ _ _ _ _ j
theorem sT2_val (tP tC deg De Dt : ℕ) (j : Fin (tapes Dt)) : (sT2 tP tC deg De Dt j).val =
    if j = inputTape Dt then 1220 + tP + tC + 4 else if j = outputTape Dt then 1220 + tP + tC
    else 1220 + tP + tC + 5 + tapes deg + (tapes De + tapes Dt) + j.val :=
  polyS_val _ _ _ _ _ _ _ _ _ j

theorem scratchCap_scrF (tP tC T : ℕ) (t : Fin (1220 + tP + tC)) :
    scratchCap (scrF tP tC) T t = if 10 ≤ t.val then T else 0 := by
  by_cases h : 10 ≤ t.val
  · rw [if_pos h]; unfold scratchCap; rw [if_pos ((scrF_iff tP tC t).mpr h)]
  · rw [if_neg h]; unfold scratchCap; rw [if_neg (fun hh => h ((scrF_iff tP tC t).mp hh))]

theorem st_hi (F : FoldIn m q) (deg T Z0 X tP tC : ℕ) (t : Fin (1220 + tP + tC)) (ht : 10 ≤ t.val) :
    F.st deg T Z0 X tP tC t = [] := by
  simp only [FoldIn.st, FrontFoldRound.Qf]; exact List.getD_eq_default _ _ (by simp; omega)

/-- **The setup's run**: the counters and the scratch erased to `0^tot`, the envelope ruler on `8`, the capacity on
`9`, the driver `1^tot` on `tw`, the capacity tape `0^(tot+1)` on `tw + 1`; the entries kept. -/
theorem setup_run (tP tC deg De Ce Dt Ct q n0 : ℕ) (BM CA SY W : List Bool) :
    ∃ B4 : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)) → List Bool,
      Step (setupM tP tC deg De Ce Dt Ct) (setupCost deg De Ce Dt Ct q n0) (fun _ => 0)
        (stIn tP tC deg De Dt BM CA SY W (List.replicate q true) (List.replicate n0 true)) (fun _ => 0) B4 ∧
      (∀ t : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)), t.val < 10 →
        B4 t = [BM, List.replicate (value Dt Ct n0) false, CA, List.replicate (value Dt Ct n0) false, SY, [], [], [],
          List.replicate ((q + 1) ^ deg) true, List.replicate (value De Ce n0) true].getD t.val []) ∧
      (∀ t : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)), 10 ≤ t.val → t.val < 1220 + tP + tC →
        B4 t = List.replicate (value Dt Ct n0) false) ∧
      B4 ⟨1220 + tP + tC, lt_NS _ _ _ (by omega)⟩ = List.replicate (value Dt Ct n0) true ∧
      B4 ⟨1220 + tP + tC + 1, lt_NS _ _ _ (by omega)⟩ = List.replicate (value Dt Ct n0 + 1) false ∧
      B4 ⟨1220 + tP + tC + 2, lt_NS _ _ _ (by omega)⟩ = W := by
  set tot := value Dt Ct n0 with htot
  have hd : 1220 + tP + tC - 8 + 8 = 1220 + tP + tC := by omega
  set B0 := stIn tP tC deg De Dt BM CA SY W (List.replicate q true) (List.replicate n0 true) with hB0
  have b0 : ∀ t : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)), t.val ≠ 0 → t.val ≠ 2 → t.val ≠ 4 →
      t.val ≠ 1220 + tP + tC + 2 → t.val ≠ 1220 + tP + tC + 3 → t.val ≠ 1220 + tP + tC + 4 → B0 t = [] := by
    intro t h1 h2 h3 h4 h5 h6; simp only [hB0, stIn]
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]
  -- 1: the envelope ruler
  obtain ⟨o1, s1, i1, q1⟩ := NearCubicWires.BlockPlatform.UnaryCalc.poly_step deg 1 q
  have d1 := s1.dock (sL tP tC deg De Dt) (sL_inj tP tC deg De Dt) (fun _ => 0) B0 (fun _ => rfl) (by
    intro j; rw [polyIn_val]
    have hv := sL_val tP tC deg De Dt j
    have := j.isLt
    by_cases hj : j = inputTape deg
    · rw [if_pos hj]; rw [if_pos hj] at hv
      simp only [hB0, stIn]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hv]
    · rw [if_neg hj]; rw [if_neg hj] at hv
      apply b0 <;> split_ifs at hv <;> omega)
  rw [FrontFoldDock.zeroH] at d1
  set B1 := install (sL tP tC deg De Dt) B0 o1 with hB1
  have c1 : ∀ t : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)), t.val ≠ 1220 + tP + tC + 3 → t.val ≠ 8 →
      (t.val < 1220 + tP + tC + 5 ∨ 1220 + tP + tC + 5 + tapes deg ≤ t.val) → B1 t = B0 t :=
    fun t h1 h2 h3 => inst_ne _ B0 o1 t (fun j => by have := j.isLt; rw [sL_val]; split_ifs <;> omega)
  have g1_8 : B1 (sL tP tC deg De Dt (outputTape deg)) = List.replicate (value deg 1 q) true :=
    (install_slot _ (sL_inj tP tC deg De Dt) B0 o1 (outputTape deg)).trans q1
  have e8 : (sL tP tC deg De Dt (outputTape deg)).val = 8 := by
    rw [sL_val, if_neg (output_ne_input deg), if_pos rfl]
  -- 2: the capacity
  obtain ⟨o2, s2, i2, q2⟩ := NearCubicWires.BlockPlatform.UnaryCalc.poly_step De Ce n0
  have d2 := s2.dock (sT1 tP tC deg De Dt) (sT1_inj tP tC deg De Dt) (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [polyIn_val]
    have hv := sT1_val tP tC deg De Dt j
    have := j.isLt
    by_cases hj : j = inputTape De
    · rw [if_pos hj]; rw [if_pos hj] at hv
      rw [c1 _ (by omega) (by omega) (by omega)]
      simp only [hB0, stIn]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hv]
    · rw [if_neg hj]; rw [if_neg hj] at hv
      rw [c1 _ (by split_ifs at hv <;> omega) (by split_ifs at hv <;> omega) (by split_ifs at hv <;> omega)]
      apply b0 <;> split_ifs at hv <;> omega)
  rw [FrontFoldDock.zeroH] at d2
  set B2 := install (sT1 tP tC deg De Dt) B1 o2 with hB2
  have c2 : ∀ t : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)), t.val ≠ 1220 + tP + tC + 4 → t.val ≠ 9 →
      (t.val < 1220 + tP + tC + 5 + tapes deg ∨ 1220 + tP + tC + 5 + tapes deg + tapes De ≤ t.val) → B2 t = B1 t :=
    fun t h1 h2 h3 => inst_ne _ B1 o2 t (fun j => by have := j.isLt; rw [sT1_val]; split_ifs <;> omega)
  have g2_9 : B2 (sT1 tP tC deg De Dt (outputTape De)) = List.replicate (value De Ce n0) true :=
    (install_slot _ (sT1_inj tP tC deg De Dt) B1 o2 (outputTape De)).trans q2
  have e9 : (sT1 tP tC deg De Dt (outputTape De)).val = 9 := by
    rw [sT1_val, if_neg (output_ne_input De), if_pos rfl]
  have g2_N : B2 (sT1 tP tC deg De Dt (inputTape De)) = List.replicate n0 true :=
    (install_slot _ (sT1_inj tP tC deg De Dt) B1 o2 (inputTape De)).trans i2
  have eN : (sT1 tP tC deg De Dt (inputTape De)).val = 1220 + tP + tC + 4 := by rw [sT1_val, if_pos rfl]
  -- 3: the driver
  obtain ⟨o3, s3, -, q3⟩ := NearCubicWires.BlockPlatform.UnaryCalc.poly_step Dt Ct n0
  have d3 := s3.dock (sT2 tP tC deg De Dt) (sT2_inj tP tC deg De Dt) (fun _ => 0) B2 (fun _ => rfl) (by
    intro j; rw [polyIn_val]
    have hv := sT2_val tP tC deg De Dt j
    have := j.isLt
    by_cases hj : j = inputTape Dt
    · rw [if_pos hj]; rw [if_pos hj] at hv
      rw [show sT2 tP tC deg De Dt j = sT1 tP tC deg De Dt (inputTape De) from Fin.ext (by rw [hv, eN]), g2_N]
    · rw [if_neg hj]; rw [if_neg hj] at hv
      rw [c2 _ (by split_ifs at hv <;> omega) (by split_ifs at hv <;> omega) (by split_ifs at hv <;> omega),
        c1 _ (by split_ifs at hv <;> omega) (by split_ifs at hv <;> omega) (by split_ifs at hv <;> omega)]
      apply b0 <;> split_ifs at hv <;> omega)
  rw [FrontFoldDock.zeroH] at d3
  set B3 := install (sT2 tP tC deg De Dt) B2 o3 with hB3
  have c3 : ∀ t : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)), t.val ≠ 1220 + tP + tC + 4 →
      t.val ≠ 1220 + tP + tC → t.val < 1220 + tP + tC + 5 + tapes deg + (tapes De + tapes Dt) → B3 t = B2 t :=
    fun t h1 h2 h3 => inst_ne _ B2 o3 t (fun j => by have := j.isLt; rw [sT2_val]; split_ifs <;> omega)
  have g3_R : B3 (sT2 tP tC deg De Dt (outputTape Dt)) = List.replicate tot true :=
    (install_slot _ (sT2_inj tP tC deg De Dt) B2 o3 (outputTape Dt)).trans q3
  have eR : (sT2 tP tC deg De Dt (outputTape Dt)).val = 1220 + tP + tC := by
    rw [sT2_val, if_neg (output_ne_input Dt), if_pos rfl]
  -- the early tapes, back to the entry
  have back : ∀ t : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)), t.val < 1220 + tP + tC + 3 →
      t.val ≠ 1220 + tP + tC → t.val ≠ 8 → t.val ≠ 9 → B3 t = B0 t := fun t h1 h2 h3 h4 => by
    rw [c3 t (by omega) h2 (by omega), c2 t (by omega) h4 (by omega), c1 t (by omega) h3 (by omega)]
  -- 4: the erase
  have d4 := (CWCore.erase_step (1220 + tP + tC - 8) tot 0).dock (erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)
    (by omega)) (erS_inj _ _ _ (by omega)) (fun _ => 0) B3 (fun _ => rfl) (by
    intro j; rw [CWCore.erIn_val]
    have := j.isLt
    by_cases h1 : j.val < 1220 + tP + tC - 8
    · rw [if_pos h1]
      have hv : (erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega) j).val =
          if j.val = 0 then 1 else if j.val = 1 then 3 else j.val + 8 := by
        simp only [erS]; split_ifs <;> omega
      rw [back _ (by split_ifs at hv <;> omega) (by split_ifs at hv <;> omega) (by split_ifs at hv <;> omega)
        (by split_ifs at hv <;> omega)]
      apply b0 <;> split_ifs at hv <;> omega
    · rw [if_neg h1]
      by_cases h2 : j.val = 1220 + tP + tC - 8
      · rw [if_pos h2, show erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega) j =
          sT2 tP tC deg De Dt (outputTape Dt) from Fin.ext (by rw [eR]; simp only [erS]; split_ifs <;> omega), g3_R]
      · rw [if_neg h2]
        have hv : (erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega) j).val = 1220 + tP + tC + 1 := by
          simp only [erS]; split_ifs <;> omega
        rw [back _ (by omega) (by omega) (by omega) (by omega), b0 _ (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)]
        rfl)
  rw [FrontFoldDock.zeroH] at d4
  set B4 := install (erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega)) B3
    (CWCore.erOut (1220 + tP + tC - 8) tot 0) with hB4
  have g4 : ∀ j, B4 (erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega) j) =
      CWCore.erOut (1220 + tP + tC - 8) tot 0 j := fun j => install_slot _ (erS_inj _ _ _ (by omega)) _ _ _
  have c4 : ∀ t : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)), t.val ≠ 1 → t.val ≠ 3 →
      (t.val < 10 ∨ 1220 + tP + tC + 2 ≤ t.val) → B4 t = B3 t :=
    fun t h1 h2 h3 => inst_ne _ B3 _ t (fun j => by have := j.isLt; simp only [erS]; split_ifs <;> omega)
  have eraseHit : ∀ t : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt)),
      (t.val = 1 ∨ t.val = 3 ∨ (10 ≤ t.val ∧ t.val < 1220 + tP + tC)) → B4 t = List.replicate tot false := by
    intro t ht
    rcases ht with e | e | ⟨e1, e2⟩
    · rw [show t = erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega) ⟨0, by omega⟩ from
        Fin.ext (by simp [erS, e]), g4, CWCore.erOut_val, if_pos (by simp; omega)]
    · rw [show t = erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega) ⟨1, by omega⟩ from
        Fin.ext (by simp [erS, e]), g4, CWCore.erOut_val, if_pos (by simp; omega)]
    · have hlt : t.val - 8 < 1220 + tP + tC - 8 := by omega
      have e3 : t = erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega) ⟨t.val - 8, by omega⟩ := by
        apply Fin.ext
        simp only [erS, Fin.val_mk]
        rw [if_neg (by omega), if_neg (by omega), if_pos hlt]; omega
      rw [e3, g4, CWCore.erOut_val, if_pos hlt]
  refine ⟨B4, d1.seq (d2.seq (d3.seq d4)), ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hv : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 ∨ t.val = 4 ∨ t.val = 5 ∨ t.val = 6 ∨ t.val = 7 ∨
        t.val = 8 ∨ t.val = 9 := by omega
    rcases hv with e | e | e | e | e | e | e | e | e | e
    · rw [c4 t (by omega) (by omega) (by omega), back t (by omega) (by omega) (by omega) (by omega), e]
      simp only [hB0, stIn]; simp [e]
    · rw [eraseHit t (by omega), e]; rfl
    · rw [c4 t (by omega) (by omega) (by omega), back t (by omega) (by omega) (by omega) (by omega), e]
      simp only [hB0, stIn]; simp [e]
    · rw [eraseHit t (by omega), e]; rfl
    · rw [c4 t (by omega) (by omega) (by omega), back t (by omega) (by omega) (by omega) (by omega), e]
      simp only [hB0, stIn]; simp [e]
    · rw [c4 t (by omega) (by omega) (by omega), back t (by omega) (by omega) (by omega) (by omega),
        b0 t (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), e]; rfl
    · rw [c4 t (by omega) (by omega) (by omega), back t (by omega) (by omega) (by omega) (by omega),
        b0 t (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), e]; rfl
    · rw [c4 t (by omega) (by omega) (by omega), back t (by omega) (by omega) (by omega) (by omega),
        b0 t (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), e]; rfl
    · rw [c4 t (by omega) (by omega) (by omega), c3 t (by omega) (by omega) (by omega),
        c2 t (by omega) (by omega) (by omega), show t = sL tP tC deg De Dt (outputTape deg) from Fin.ext (by rw [e8, e]),
        g1_8, e8]
      simp [value]
    · rw [c4 t (by omega) (by omega) (by omega), c3 t (by omega) (by omega) (by omega),
        show t = sT1 tP tC deg De Dt (outputTape De) from Fin.ext (by rw [e9, e]), g2_9, e9]; rfl
  · intro t h1 h2; exact eraseHit t (by omega)
  · rw [show (⟨1220 + tP + tC, lt_NS _ _ _ (by omega)⟩ : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt))) =
      erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega) ⟨1220 + tP + tC - 8, by omega⟩ from
      Fin.ext (by simp only [erS, Fin.val_mk]; split_ifs <;> omega), g4, CWCore.erOut_val, if_neg (by simp),
      if_pos (by simp)]
  · rw [show (⟨1220 + tP + tC + 1, lt_NS _ _ _ (by omega)⟩ : Fin (NS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt))) =
      erS (1220 + tP + tC) (tapes deg) (tapes De + tapes Dt) (by omega) ⟨1220 + tP + tC - 8 + 1, by omega⟩ from
      Fin.ext (by
        simp only [erS, Fin.val_mk]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]),
      g4, CWCore.erOut_val, if_neg (by simp), if_neg (by simp)]
    simp
  · rw [c4 _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)
      (by simp only [Fin.val_mk]; omega), back _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)
      (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
    simp [hB0, stIn]
    intro h; exact absurd h (by omega)

/-- **The writers' fold with its rulers**: from the bitmaps, the atoms' codes, `1^sys`, the count word of `nv`, `1^q`
and `1^n0`, every kept tape ends as in the fold's final state: the parity codes, the carrier codes and the envelope
bits (at degree `deg`) of all `nv` variables, for a uniform round fuel `cw` below `tot = Ct·(n0+1)^Dt`. -/
theorem stage_step (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (F : FoldIn m q) (deg De Ce Dt Ct n0 Wa cw : ℕ)
    (hWa : ∀ a ∈ F.as, a.length ≤ Wa) (hZ0 : F.nv + 1 ≤ value Dt Ct n0)
    (henv : ∀ X < F.nv, EnvFit (F.car X) deg (value De Ce n0))
    (hcw : ∀ X < F.nv, rcost Pw Cw F (value De Ce n0) Wa X ≤ cw) (hcwT : cw + 1 ≤ value Dt Ct n0)
    (hlen : ∀ X ≤ F.nv, ∀ t,
      (F.st deg (value De Ce n0) (value Dt Ct n0) X Pw.t Cw.t t).length ≤ value Dt Ct n0) :
    ∃ out : Fin (NS (1220 + Pw.t + Cw.t) (tapes deg) (tapes De + tapes Dt)) → List Bool,
      Step (stageM Pw Cw deg De Ce Dt Ct) (stageCost deg De Ce Dt Ct q n0 F.nv cw) (fun _ => 0)
        (stIn Pw.t Cw.t deg De Dt (F.ys.flatMap frame) (F.as.flatMap frame) (List.replicate F.sys true)
          (CompareMachine.word F.nv) (List.replicate q true) (List.replicate n0 true)) (fun _ => 0) out ∧
      ∀ t : Fin (NS (1220 + Pw.t + Cw.t) (tapes deg) (tapes De + tapes Dt)), (ht : t.val < 10) →
        out t = F.st deg (value De Ce n0) (value Dt Ct n0) F.nv Pw.t Cw.t ⟨t.val, by omega⟩ := by
  set tot := value Dt Ct n0 with htot
  set T := value De Ce n0 with hT
  obtain ⟨B4, d4, h10, hscr, hR, hC, hW⟩ := setup_run Pw.t Cw.t deg De Ce Dt Ct q n0 (F.ys.flatMap frame)
    (F.as.flatMap frame) (List.replicate F.sys true) (CompareMachine.word F.nv)
  have fR := fold_run Pw Cw F deg T tot Wa hWa hZ0 henv tot (tot + 1) cw le_rfl hcw hcwT hlen
  have d5 := (FrontLoopKit.step_of_ready fR).dock (foldS (1220 + Pw.t + Cw.t) (tapes deg) (tapes De + tapes Dt))
    (foldS_inj _ _ _) (fun _ => 0) B4 (fun _ => rfl) (by
    intro i
    rw [foldIn_val]
    have hfi : (foldS (1220 + Pw.t + Cw.t) (tapes deg) (tapes De + tapes Dt) i).val = i.val := rfl
    by_cases h1 : i.val < 1220 + Pw.t + Cw.t
    · rw [dif_pos h1, scratchCap_scrF]
      simp only [Fin.val_mk]
      by_cases h10' : 10 ≤ i.val
      · rw [if_pos h10', st_hi _ _ _ _ _ _ _ _ (by simpa using h10'), pad_nil,
          hscr _ (by rw [hfi]; exact h10') (by rw [hfi]; exact h1)]
      · rw [if_neg h10', pad_zero', h10 _ (by rw [hfi]; omega), hfi]
        simp only [FoldIn.st, FrontFoldRound.Qf]
        simp [FrontFoldRound.ctr, htot, hT]
    · rw [dif_neg h1]
      by_cases h2 : i.val = 1220 + Pw.t + Cw.t
      · rw [if_pos h2, show foldS (1220 + Pw.t + Cw.t) (tapes deg) (tapes De + tapes Dt) i =
          ⟨1220 + Pw.t + Cw.t, lt_NS _ _ _ (by omega)⟩ from Fin.ext (by rw [hfi, h2]), hR]
      · rw [if_neg h2]
        by_cases h3 : i.val = 1220 + Pw.t + Cw.t + 1
        · rw [if_pos h3, show foldS (1220 + Pw.t + Cw.t) (tapes deg) (tapes De + tapes Dt) i =
            ⟨1220 + Pw.t + Cw.t + 1, lt_NS _ _ _ (by omega)⟩ from Fin.ext (by rw [hfi, h3]), hC]
        · rw [if_neg h3, show foldS (1220 + Pw.t + Cw.t) (tapes deg) (tapes De + tapes Dt) i =
            ⟨1220 + Pw.t + Cw.t + 2, lt_NS _ _ _ (by omega)⟩ from
            Fin.ext (by simp only [Fin.val_mk]; rw [hfi]; have := i.isLt; omega), hW])
  rw [FrontFoldDock.zeroH] at d5
  have key : ∀ i : Fin (1220 + Pw.t + Cw.t + 2 + 1), (hi : i.val < 10) →
      install (foldS (1220 + Pw.t + Cw.t) (tapes deg) (tapes De + tapes Dt)) B4
        (Fin.addCases (m := 1220 + Pw.t + Cw.t + 2) (n := 1) (motive := fun _ => List Bool)
          (roundTapes (padScratch (scrF Pw.t Cw.t) tot (F.st deg T tot F.nv Pw.t Cw.t)) tot (tot + 1))
          (fun _ => CompareMachine.word F.nv)) (foldS (1220 + Pw.t + Cw.t) (tapes deg) (tapes De + tapes Dt) i) =
        F.st deg T tot F.nv Pw.t Cw.t ⟨i.val, by omega⟩ := by
    intro i hi
    rw [install_slot _ (foldS_inj _ _ _) _ _ _, foldIn_val, dif_pos (by omega), scratchCap_scrF]
    simp only [Fin.val_mk]
    rw [if_neg (by omega), pad_zero']
  refine ⟨_, d4.seq d5, fun t ht => key ⟨t.val, by omega⟩ ht⟩
end StageRun

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldStage
