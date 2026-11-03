import Proof.Wire_3_5.UnionMachine.CWRoundA
import Proof.CaseAnalysis.RowsGateHeader
import Proof.PCP.PCPPairCanonical

/-! # C6 front, U5, the code writers: loop B's round — one bottom's atom code

A named carrier is a list of bottom threshold atoms, and its code is "the balanced list of atom codes"
(`Stars.Carrier.code`, P3:3071-3086): each atom's code is the tagged pair `[encodeIntList w, encodeInt θ]`
(`CarrierFormat.gateCode`), the first two fields of the supported bottom's code it comes from
(`CarrierFormat.gateCode_supported`, on the gate header's field words `supported_codeWords`). One ROUND of loop B
handles bottom `j` on a fixed bank of `292` tapes:
* `0` the bottoms (framed words), `1` the round counter `1^j 0 r`, `2` the atom-code accumulator; `3` the cell;
* the crop (`CWWords.cropBW`): bottom `j` on `4`, the constants `frame []` on `5`, `6` and `frame [true]` on `7`, `8`;
* base's gate header (`CloseoutRowsGateHeader`, 148 tapes): the field words `frame (codeWord y k)`;
* base's pair node four times (`PCPPairCold` ×3, `PCPPairCanonical`): `Nat.pair v₁ 0`, `Nat.pair 1 ·`,
  `Nat.pair v₀ ·`, `Nat.pair 1 ·` = `encodeTaggedList [v₀, v₁]`, the last one in canonical binary;
* the append (`CWWords.appendBW`): the atom code's framed word joins the accumulator.

Paper quantity of the main type (**`roundB_run`**): the atom code `gc y = encodeTaggedList [v₀, v₁]` of bottom `j`
(`v_k` the values of its gate header's field words), appended in canonical binary. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWRoundB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready FrontKit.ready_of_step)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## The atom code of a bottom word -/

/-- The gate header's field word `k` of a bottom word. -/
def cw (y : List Bool) (k : Fin 3) : List Bool := CloseoutRowsGateHeader.codeWord y k

/-- **The atom code of a bottom word**: the tagged pair of its first two field values. -/
def gc (y : List Bool) : ℕ := CanonicalBinary.encodeTaggedList [value (cw y 0), value (cw y 1)]

theorem gc_pos (y : List Bool) : 0 < gc y := by
  unfold gc CanonicalBinary.encodeTaggedList
  have := Nat.add_le_pair 1 (Nat.pair (value (cw y 0)) (CanonicalBinary.encodeTaggedList [value (cw y 1)]))
  omega

theorem gc_bits_ne (y : List Bool) : (gc y).bits ≠ [] := by
  intro h
  have := CanonicalPositiveOutput.nat_bits_value (gc y)
  rw [h] at this
  have hp := gc_pos y
  simp [RadixSemantics.value] at this; omega

theorem cw_length (y : List Bool) (k : Fin 3) : (cw y k).length = y.length := by
  unfold cw CloseoutRowsGateHeader.codeWord
  rw [(RecoveryFixedUnpair.word_lengths _).1, CompetitorWitnessTriple.word_length]

/-! ## The four pair words -/

/-- `Nat.pair v₁ 0`, at the pair node's width. -/
def w1 (y : List Bool) : List Bool := binary (PCPPair.width (cw y 1) []) (Nat.pair (value (cw y 1)) (value []))
/-- `Nat.pair 1 (Nat.pair v₁ 0)`. -/
def w2 (y : List Bool) : List Bool := binary (PCPPair.width [true] (w1 y)) (Nat.pair (value [true]) (value (w1 y)))
/-- `Nat.pair v₀ (Nat.pair 1 (Nat.pair v₁ 0))`. -/
def w3 (y : List Bool) : List Bool := binary (PCPPair.width (cw y 0) (w2 y)) (Nat.pair (value (cw y 0)) (value (w2 y)))

theorem value_w1 (y : List Bool) : value (w1 y) = Nat.pair (value (cw y 1)) 0 :=
  binary_value _ _ (PCPPair.pair_bound _ _)
theorem value_w2 (y : List Bool) : value (w2 y) = Nat.pair 1 (Nat.pair (value (cw y 1)) 0) := by
  unfold w2; rw [binary_value _ _ (PCPPair.pair_bound _ _), value_w1]; rfl
theorem value_w3 (y : List Bool) :
    value (w3 y) = Nat.pair (value (cw y 0)) (Nat.pair 1 (Nat.pair (value (cw y 1)) 0)) := by
  unfold w3; rw [binary_value _ _ (PCPPair.pair_bound _ _), value_w2]

theorem pair4 (y : List Bool) : Nat.pair (value [true]) (value (w3 y)) = gc y := by
  rw [value_w3]; rfl

theorem w1_len (y : List Bool) : (w1 y).length = 2 * y.length + 2 := by
  simp [w1, PCPPair.width, cw_length]; ring
theorem w2_len (y : List Bool) : (w2 y).length = 4 * y.length + 8 := by
  simp [w2, PCPPair.width, w1_len]; ring
theorem w3_len (y : List Bool) : (w3 y).length = 10 * y.length + 18 := by
  simp [w3, PCPPair.width, w2_len, cw_length]; ring

/-! ## The layout -/

def cropSl : Fin 9 → Fin 292 := ![0, 3, 1, 4, 5, 6, 7, 8, 9]
def ghSl (j : Fin 148) : Fin 292 := ⟨if j.val = 0 then 5 else if j.val = 1 then 4 else j.val + 8, by split_ifs <;> omega⟩
/-- A pair node's slot value: its operands at `a`, `b`, its other tapes from `base`. -/
def pv (a b base j : ℕ) : ℕ :=
  if j = 2 then a else if j = 3 then b else if j = 0 then base else if j = 1 then base + 1 else j + base - 2

/-- A pair node's slots. -/
def pSl (t a b base : ℕ) (h : ∀ j < t, pv a b base j < 292) (j : Fin t) : Fin 292 := ⟨pv a b base j.val, h j j.isLt⟩

def p1Sl : Fin 35 → Fin 292 := pSl 35 86 6 156 (fun j hj => by unfold pv; split_ifs <;> omega)
def p2Sl : Fin 35 → Fin 292 := pSl 35 7 180 189 (fun j hj => by unfold pv; split_ifs <;> omega)
def p3Sl : Fin 35 → Fin 292 := pSl 35 46 213 222 (fun j hj => by unfold pv; split_ifs <;> omega)
def p4Sl : Fin 38 → Fin 292 := pSl 38 8 246 255 (fun j hj => by unfold pv; split_ifs <;> omega)
def abSl : Fin 4 → Fin 292 := ![279, 3, 2, 291]

theorem cropSl_inj : Function.Injective cropSl := by decide
theorem abSl_inj : Function.Injective abSl := by decide
theorem ghSl_inj : Function.Injective ghSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [ghSl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem p1Sl_inj : Function.Injective p1Sl := by decide
theorem p2Sl_inj : Function.Injective p2Sl := by decide
theorem p3Sl_inj : Function.Injective p3Sl := by decide
theorem p4Sl_inj : Function.Injective p4Sl := by decide

theorem cropSl_val (j : Fin 9) : (cropSl j).val = [0, 3, 1, 4, 5, 6, 7, 8, 9].getD j.val 0 := by fin_cases j <;> rfl
theorem abSl_val (j : Fin 4) : (abSl j).val = [279, 3, 2, 291].getD j.val 0 := by fin_cases j <;> rfl

/-- The image of a pair node's slots, outside its two operands, is `[base, base + t - 2)`. -/
theorem pv_range (t a b base : ℕ) (ht : 4 ≤ t) (j : ℕ) (hj : j < t) (h2 : j ≠ 2) (h3 : j ≠ 3) :
    base ≤ pv a b base j ∧ pv a b base j < base + t - 2 := by
  unfold pv; split_ifs <;> omega

noncomputable def cellR := RecoveryFocus.machine (fun _ : Fin 1 => (3 : Fin 292)) NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def cropR := RecoveryFocus.machine cropSl (Rewind.machine cropBW.toProg.compile)
noncomputable def ghR := RecoveryFocus.machine ghSl CloseoutRowsGateHeader.machine
noncomputable def p1R := RecoveryFocus.machine p1Sl PCPPairCold.machine
noncomputable def p2R := RecoveryFocus.machine p2Sl PCPPairCold.machine
noncomputable def p3R := RecoveryFocus.machine p3Sl PCPPairCold.machine
noncomputable def p4R := RecoveryFocus.machine p4Sl PCPPairCanonical.machine
noncomputable def abR := RecoveryFocus.machine abSl (Rewind.machine appendBW.toProg.compile)

/-- **Loop B's round worker.** -/
noncomputable def workerB :=
  Composition.machine cellR (Composition.machine cropR (Composition.machine ghR (Composition.machine p1R
    (Composition.machine p2R (Composition.machine p3R (Composition.machine p4R abR))))))

/-- The round's entry: the bottoms, the counter, the accumulator; every other tape blank. -/
def roundBIn (S K G : List Bool) : Fin 292 → List Bool :=
  fun t => if t.val = 0 then S else if t.val = 1 then K else if t.val = 2 then G else []

theorem zeroH (t : ℕ) (sl : Fin t → Fin 292) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

theorem pairIn_val (l r : List Bool) (j : Fin 35) :
    PCPPairCold.input l r j = if j.val = 2 then frame l else if j.val = 3 then frame r else [] := rfl

theorem canIn_val (l r : List Bool) (j : Fin 38) :
    PCPPairCanonical.input l r j = if j.val = 2 then frame l else if j.val = 3 then frame r else [] := rfl

/-- The round's fuel. -/
noncomputable def roundBCost (j W : ℕ) (y : List Bool) (gs : List (List Bool)) : ℕ :=
  1 + 1 + ((2 * cropBCost j W + 2) + 1 + (CloseoutRowsGateHeader.budget y + 1 +
    (PCPPairCold.budget (cw y 1) [] + 1 + (PCPPairCold.budget [true] (w1 y) + 1 +
      (PCPPairCold.budget (cw y 0) (w2 y) + 1 + (PCPPairCanonical.budget [true] (w3 y) + 1 +
        (2 * appendBCost gs (gc y).bits + 2)))))))

/-- **One round of loop B**: bottom `j`'s atom code joins the accumulator in canonical binary; the counter advances. -/
theorem roundB_run (W : ℕ) (ys : List (List Bool)) (hys : ∀ y ∈ ys, y.length ≤ W) (j : ℕ) (hj : j < ys.length)
    (rest : List Bool) (gs : List (List Bool)) (hgs : ∀ g ∈ gs, g ≠ []) :
    ∃ out, ClockJoin.ReadyRun workerB (roundBCost j W ys[j] gs)
        (roundBIn (ys.flatMap frame) (List.replicate j true ++ (false :: rest)) (gs.flatMap frame)) out ∧
      out 0 = ys.flatMap frame ∧ out 1 = List.replicate (j + 1) true ++ rest ∧
      out 2 = (gs ++ [(gc ys[j]).bits]).flatMap frame := by
  set y := ys[j] with hy
  set B0 := roundBIn (ys.flatMap frame) (List.replicate j true ++ (false :: rest)) (gs.flatMap frame) with hB0
  have b0 : ∀ t : Fin 292, 3 ≤ t.val → B0 t = [] := by
    intro t ht; simp only [hB0, roundBIn]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 1: the cell
  have d1 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock (fun _ : Fin 1 => (3 : Fin 292))
    (fun a b _ => Subsingleton.elim a b) (fun _ => 0) B0 (fun _ => rfl) (fun _ => b0 3 (by decide))
  rw [zeroH] at d1
  set B1 := install (fun _ : Fin 1 => (3 : Fin 292)) B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 292, t.val ≠ 3 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b13 : B1 3 = [false] := install_slot (fun _ : Fin 1 => (3 : Fin 292)) (fun a b _ => Subsingleton.elim a b) _ _ 0
  -- 2: the crop
  obtain ⟨o2, s2, c0, c1, c2, c3, c4, c5, c6, c7⟩ := cropBStage W ys hys [] j hj rest
  rw [List.append_nil] at c0
  have d2 := s2.dock cropSl cropSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro i; rw [cropBIn_val]
    fin_cases i
    · show B1 0 = _; rw [b1 _ (by decide)]; simp [hB0, roundBIn]
    · show B1 3 = _; rw [b13]; rfl
    · show B1 1 = _; rw [b1 _ (by decide)]; simp [hB0, roundBIn]
    all_goals (show B1 _ = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl))
  rw [zeroH] at d2
  set B2 := install cropSl B1 o2 with hB2
  have b2 : ∀ t : Fin 292, (∀ i, (cropSl i).val ≠ t.val) → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun i e => ht i (congrArg Fin.val e))
  have b2hit : ∀ i, B2 (cropSl i) = o2 i := fun i => install_slot _ cropSl_inj _ _ _
  have b2big : ∀ t : Fin 292, 10 ≤ t.val → B2 t = [] := by
    intro t ht
    rw [b2 _ (by intro i; rw [cropSl_val]; fin_cases i <;> simp <;> omega), b1 _ (by omega), b0 _ (by omega)]
  -- 3: the gate header
  obtain ⟨r3, -, hp3⟩ := CloseoutRowsGateHeader.header_run y
  have d3 := (FrontLoopKit.step_of_ready r3).dock ghSl ghSl_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro i; rw [CompetitorWitnessHeader.input_eq]
    by_cases h0 : i.val = 0
    · rw [if_pos h0, show ghSl i = cropSl 4 from Fin.ext (by simp [ghSl, h0]; rfl), b2hit, c4]; rfl
    · by_cases h1 : i.val = 1
      · rw [if_neg h0, if_pos h1, show ghSl i = cropSl 3 from Fin.ext (by simp [ghSl, h1]; rfl), b2hit, c3]
      · rw [if_neg h0, if_neg h1, b2big _ (by simp only [ghSl]; rw [if_neg h0, if_neg h1]; omega)])
  rw [zeroH] at d3
  set B3 := install ghSl B2 (CloseoutRowsGateHeader.output y) with hB3
  have b3 : ∀ t : Fin 292, (t.val < 4 ∨ 6 ≤ t.val ∧ t.val < 10 ∨ 156 ≤ t.val) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun i e => by
      have := congrArg Fin.val e; simp only [ghSl] at this; split_ifs at this <;> omega)
  have b3c0 : B3 46 = frame (cw y 0) := (install_slot ghSl ghSl_inj B2 _ 38).trans (hp3 0)
  have b3c1 : B3 86 = frame (cw y 1) := (install_slot ghSl ghSl_inj B2 _ 78).trans (hp3 1)
  -- 4: the first pair node, `Nat.pair v₁ 0`
  obtain ⟨o4, r4, t4⟩ := PCPPairCold.pair_run (cw y 1) []
  have d4 := (FrontLoopKit.step_of_ready r4).dock p1Sl p1Sl_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro i; rw [pairIn_val]
    by_cases h2 : i.val = 2
    · rw [if_pos h2, show p1Sl i = (86 : Fin 292) from Fin.ext (by simp [p1Sl, pSl, pv, h2]), b3c1]
    · by_cases h3 : i.val = 3
      · rw [if_neg h2, if_pos h3, show p1Sl i = cropSl 5 from Fin.ext (by simp [p1Sl, pSl, pv, h3]; rfl), b3 _ (by
          simp [cropSl]), b2hit, c5]; rfl
      · rw [if_neg h2, if_neg h3]
        have hr := pv_range 35 86 6 156 (by omega) i.val i.isLt h2 h3
        rw [b3 _ (by simp only [p1Sl, pSl]; omega), b2big _ (by simp only [p1Sl, pSl]; omega)])
  rw [zeroH] at d4
  set B4 := install p1Sl B3 o4 with hB4
  have b4 : ∀ t : Fin 292, (t.val < 156 ∧ t.val ≠ 86 ∧ t.val ≠ 6 ∨ 189 ≤ t.val) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun i e => by
      have := congrArg Fin.val e; have := i.isLt; simp only [p1Sl, pSl, pv] at *; split_ifs at * <;> omega)
  have b4o : B4 180 = frame (w1 y) := (install_slot p1Sl p1Sl_inj B3 o4 26).trans t4
  -- 5: the second pair node, `Nat.pair 1 ·`
  obtain ⟨o5, r5, t5⟩ := PCPPairCold.pair_run [true] (w1 y)
  have d5 := (FrontLoopKit.step_of_ready r5).dock p2Sl p2Sl_inj (fun _ => 0) B4 (fun _ => rfl) (by
    intro i; rw [pairIn_val]
    by_cases h2 : i.val = 2
    · rw [if_pos h2, show p2Sl i = cropSl 6 from Fin.ext (by simp [p2Sl, pSl, pv, h2]; rfl), b4 _ (by simp [cropSl]),
        b3 _ (by simp [cropSl]), b2hit, c6]; rfl
    · by_cases h3 : i.val = 3
      · rw [if_neg h2, if_pos h3, show p2Sl i = (180 : Fin 292) from Fin.ext (by simp [p2Sl, pSl, pv, h3]), b4o]
      · rw [if_neg h2, if_neg h3]
        have hr := pv_range 35 7 180 189 (by omega) i.val i.isLt h2 h3
        rw [b4 _ (by simp only [p2Sl, pSl]; omega), b3 _ (by simp only [p2Sl, pSl]; omega),
          b2big _ (by simp only [p2Sl, pSl]; omega)])
  rw [zeroH] at d5
  set B5 := install p2Sl B4 o5 with hB5
  have b5 : ∀ t : Fin 292, (t.val < 189 ∧ t.val ≠ 7 ∧ t.val ≠ 180 ∨ 222 ≤ t.val) → B5 t = B4 t := fun t ht =>
    install_other _ _ _ _ (fun i e => by
      have := congrArg Fin.val e; have := i.isLt; simp only [p2Sl, pSl, pv] at *; split_ifs at * <;> omega)
  have b5o : B5 213 = frame (w2 y) := (install_slot p2Sl p2Sl_inj B4 o5 26).trans t5
  -- 6: the third pair node, `Nat.pair v₀ ·`
  obtain ⟨o6, r6, t6⟩ := PCPPairCold.pair_run (cw y 0) (w2 y)
  have d6 := (FrontLoopKit.step_of_ready r6).dock p3Sl p3Sl_inj (fun _ => 0) B5 (fun _ => rfl) (by
    intro i; rw [pairIn_val]
    by_cases h2 : i.val = 2
    · rw [if_pos h2, show p3Sl i = (46 : Fin 292) from Fin.ext (by simp [p3Sl, pSl, pv, h2]), b5 _ (by decide),
        b4 _ (by decide), b3c0]
    · by_cases h3 : i.val = 3
      · rw [if_neg h2, if_pos h3, show p3Sl i = (213 : Fin 292) from Fin.ext (by simp [p3Sl, pSl, pv, h3]), b5o]
      · rw [if_neg h2, if_neg h3]
        have hr := pv_range 35 46 213 222 (by omega) i.val i.isLt h2 h3
        rw [b5 _ (by simp only [p3Sl, pSl]; omega), b4 _ (by simp only [p3Sl, pSl]; omega),
          b3 _ (by simp only [p3Sl, pSl]; omega), b2big _ (by simp only [p3Sl, pSl]; omega)])
  rw [zeroH] at d6
  set B6 := install p3Sl B5 o6 with hB6
  have b6 : ∀ t : Fin 292, (t.val < 222 ∧ t.val ≠ 46 ∧ t.val ≠ 213 ∨ 255 ≤ t.val) → B6 t = B5 t := fun t ht =>
    install_other _ _ _ _ (fun i e => by
      have := congrArg Fin.val e; have := i.isLt; simp only [p3Sl, pSl, pv] at *; split_ifs at * <;> omega)
  have b6o : B6 246 = frame (w3 y) := (install_slot p3Sl p3Sl_inj B5 o6 26).trans t6
  -- 7: the last pair node, `Nat.pair 1 ·`, in canonical binary
  obtain ⟨o7, r7, t7, -⟩ := PCPPairCanonical.pair_run [true] (w3 y) (by rw [pair4]; exact gc_pos y)
  have d7 := (FrontLoopKit.step_of_ready r7).dock p4Sl p4Sl_inj (fun _ => 0) B6 (fun _ => rfl) (by
    intro i; rw [canIn_val]
    by_cases h2 : i.val = 2
    · rw [if_pos h2, show p4Sl i = cropSl 7 from Fin.ext (by simp [p4Sl, pSl, pv, h2]; rfl), b6 _ (by simp [cropSl]),
        b5 _ (by simp [cropSl]), b4 _ (by simp [cropSl]), b3 _ (by simp [cropSl]), b2hit, c7]; rfl
    · by_cases h3 : i.val = 3
      · rw [if_neg h2, if_pos h3, show p4Sl i = (246 : Fin 292) from Fin.ext (by simp [p4Sl, pSl, pv, h3]), b6o]
      · rw [if_neg h2, if_neg h3]
        have hr := pv_range 38 8 246 255 (by omega) i.val i.isLt h2 h3
        rw [b6 _ (by simp only [p4Sl, pSl]; omega), b5 _ (by simp only [p4Sl, pSl]; omega),
          b4 _ (by simp only [p4Sl, pSl]; omega), b3 _ (by simp only [p4Sl, pSl]; omega),
          b2big _ (by simp only [p4Sl, pSl]; omega)])
  rw [zeroH] at d7
  set B7 := install p4Sl B6 o7 with hB7
  have b7 : ∀ t : Fin 292, (t.val < 255 ∧ t.val ≠ 8 ∧ t.val ≠ 246 ∨ 291 ≤ t.val) → B7 t = B6 t := fun t ht =>
    install_other _ _ _ _ (fun i e => by
      have := congrArg Fin.val e; have := i.isLt; simp only [p4Sl, pSl, pv] at *; split_ifs at * <;> omega)
  have b7o : B7 279 = frame (gc y).bits ++
      List.replicate (2 * PCPPair.width [true] (w3 y) + 1 - (frame (gc y).bits).length) false := by
    refine (install_slot p4Sl p4Sl_inj B6 o7 26).trans (t7.trans ?_)
    rw [pair4]; rfl
  -- 8: the append
  obtain ⟨o8, s8, a0, a1, a2⟩ := appendBStage gs hgs (gc y).bits
    (List.replicate (2 * PCPPair.width [true] (w3 y) + 1 - (frame (gc y).bits).length) false)
  have d8 := s8.dock abSl abSl_inj (fun _ => 0) B7 (fun _ => rfl) (by
    intro i; rw [appendBIn_val]
    fin_cases i
    · show B7 279 = _; rw [b7o]; rfl
    · show B7 3 = _; rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        show (3 : Fin 292) = cropSl 1 from rfl, b2hit, c1]; rfl
    · show B7 2 = _; rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        b2 _ (by intro k; rw [cropSl_val]; fin_cases k <;> decide), b1 _ (by decide)]; simp [hB0, roundBIn]
    · show B7 291 = _; rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide),
        b3 _ (by decide), b2big _ (by decide)]; rfl)
  rw [zeroH] at d8
  set B8 := install abSl B7 o8 with hB8
  have b8 : ∀ t : Fin 292, (∀ i, (abSl i).val ≠ t.val) → B8 t = B7 t := fun t ht =>
    install_other _ _ _ _ (fun i e => ht i (congrArg Fin.val e))
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq (d7.seq d8))))))
  have run' : Step workerB _ (fun _ => 0) B0 (fun _ => 0) B8 := run
  refine ⟨B8, FrontKit.ready_of_step (run'.enlarge (by unfold roundBCost; exact le_refl _)), ?_, ?_, ?_⟩
  · rw [b8 _ (by intro k; rw [abSl_val]; fin_cases k <;> decide), b7 _ (by decide), b6 _ (by decide),
      b5 _ (by decide), b4 _ (by decide), b3 _ (by decide), show (0 : Fin 292) = cropSl 0 from rfl, b2hit, c0]
  · rw [b8 _ (by intro k; rw [abSl_val]; fin_cases k <;> decide), b7 _ (by decide), b6 _ (by decide),
      b5 _ (by decide), b4 _ (by decide), b3 _ (by decide), show (1 : Fin 292) = cropSl 2 from rfl, b2hit, c2]
  · exact (install_slot abSl abSl_inj B7 o8 2).trans a2


/-! ## Loop B: every bottom -/

open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.WireExponent3_5.UnionMachine.CWRoundA (idleA idleA_ready prefix_flat_le pad_split pad_succ)

/-- The round's scratch: every tape but the bottoms, the counter and the accumulator. -/
def scrB (j : Fin 289) : Fin 292 := ⟨j.val + 3, by omega⟩

theorem scrB_inj : Function.Injective scrB := fun a b h => Fin.ext (by have := congrArg Fin.val h; simp [scrB] at this; omega)

theorem scrB_iff (t : Fin 292) : (∃ j, scrB j = t) ↔ 3 ≤ t.val := by
  constructor
  · rintro ⟨j, rfl⟩; simp [scrB]
  · intro h; exact ⟨⟨t.val - 3, by omega⟩, Fin.ext (by simp [scrB]; omega)⟩

/-- **Loop B.** -/
noncomputable def foldB := foldLoop (foldBody workerB scrB (idleA (292 + 2)))

/-- The atom codes of the first `j` bottoms, in canonical binary. -/
def gacc (ys : List (List Bool)) (j : ℕ) : List (List Bool) := (ys.take j).map fun y => (gc y).bits

theorem gacc_succ (ys : List (List Bool)) (j : ℕ) (hj : j < ys.length) :
    gacc ys (j + 1) = gacc ys j ++ [(gc ys[j]).bits] := by
  unfold gacc
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append, List.map_cons, List.map_nil]

theorem gacc_ne (ys : List (List Bool)) (j : ℕ) : ∀ g ∈ gacc ys j, g ≠ [] := by
  intro g hg
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hg
  exact gc_bits_ne y

theorem gacc_prefix (ys : List (List Bool)) (j : ℕ) : gacc ys j <+: gacc ys ys.length := by
  unfold gacc
  rw [List.take_length]
  exact (List.take_prefix j ys).map _

/-- The round's entry at bottom `j`. -/
def Qb (ys : List (List Bool)) (total j : ℕ) : Fin 292 → List Bool :=
  roundBIn (ys.flatMap frame) (ZeroPadding.pad total (List.replicate j true)) ((gacc ys j).flatMap frame)

/-- One round's uniform fuel: `c` bottoms of width `≤ W`, `TG` cells of atom codes. -/
def foldCwB (W c TG : ℕ) : ℕ :=
  1 + 1 + ((2 * (c * (5 * W + 8) + 14 * W + 50) + 2) + 1 + (27000 * (W + 1) ^ 2 + 1 +
    (1024 * (W + 1) ^ 2 + 1 + (1024 * (2 * W + 4) ^ 2 + 1 + (1024 * (5 * W + 9) ^ 2 + 1 +
      (1024 * (10 * W + 20) ^ 2 + 8 * (20 * W + 40) + 10 + 1 + (2 * (20 * TG + 7) + 2)))))))

theorem roundBCost_le (W : ℕ) (ys : List (List Bool)) (hys : ∀ y ∈ ys, y.length ≤ W) (j : ℕ) (hj : j < ys.length) :
    roundBCost j W ys[j] (gacc ys j) ≤ foldCwB W ys.length ((gacc ys ys.length).flatMap frame).length := by
  set y := ys[j] with hy
  have hyW : y.length ≤ W := hys _ (List.getElem_mem hj)
  have hpre := gacc_prefix ys (j + 1)
  rw [gacc_succ ys j hj] at hpre
  have hG := prefix_flat_le hpre
  rw [List.flatMap_append, List.length_append, ← hy] at hG
  have hbit : 2 * (gc y).bits.length + 1 ≤ ((gacc ys ys.length).flatMap frame).length := by
    have : ([(gc y).bits].flatMap frame).length = 2 * (gc y).bits.length + 1 := by
      simp [frame_eq_frameP]
    omega
  have p1 := PCPPairCold.budget_quadratic (cw y 1) []
  have p2 := PCPPairCold.budget_quadratic [true] (w1 y)
  have p3 := PCPPairCold.budget_quadratic (cw y 0) (w2 y)
  have p4 := PCPPairCold.budget_quadratic [true] (w3 y)
  rw [cw_length] at p1 p3
  rw [w1_len] at p2
  rw [w2_len] at p3
  rw [w3_len] at p4
  simp only [List.length_nil, List.length_cons] at p1 p2 p4
  have q1 : 1024 * (y.length + 0 + 1) ^ 2 ≤ 1024 * (W + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have q2 : 1024 * (0 + 1 + (2 * y.length + 2) + 1) ^ 2 ≤ 1024 * (2 * W + 4) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have q3 : 1024 * (y.length + (4 * y.length + 8) + 1) ^ 2 ≤ 1024 * (5 * W + 9) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have q4 : 1024 * (0 + 1 + (10 * y.length + 18) + 1) ^ 2 ≤ 1024 * (10 * W + 20) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have qh : 27000 * (y.length + 1) ^ 2 ≤ 27000 * (W + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hw4 : PCPPair.width [true] (w3 y) = 20 * y.length + 40 := by simp [PCPPair.width, w3_len]; ring
  have hc : j * (5 * W + 8) ≤ ys.length * (5 * W + 8) := Nat.mul_le_mul_right _ hj.le
  unfold roundBCost foldCwB cropBCost appendBCost PCPPairCanonical.budget CloseoutRowsGateHeader.budget
  rw [hw4]
  omega

/-- **Loop B is ready**: from the padded round tapes at bottom `0` and the unary count `|ys|`, the loop ends at the
padded round tapes at bottom `|ys|`: the atom codes of every bottom, in order. -/
theorem foldB_run (W : ℕ) (ys : List (List Bool)) (hys : ∀ y ∈ ys, y.length ≤ W) (total capT : ℕ)
    (hcap : total + 1 ≤ capT) (hc : ys.length ≤ total) (hS : (ys.flatMap frame).length ≤ total)
    (hG : ((gacc ys ys.length).flatMap frame).length ≤ total)
    (hcw : foldCwB W ys.length ((gacc ys ys.length).flatMap frame).length + 1 ≤ total) :
    ClockJoin.ReadyRun foldB
      (1 + 1 + (ys.length * (foldCwB W ys.length ((gacc ys ys.length).flatMap frame).length + 1 +
        (2 * total + 4 + 1 + 0) + 2) + ys.length + 3 + 1 + 1))
      (Fin.addCases (roundTapes (padScratch scrB total (Qb ys total 0)) total capT)
        (fun _ => CompareMachine.word ys.length))
      (Fin.addCases (roundTapes (padScratch scrB total (Qb ys total ys.length)) total capT)
        (fun _ => CompareMachine.word ys.length)) := by
  set cw := foldCwB W ys.length ((gacc ys ys.length).flatMap frame).length with hcw'
  have hround : ∀ j, ∃ out : Fin 292 → List Bool, j < ys.length →
      ClockJoin.ReadyRun workerB cw (Qb ys total j) out ∧
      out 0 = ys.flatMap frame ∧ out 1 = ZeroPadding.pad total (List.replicate (j + 1) true) ∧
      out 2 = (gacc ys (j + 1)).flatMap frame := by
    intro j
    by_cases hj : j < ys.length
    · obtain ⟨out, h1, h2, h3, h4⟩ := roundB_run W ys hys j hj (List.replicate (total - j - 1) false) (gacc ys j)
        (gacc_ne ys j)
      refine ⟨out, fun _ => ⟨?_, h2, by rw [h3, pad_succ total j], by rw [h4, gacc_succ ys j hj]⟩⟩
      unfold Qb; rw [pad_split total j (by omega)]
      exact ClockJoin.enlarge _ _ _ _ _ h1 (roundBCost_le W ys hys j hj)
    · exact ⟨fun _ => [], fun h => absurd h hj⟩
  choose Q' hQ' using hround
  have hlenQ : ∀ j, j ≤ ys.length → ∀ t, (Qb ys total j t).length ≤ total := by
    intro j hj t
    have hl2 := prefix_flat_le (gacc_prefix ys j)
    unfold Qb roundBIn
    split_ifs
    · exact hS
    · simp [ZeroPadding.pad]; omega
    · omega
    · simp
  have hwork : ∀ j, j < ys.length → ClockJoin.ReadyRun workerB cw (Qb ys total j) (Q' j) := fun j hj => (hQ' j hj).1
  exact uniformFold_ready workerB scrB scrB_inj (idleA (292 + 2)) total capT cw 0 ys.length hcap (Qb ys total) Q'
    hwork
    (fun j hj i => by
      have hl := ready_lengths (hwork j hj) total (hlenQ j hj.le) (scrB i)
      have : max total (cw + 1) = total := max_eq_left (by omega)
      omega)
    (fun j hj => by
      have e : blankScratch scrB (Q' j) = Qb ys total (j + 1) := by
        funext t
        unfold blankScratch
        by_cases ht : ∃ i, scrB i = t
        · rw [if_pos ht]
          have h3 := (scrB_iff t).mp ht
          unfold Qb roundBIn; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · rw [if_neg ht]
          have h3 : t.val < 3 := by by_contra hc'; exact ht ((scrB_iff t).mpr (by omega))
          obtain ⟨-, o0, o1, o2⟩ := hQ' j hj
          unfold Qb roundBIn
          by_cases h0 : t.val = 0
          · rw [if_pos h0, show t = 0 from Fin.ext h0, o0]
          · by_cases h1 : t.val = 1
            · rw [if_neg h0, if_pos h1, show t = 1 from Fin.ext h1, o1]
            · rw [if_neg h0, if_neg h1, if_pos (by omega), show t = 2 from Fin.ext (by omega), o2]
      rw [e]; exact idleA_ready _ _)

end NearCubicWires.WireExponent3_5.UnionMachine.CWRoundB
