import Proof.Wire_3_5.UnionMachine.CWEnvChk
import Proof.Wire_3_5.UnionMachine.CWRoundB

/-! # C6 front, U5, the code writers: the envelope loop over a carrier's atoms

A named carrier is within the envelope when every one of its atoms (gates) has at most `L = (n+1)^deg` description
bits (P3:3083-3094). The carrier's code lists its atoms' codes; base's balanced traversal writes them as framed words
`y`. One ROUND of the loop checks atom `j` on `1010` tapes:
* `0` the atoms' words, `1` the round counter, `2` the flag `[b]`, `3` the ruler `1^L`, `4` the cell;
* the crop (`CWWords.cropBW`): atom `j` framed on `5`;
* base's gate field stage (`CloseoutRowsGateFields`, 998 tapes) on it: the weights' `intWord`s on `371`, their count
  on `378`, the threshold's `natWord` on `818`;
* the gate check (`CWEnvChk.envChkW`): the flag becomes `[b && decide (pbits y ≤ L)]`.

Paper quantity of the main type (**`roundE_run`**, **`foldE_run`**): the envelope bit of the atoms,
`[b && decide (∀ y, pbits y ≤ L)]`, `pbits y` the atom's description bits read from its code's fields. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWEnvRound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords NearCubicWires.WireExponent3_5.UnionMachine.CWEnvChk
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready FrontKit.ready_of_step)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-! ## An atom word's description bits -/

/-- The weights read from an atom word's first field. -/
def wsOf (y : List Bool) : List ℤ := (CanonicalBinary.decodeIntList (value (CWRoundB.cw y 0))).getD []

/-- The threshold read from an atom word's second field. -/
def thOf (y : List Bool) : ℤ := (CanonicalBinary.decodeInt (value (CWRoundB.cw y 1))).getD 0

/-- **The atom's description bits**, read from its fields. -/
def pbits (y : List Bool) : ℕ := wbits (wsOf y) + natBitLength (thOf y).natAbs

/-- Both fields decode. -/
def Dec (y : List Bool) : Prop :=
  (CanonicalBinary.decodeIntList (value (CWRoundB.cw y 0))).isSome = true ∧
    (CanonicalBinary.decodeInt (value (CWRoundB.cw y 1))).isSome = true

theorem intWord_len (z : ℤ) : (intWord z).length = 2 * natBitLength z.natAbs + 2 := by
  unfold intWord; rw [List.length_cons, natWord_len]

theorem flat_len : ∀ ws : List ℤ, (ws.flatMap intWord).length = 2 * wbits ws + 2 * ws.length
  | [] => by simp [wbits]
  | z :: ws => by
    rw [List.flatMap_cons, List.length_append, intWord_len, flat_len ws]
    simp [wbits]; ring

/-! ## The layout -/

def cellSl : Fin 1 → Fin 1010 := fun _ => 4
def cropSl : Fin 9 → Fin 1010 := ![0, 4, 1, 5, 6, 7, 8, 9, 10]
def fdSl (j : Fin 998) : Fin 1010 := ⟨if j.val = 1 then 5 else if j.val = 0 then 11 else j.val + 10, by split_ifs <;> omega⟩
def chkSl : Fin 8 → Fin 1010 := ![371, 4, 818, 378, 3, 2, 1008, 1009]

theorem cellSl_inj : Function.Injective cellSl := fun a b _ => Subsingleton.elim a b
theorem cropSl_inj : Function.Injective cropSl := by decide
theorem chkSl_inj : Function.Injective chkSl := by decide
theorem fdSl_inj : Function.Injective fdSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [fdSl] at hv; apply Fin.ext; split_ifs at hv <;> omega

theorem cropSl_val (j : Fin 9) : (cropSl j).val = [0, 4, 1, 5, 6, 7, 8, 9, 10].getD j.val 0 := by
  fin_cases j <;> rfl
theorem chkSl_val (j : Fin 8) : (chkSl j).val = [371, 4, 818, 378, 3, 2, 1008, 1009].getD j.val 0 := by
  fin_cases j <;> rfl

noncomputable def cellR := RecoveryFocus.machine cellSl NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def cropR := RecoveryFocus.machine cropSl (Rewind.machine cropBW.toProg.compile)
noncomputable def fdR := RecoveryFocus.machine fdSl CloseoutRowsGateFields.machine
noncomputable def chkR := RecoveryFocus.machine chkSl (Rewind.machine envChkW.toProg.compile)

/-- **The envelope round worker.** -/
noncomputable def workerE := Composition.machine cellR (Composition.machine cropR (Composition.machine fdR chkR))

/-- The round's entry: the atoms, the counter, the flag, the ruler; every other tape blank. -/
def roundEIn (S K F E : List Bool) : Fin 1010 → List Bool :=
  fun t => if t.val = 0 then S else if t.val = 1 then K else if t.val = 2 then F else if t.val = 3 then E else []

theorem zeroH (t : ℕ) (sl : Fin t → Fin 1010) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- The gate fields stage's bound at width `W`. -/
def fB (W : ℕ) : ℕ := 4000000000000000000000000 * (W + 2) ^ 26

/-- One round's uniform fuel: `c` atoms of width `≤ W`. -/
def foldCwE (W c : ℕ) : ℕ :=
  1 + 1 + ((2 * (c * (5 * W + 8) + 14 * W + 50) + 2) + 1 + (fB W + 1 + (2 * (8 * (2 * (fB W + 2 * W + 2)) + 20) + 2)))

theorem fB_mono (y : List Bool) (W : ℕ) (hy : y.length ≤ W) : CloseoutRowsGateFields.budget y ≤ fB W :=
  (CloseoutRowsGateFields.budget_bound y).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

/-- **One envelope round**: atom `i`'s check conjoined into the flag; the counter advances. -/
theorem roundE_run (ys : List (List Bool)) (W : ℕ) (hys : ∀ y ∈ ys, y.length ≤ W) (c i : ℕ) (hi : i < ys.length)
    (hic : i < c) (hdec : Dec ys[i]) (rest : List Bool) (b : Bool) (L : ℕ) :
    ∃ out, ClockJoin.ReadyRun workerE (foldCwE W c)
        (roundEIn (ys.flatMap frame) (List.replicate i true ++ (false :: rest)) [b] (List.replicate L true)) out ∧
      out 0 = ys.flatMap frame ∧ out 1 = List.replicate (i + 1) true ++ rest ∧
      out 2 = [b && decide (pbits ys[i] ≤ L)] ∧ out 3 = List.replicate L true := by
  set y := ys[i] with hy
  have hyW : y.length ≤ W := hys _ (List.getElem_mem hi)
  set B0 := roundEIn (ys.flatMap frame) (List.replicate i true ++ (false :: rest)) [b] (List.replicate L true) with hB0
  have b0 : ∀ t : Fin 1010, 4 ≤ t.val → B0 t = [] := by
    intro t ht; simp only [hB0, roundEIn]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 1: the cell
  have d1 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock cellSl cellSl_inj (fun _ => 0) B0 (fun _ => rfl)
    (fun _ => b0 4 (by decide))
  rw [zeroH] at d1
  set B1 := install cellSl B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 1010, t.val ≠ 4 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b14 : B1 4 = [false] := install_slot cellSl cellSl_inj _ _ 0
  -- 2: the crop
  obtain ⟨o2, s2, c0, c1, c2, c3, -, -, -, -⟩ := cropBStage W ys hys [] i hi rest
  rw [List.append_nil] at s2 c0
  have d2 := s2.dock cropSl cropSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [cropBIn_val]
    fin_cases j
    · show B1 0 = _; rw [b1 _ (by decide)]; simp [hB0, roundEIn]
    · show B1 4 = _; rw [b14]; rfl
    · show B1 1 = _; rw [b1 _ (by decide)]; simp [hB0, roundEIn]
    · show B1 5 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 6 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 7 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 8 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 9 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 10 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl)
  rw [zeroH] at d2
  set B2 := install cropSl B1 o2 with hB2
  have b2 : ∀ t : Fin 1010, (∀ j, (cropSl j).val ≠ t.val) → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have b2hit : ∀ j, B2 (cropSl j) = o2 j := fun j => install_slot _ cropSl_inj _ _ _
  have b2big : ∀ t : Fin 1010, 11 ≤ t.val → B2 t = [] := by
    intro t ht
    rw [b2 _ (by intro j; rw [cropSl_val]; fin_cases j <;> simp <;> omega), b1 _ (by omega), b0 _ (by omega)]
  have b2y : B2 5 = frame y := by rw [show (5 : Fin 1010) = cropSl 3 from rfl, b2hit, c3]
  -- 3: the gate fields
  obtain ⟨o3, r3, -, -, -, -, -, -, -, -, -, hw3, ht3, -⟩ := CloseoutRowsGateFields.fields_run y
  obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hdec.1
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hdec.2
  have hws : wsOf y = vs := by unfold wsOf; rw [hvs]; rfl
  have hth : thOf y = z := by unfold thOf; rw [hz]; rfl
  obtain ⟨o361, o368⟩ := hw3 vs hvs
  have o808 := ht3 z hz
  have hlen3 := NearCubicWires.WireExponent3_5.Transfer.ready_lengths r3 (2 * y.length + 1) (by
    intro k; unfold CloseoutRowsGateFields.input; split_ifs
    · rw [frame_eq_frameP]; simp
    · simp)
  have d3 := (FrontLoopKit.step_of_ready r3).dock fdSl fdSl_inj (fun _ => 0) B2
    (fun _ => rfl) (by
      intro j
      show B2 (fdSl j) = (if j.val = 1 then frame y else [])
      by_cases h1 : j.val = 1
      · rw [if_pos h1, show fdSl j = (5 : Fin 1010) from Fin.ext (by simp [fdSl, h1]), b2y]
      · rw [if_neg h1, b2big _ (by simp only [fdSl]; split_ifs <;> omega)])
  rw [zeroH] at d3
  set B3 := install fdSl B2 o3 with hB3
  have b3 : ∀ t : Fin 1010, (t.val < 5 ∨ (5 < t.val ∧ t.val < 11) ∨ 1008 ≤ t.val) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [fdSl] at hv; have hj := j.isLt; split_ifs at hv <;> omega)
  have b3A : B3 371 = vs.flatMap intWord := (install_slot fdSl fdSl_inj B2 o3 361).trans o361
  have b3C : B3 378 = CompareMachine.word vs.length := (install_slot fdSl fdSl_inj B2 o3 368).trans o368
  have b3T : B3 818 = natWord z.natAbs := (install_slot fdSl fdSl_inj B2 o3 808).trans o808
  -- 4: the gate check
  obtain ⟨o4, s4, -, -, -, -, a4, a5⟩ := envChkStage vs z.natAbs L b
  have d4 := s4.dock chkSl chkSl_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro j; rw [envIn_val]
    fin_cases j
    · show B3 371 = _; rw [b3A]; rfl
    · show B3 4 = _; rw [b3 _ (by decide), show (4 : Fin 1010) = cropSl 1 from rfl, b2hit, c1]; rfl
    · show B3 818 = _; rw [b3T]; rfl
    · show B3 378 = _; rw [b3C]; rfl
    · show B3 3 = _
      rw [b3 _ (by decide), b2 _ (by intro k; rw [cropSl_val]; fin_cases k <;> decide), b1 _ (by decide)]
      simp [hB0, roundEIn]
    · show B3 2 = _
      rw [b3 _ (by decide), b2 _ (by intro k; rw [cropSl_val]; fin_cases k <;> decide), b1 _ (by decide)]
      simp [hB0, roundEIn]
    · show B3 1008 = _; rw [b3 _ (by decide), b2big _ (by decide)]; rfl
    · show B3 1009 = _; rw [b3 _ (by decide), b2big _ (by decide)]; rfl)
  rw [zeroH] at d4
  set B4 := install chkSl B3 o4 with hB4
  have b4 : ∀ t : Fin 1010, (∀ j, (chkSl j).val ≠ t.val) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  -- the cost
  have hB := fB_mono y W hyW
  have l361 := hlen3 361
  have l808 := hlen3 808
  rw [o361, flat_len] at l361
  rw [o808, natWord_len] at l808
  have hmax : max (2 * y.length + 1) (CloseoutRowsGateFields.budget y + 1) ≤ fB W + 2 * W + 2 := by omega
  have hcost : 2 * cropBCost i W + 2 + 1 + (CloseoutRowsGateFields.budget y + 1 + (2 * envChkCost vs z.natAbs + 2)) ≤
      2 * (c * (5 * W + 8) + 14 * W + 50) + 2 + 1 + (fB W + 1 + (2 * (8 * (2 * (fB W + 2 * W + 2)) + 20) + 2)) := by
    have hc : i * (5 * W + 8) ≤ c * (5 * W + 8) := Nat.mul_le_mul_right _ hic.le
    unfold cropBCost envChkCost
    omega
  have run := d1.seq (d2.seq (d3.seq d4))
  have run' : Step workerE _ (fun _ => 0) B0 (fun _ => 0) B4 := run
  refine ⟨B4, FrontKit.ready_of_step (run'.enlarge (by unfold foldCwE; omega)), ?_, ?_, ?_, ?_⟩
  · rw [b4 _ (by intro k; rw [chkSl_val]; fin_cases k <;> decide), b3 _ (by decide),
      show (0 : Fin 1010) = cropSl 0 from rfl, b2hit, c0]
  · rw [b4 _ (by intro k; rw [chkSl_val]; fin_cases k <;> decide), b3 _ (by decide),
      show (1 : Fin 1010) = cropSl 2 from rfl, b2hit, c2]
  · rw [show (2 : Fin 1010) = chkSl 5 from rfl]
    refine (install_slot chkSl chkSl_inj B3 o4 5).trans (a5.trans ?_)
    unfold pbits; rw [hws, hth]
  · rw [show (3 : Fin 1010) = chkSl 4 from rfl]
    exact (install_slot chkSl chkSl_inj B3 o4 4).trans a4

/-! ## The loop: every atom -/

open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.CWRoundA (idleA idleA_ready pad_split pad_succ)

/-- The round's scratch: every tape but the atoms, the counter, the flag and the ruler. -/
def scrE (j : Fin 1006) : Fin 1010 := ⟨j.val + 4, by omega⟩

theorem scrE_inj : Function.Injective scrE := fun a b h => Fin.ext (by have := congrArg Fin.val h; simp [scrE] at this; omega)

theorem scrE_iff (t : Fin 1010) : (∃ j, scrE j = t) ↔ 4 ≤ t.val := by
  constructor
  · rintro ⟨j, rfl⟩; simp [scrE]
  · intro h; exact ⟨⟨t.val - 4, by omega⟩, Fin.ext (by simp [scrE]; omega)⟩

/-- **The envelope loop.** -/
noncomputable def foldE := foldLoop (foldBody workerE scrE (idleA (1010 + 2)))

/-- The flag after the first `i` atoms, from the flag `b0`. -/
def flagAt (ys : List (List Bool)) (b0 : Bool) (L i : ℕ) : Bool := b0 && (ys.take i).all fun y => decide (pbits y ≤ L)

theorem flagAt_succ (ys : List (List Bool)) (b0 : Bool) (L i : ℕ) (hi : i < ys.length) :
    flagAt ys b0 L (i + 1) = (flagAt ys b0 L i && decide (pbits ys[i] ≤ L)) := by
  unfold flagAt
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.all_append]
  simp [Bool.and_assoc]

/-- The round's entry at atom `i`. -/
def Qe (ys : List (List Bool)) (b0 : Bool) (L total i : ℕ) : Fin 1010 → List Bool :=
  roundEIn (ys.flatMap frame) (ZeroPadding.pad total (List.replicate i true)) [flagAt ys b0 L i] (List.replicate L true)

/-- **The envelope loop is ready**: from the padded round tapes at atom `0` and the unary count, the loop ends at
the padded round tapes at atom `|ys|`: the flag `b0` conjoined with every atom's check. -/
theorem foldE_run (ys : List (List Bool)) (W : ℕ) (hys : ∀ y ∈ ys, y.length ≤ W) (hdec : ∀ y ∈ ys, Dec y)
    (b0 : Bool) (L total capT : ℕ) (hcap : total + 1 ≤ capT) (hc : ys.length ≤ total)
    (hS : (ys.flatMap frame).length ≤ total) (hL : L ≤ total) (hcw : foldCwE W ys.length + 1 ≤ total) :
    ClockJoin.ReadyRun foldE
      (1 + 1 + (ys.length * (foldCwE W ys.length + 1 + (2 * total + 4 + 1 + 0) + 2) + ys.length + 3 + 1 + 1))
      (Fin.addCases (roundTapes (padScratch scrE total (Qe ys b0 L total 0)) total capT)
        (fun _ => CompareMachine.word ys.length))
      (Fin.addCases (roundTapes (padScratch scrE total (Qe ys b0 L total ys.length)) total capT)
        (fun _ => CompareMachine.word ys.length)) := by
  set cw := foldCwE W ys.length with hcw'
  have hround : ∀ i, ∃ out : Fin 1010 → List Bool, i < ys.length →
      ClockJoin.ReadyRun workerE cw (Qe ys b0 L total i) out ∧
      out 0 = ys.flatMap frame ∧ out 1 = ZeroPadding.pad total (List.replicate (i + 1) true) ∧
      out 2 = [flagAt ys b0 L (i + 1)] ∧ out 3 = List.replicate L true := by
    intro i
    by_cases hi : i < ys.length
    · obtain ⟨out, h1, h2, h3, h4, h5⟩ := roundE_run ys W hys ys.length i hi hi (hdec _ (List.getElem_mem hi))
        (List.replicate (total - i - 1) false) (flagAt ys b0 L i) L
      refine ⟨out, fun _ => ⟨?_, h2, by rw [h3, pad_succ total i], by rw [h4, flagAt_succ ys b0 L i hi], h5⟩⟩
      unfold Qe; rw [pad_split total i (by omega)]
      exact h1
    · exact ⟨fun _ => [], fun h => absurd h hi⟩
  choose Q' hQ' using hround
  have hlenQ : ∀ i, i ≤ ys.length → ∀ t, (Qe ys b0 L total i t).length ≤ total := by
    intro i hi t
    unfold Qe roundEIn
    split_ifs
    · exact hS
    · simp [ZeroPadding.pad]; omega
    · simp; omega
    · simp; omega
    · simp
  have hwork : ∀ i, i < ys.length → ClockJoin.ReadyRun workerE cw (Qe ys b0 L total i) (Q' i) :=
    fun i hi => (hQ' i hi).1
  exact uniformFold_ready workerE scrE scrE_inj (idleA (1010 + 2)) total capT cw 0 ys.length hcap
    (Qe ys b0 L total) Q' hwork
    (fun i hi j => by
      have hl := ready_lengths (hwork i hi) total (hlenQ i hi.le) (scrE j)
      have : max total (cw + 1) = total := max_eq_left (by omega)
      omega)
    (fun i hi => by
      have e : blankScratch scrE (Q' i) = Qe ys b0 L total (i + 1) := by
        funext t
        unfold blankScratch
        by_cases ht : ∃ j, scrE j = t
        · rw [if_pos ht]
          have h4 := (scrE_iff t).mp ht
          unfold Qe roundEIn; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · rw [if_neg ht]
          have h4 : t.val < 4 := by by_contra hc'; exact ht ((scrE_iff t).mpr (by omega))
          obtain ⟨-, o0, o1, o2, o3⟩ := hQ' i hi
          unfold Qe roundEIn
          by_cases h0 : t.val = 0
          · rw [if_pos h0, show t = 0 from Fin.ext h0, o0]
          · by_cases h1 : t.val = 1
            · rw [if_neg h0, if_pos h1, show t = 1 from Fin.ext h1, o1]
            · by_cases h2 : t.val = 2
              · rw [if_neg h0, if_neg h1, if_pos h2, show t = 2 from Fin.ext h2, o2]
              · rw [if_neg h0, if_neg h1, if_neg h2, if_pos (by omega), show t = 3 from Fin.ext (by omega), o3]
      rw [e]; exact idleA_ready _ _)

end NearCubicWires.WireExponent3_5.UnionMachine.CWEnvRound
