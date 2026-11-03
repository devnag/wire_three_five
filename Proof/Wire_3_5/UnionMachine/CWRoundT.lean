import Proof.Wire_3_5.UnionMachine.CWRoundA
import Proof.Wire_3_5.UnionMachine.CWSel
import Proof.CaseAnalysis.RowsGateHeader

/-! # C6 front, U5, the code writers: loop A's round for `THR∘THR` circuits — the retained bottoms

The charged gates of a `THR∘THR` circuit are its bottoms at the top's support (`Stars.thrGates`, P3:3401-3410). A
circuit's code is the tagged list `[family tag, bottom count, bottoms, top]` (`CarrierFormat.thr_fields`),
the top a supported gate whose code is the tagged list `[weights, threshold, support bitmap]`. One ROUND handles circuit
`i` on `743` tapes, loop A's round (`CWRoundA`) followed by the selection:
* `0` the fields `frame u`, `1` the round counter, `2` the retained-bottom accumulator, `3` its count, `4` the cell;
* the crop, base's circuit header and base's traversal of field 2 as in `CWRoundA` (the same slots);
* a second cell `[false]` on `422` (the gate header's constant), base's gate header (`CloseoutRowsGateHeader`, 148
  tapes) on field 3, base's traversal of the gate's field 2 (the support bitmap), and the selection (`CWSel.selW`).

Paper quantity of the main type (**`roundT_run`**): the retained bottoms `bwT x` of circuit `i`, appended with their
count. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWRoundT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords NearCubicWires.WireExponent3_5.UnionMachine.CWSel
open NearCubicWires.WireExponent3_5.UnionMachine.CWRoundA (fld bw fld_length bw_ne stream_bw hdIn_val idleA idleA_ready
  bacc bacc_succ bacc_prefix bacc_ne prefix_flat_le pad_split pad_succ)
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready FrontKit.ready_of_step)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## One circuit's retained bottoms -/

/-- The top's field word of the circuit with code `x`: field 3 of its payload. -/
def top (x : ℕ) : List Bool := CloseoutRowsCircuitHeader.codeWord (pay x) 3

/-- The top's support field word: field 2 of the top's code. -/
def supw (x : ℕ) : List Bool := CloseoutRowsGateHeader.codeWord (top x) 2

/-- **The selectors**: the atoms of the support field, at its width. -/
def sels (x : ℕ) : List (List Bool) :=
  (PCPPNativeCanonicalTree.tree (RadixSemantics.value (supw x))).atoms.map (binary (supw x).length)

/-- The (bottom word, selector) pairs of circuit `x`. -/
def pairs (x : ℕ) : List (List Bool × List Bool) := (bw x).zip (sels x)

/-- **The retained bottoms' words** of the circuit with code `x`. -/
def bwT (x : ℕ) : List (List Bool) := selOf (pairs x)

theorem top_length (x : ℕ) : (top x).length = natBitLength x := by
  unfold top CloseoutRowsCircuitHeader.codeWord
  rw [(RecoveryFixedUnpair.word_lengths _).1, CompetitorWitnessTriple.word_length, pay_length]

theorem supw_length (x : ℕ) : (supw x).length = natBitLength x := by
  unfold supw CloseoutRowsGateHeader.codeWord
  rw [(RecoveryFixedUnpair.word_lengths _).1, CompetitorWitnessTriple.word_length, top_length]

theorem sels_ne (x : ℕ) : ∀ w ∈ sels x, w ≠ [] := by
  intro w hw
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hw
  intro h
  have h1 := congrArg List.length h
  rw [binary_length, supw_length, List.length_nil] at h1
  have := natBitLength_pos x
  omega

theorem stream_sels (x : ℕ) :
    PCPPNativeCanonicalWalk.atomStream (supw x).length
      (PCPPNativeCanonicalTree.tree (RadixSemantics.value (supw x))).atoms = (sels x).flatMap frame := by
  unfold PCPPNativeCanonicalWalk.atomStream sels
  rw [List.flatMap_map]

theorem pairs_fst (x : ℕ) (h : (sels x).length = (bw x).length) : (pairs x).map Prod.fst = bw x := by
  unfold pairs; exact List.map_fst_zip (by omega)

theorem pairs_snd (x : ℕ) (h : (sels x).length = (bw x).length) : (pairs x).map Prod.snd = sels x := by
  unfold pairs; exact List.map_snd_zip (by omega)

theorem pairs_sel_ne (x : ℕ) : ∀ p ∈ pairs x, p.2 ≠ [] := by
  intro p hp
  exact sels_ne x p.2 (List.of_mem_zip hp).2

theorem selOf_sublist : ∀ ps : List (List Bool × List Bool), List.Sublist (selOf ps) (ps.map Prod.fst)
  | [] => by simp [selOf_nil]
  | p :: ps => by
    rw [selOf_cons, List.map_cons]
    by_cases h : selBit p.2 = true
    · rw [if_pos h]; exact (selOf_sublist ps).cons_cons p.1
    · rw [if_neg h]; exact (selOf_sublist ps).cons p.1

theorem bwT_sublist (x : ℕ) (h : (sels x).length = (bw x).length) : List.Sublist (bwT x) (bw x) := by
  have hs := selOf_sublist (pairs x)
  rw [pairs_fst x h] at hs
  exact hs

/-! ## The layout -/

def cellSl : Fin 1 → Fin 743 := fun _ => 4
def cropSl : Fin 7 → Fin 743 := ![0, 4, 1, 5, 6, 7, 8]
def hdSl (j : Fin 242) : Fin 743 := ⟨if j.val = 0 then 7 else if j.val = 1 then 5 else j.val + 7, by split_ifs <;> omega⟩
def trSl (j : Fin 174) : Fin 743 := ⟨if j.val = 0 then 125 else j.val + 248, by split_ifs <;> omega⟩
def cell2Sl : Fin 1 → Fin 743 := fun _ => 422
def ghSl (j : Fin 148) : Fin 743 :=
  ⟨if j.val = 0 then 422 else if j.val = 1 then 165 else j.val + 421, by split_ifs <;> omega⟩
def tr2Sl (j : Fin 174) : Fin 743 := ⟨if j.val = 0 then 539 else j.val + 568, by split_ifs <;> omega⟩
def selSl : Fin 6 → Fin 743 := ![278, 4, 598, 2, 3, 742]

theorem cellSl_inj : Function.Injective cellSl := fun a b _ => Subsingleton.elim a b
theorem cell2Sl_inj : Function.Injective cell2Sl := fun a b _ => Subsingleton.elim a b
theorem cropSl_inj : Function.Injective cropSl := by decide
theorem selSl_inj : Function.Injective selSl := by decide
theorem hdSl_inj : Function.Injective hdSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [hdSl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem trSl_inj : Function.Injective trSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [trSl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem ghSl_inj : Function.Injective ghSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [ghSl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem tr2Sl_inj : Function.Injective tr2Sl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [tr2Sl] at hv; apply Fin.ext; split_ifs at hv <;> omega

theorem cropSl_val (j : Fin 7) : (cropSl j).val = [0, 4, 1, 5, 6, 7, 8].getD j.val 0 := by fin_cases j <;> rfl
theorem selSl_val (j : Fin 6) : (selSl j).val = [278, 4, 598, 2, 3, 742].getD j.val 0 := by fin_cases j <;> rfl

noncomputable def cellR := RecoveryFocus.machine cellSl NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def cropR := RecoveryFocus.machine cropSl (Rewind.machine cropAW.toProg.compile)
noncomputable def hdR := RecoveryFocus.machine hdSl CloseoutRowsCircuitHeader.machine
noncomputable def trR := RecoveryFocus.machine trSl CloseoutWitness.CanonicalTest.machine
noncomputable def cell2R := RecoveryFocus.machine cell2Sl NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def ghR := RecoveryFocus.machine ghSl CloseoutRowsGateHeader.machine
noncomputable def tr2R := RecoveryFocus.machine tr2Sl CloseoutWitness.CanonicalTest.machine
noncomputable def selR := RecoveryFocus.machine selSl (Rewind.machine selW.toProg.compile)

/-- **The `THR∘THR` round worker.** -/
noncomputable def workerT :=
  Composition.machine cellR (Composition.machine cropR (Composition.machine hdR (Composition.machine trR
    (Composition.machine cell2R (Composition.machine ghR (Composition.machine tr2R selR))))))

/-- The round's entry: the fields, the counter, the two accumulators; every other tape blank. -/
def roundTIn (S K B N : List Bool) : Fin 743 → List Bool :=
  fun t => if t.val = 0 then S else if t.val = 1 then K else if t.val = 2 then B else if t.val = 3 then N else []

theorem zeroH (t : ℕ) (sl : Fin t → Fin 743) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- The round's fuel. -/
noncomputable def roundTCost (i W : ℕ) (x : ℕ) (Bw : List (List Bool)) (n : ℕ) : ℕ :=
  1 + 1 + ((2 * cropACost i W + 2) + 1 + (CloseoutRowsCircuitHeader.budget (pay x) + 1 +
    (CloseoutWitness.CanonicalTest.budget (fld x) + 1 + (1 + 1 + (CloseoutRowsGateHeader.budget (top x) + 1 +
      (CloseoutWitness.CanonicalTest.budget (supw x) + 1 + (2 * selWCost (pairs x) Bw n + 2)))))))

/-- **One `THR∘THR` round**: circuit `i`'s retained bottoms join the accumulator, their count the count; the counter
advances. -/
theorem roundT_run (xs : List ℕ) (W : ℕ) (hW : ∀ x ∈ xs, natBitLength x ≤ W) (i : ℕ) (hi : i < xs.length)
    (hsel : (sels xs[i]).length = (bw xs[i]).length)
    (rest : List Bool) (Bw : List (List Bool)) (hBw : ∀ b ∈ Bw, b ≠ []) (n : ℕ) :
    ∃ out, ClockJoin.ReadyRun workerT (roundTCost i W xs[i] Bw n)
        (roundTIn ((xs.map nf).flatten ++ [false]) (List.replicate i true ++ (false :: rest)) (Bw.flatMap frame)
          (false :: List.replicate n true)) out ∧
      out 0 = (xs.map nf).flatten ++ [false] ∧ out 1 = List.replicate (i + 1) true ++ rest ∧
      out 2 = (Bw ++ bwT xs[i]).flatMap frame ∧ out 3 = false :: List.replicate (n + (bwT xs[i]).length) true := by
  set x := xs[i] with hx
  set S := (xs.map nf).flatten ++ [false] with hS
  set B0 := roundTIn S (List.replicate i true ++ (false :: rest)) (Bw.flatMap frame) (false :: List.replicate n true)
    with hB0
  have b0 : ∀ t : Fin 743, 4 ≤ t.val → B0 t = [] := by
    intro t ht; simp only [hB0, roundTIn]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 1: the cell
  have d1 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock cellSl cellSl_inj (fun _ => 0) B0 (fun _ => rfl)
    (fun _ => b0 4 (by decide))
  rw [zeroH] at d1
  set B1 := install cellSl B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 743, t.val ≠ 4 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b14 : B1 4 = [false] := install_slot cellSl cellSl_inj _ _ 0
  -- 2: the crop
  obtain ⟨o2, s2, c0, c1, c2, c3, ⟨r2, c4⟩, c5⟩ := cropAStage xs W hW [false] i hi rest
  have d2 := s2.dock cropSl cropSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [cropAIn_val]
    fin_cases j
    · show B1 0 = _; rw [b1 _ (by decide)]; simp [hB0, roundTIn, hS]
    · show B1 4 = _; rw [b14]; rfl
    · show B1 1 = _; rw [b1 _ (by decide)]; simp [hB0, roundTIn]
    · show B1 5 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 6 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 7 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 8 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl)
  rw [zeroH] at d2
  set B2 := install cropSl B1 o2 with hB2
  have b2 : ∀ t : Fin 743, (∀ j, (cropSl j).val ≠ t.val) → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have b2hit : ∀ j, B2 (cropSl j) = o2 j := fun j => install_slot _ cropSl_inj _ _ _
  have b2big : ∀ t : Fin 743, 9 ≤ t.val → B2 t = [] := by
    intro t ht
    rw [b2 _ (by intro j; rw [cropSl_val]; fin_cases j <;> simp <;> omega), b1 _ (by omega), b0 _ (by omega)]
  -- 3: the circuit header
  obtain ⟨o3, r3⟩ := CloseoutRowsCircuitHeader.header_run (pay x)
  obtain ⟨r3, hp3⟩ := r3
  have d3 := (FrontLoopKit.step_of_ready r3).dock hdSl hdSl_inj (fun _ => 0) B2
    (fun _ => rfl) (by
      intro j; rw [hdIn_val]
      by_cases h0 : j.val = 0
      · rw [if_pos h0, show hdSl j = cropSl 5 from Fin.ext (by simp [hdSl, h0]; rfl), b2hit, c5]
      · by_cases h1 : j.val = 1
        · rw [if_neg h0, if_pos h1, show hdSl j = cropSl 3 from Fin.ext (by simp [hdSl, h1]; rfl), b2hit, c3]
        · rw [if_neg h0, if_neg h1, b2big _ (by simp only [hdSl]; rw [if_neg h0, if_neg h1]; omega)])
  rw [zeroH] at d3
  set B3 := install hdSl B2 o3 with hB3
  have b3 : ∀ t : Fin 743, (t.val < 5 ∨ t.val = 6 ∨ t.val = 8 ∨ 249 ≤ t.val) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have := congrArg Fin.val e; simp only [hdSl] at this; split_ifs at this <;> omega)
  have b3port : B3 125 = frame (fld x) := (install_slot hdSl hdSl_inj B2 o3 118).trans (hp3 2)
  have b3top : B3 165 = frame (top x) := (install_slot hdSl hdSl_inj B2 o3 158).trans (hp3 3)
  -- 4: the traversal of field 2
  obtain ⟨o4, r4, t30, t41, -⟩ := CloseoutWitness.CanonicalTest.fields_run (fld x)
  have d4 := (FrontLoopKit.step_of_ready r4).dock trSl trSl_inj (fun _ => 0) B3
    (fun _ => rfl) (by
      intro j
      show B3 (trSl j) = (if j.val = 0 then frame (fld x) else [])
      by_cases h0 : j.val = 0
      · rw [if_pos h0, show trSl j = (125 : Fin 743) from Fin.ext (by simp [trSl, h0]), b3port]
      · rw [if_neg h0, b3 _ (by simp only [trSl]; rw [if_neg h0]; omega),
          b2big _ (by simp only [trSl]; rw [if_neg h0]; omega)])
  rw [zeroH] at d4
  set B4 := install trSl B3 o4 with hB4
  have b4 : ∀ t : Fin 743, (t.val ≠ 125 ∧ (t.val < 249 ∨ 422 ≤ t.val)) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have := congrArg Fin.val e; simp only [trSl] at this; split_ifs at this <;> omega)
  have b4A : B4 278 = (bw x).flatMap frame := (install_slot trSl trSl_inj B3 o4 30).trans (t30.trans (stream_bw x))
  -- 5: the second cell
  have d5 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock cell2Sl cell2Sl_inj (fun _ => 0) B4 (fun _ => rfl)
    (fun _ => by
      show B4 422 = []
      rw [b4 _ (by decide), b3 _ (by decide), b2big _ (by decide)])
  rw [zeroH] at d5
  set B5 := install cell2Sl B4 (fun _ => [false]) with hB5
  have b5 : ∀ t : Fin 743, t.val ≠ 422 → B5 t = B4 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b5c : B5 422 = [false] := install_slot cell2Sl cell2Sl_inj _ _ 0
  -- 6: the gate header on the top's code
  obtain ⟨r6, -, hp6⟩ := CloseoutRowsGateHeader.header_run (top x)
  have d6 := (FrontLoopKit.step_of_ready r6).dock ghSl ghSl_inj (fun _ => 0) B5
    (fun _ => rfl) (by
      intro j; rw [CompetitorWitnessHeader.input_eq]
      by_cases h0 : j.val = 0
      · rw [if_pos h0, show ghSl j = (422 : Fin 743) from Fin.ext (by simp [ghSl, h0]), b5c]; rfl
      · by_cases h1 : j.val = 1
        · rw [if_neg h0, if_pos h1, show ghSl j = (165 : Fin 743) from Fin.ext (by simp [ghSl, h1]),
            b5 _ (by decide), b4 _ (by decide), b3top]
        · have hj := j.isLt
          rw [if_neg h0, if_neg h1, b5 _ (by simp only [ghSl]; rw [if_neg h0, if_neg h1]; omega),
            b4 _ (by simp only [ghSl]; rw [if_neg h0, if_neg h1]; omega),
            b3 _ (by simp only [ghSl]; rw [if_neg h0, if_neg h1]; omega),
            b2big _ (by simp only [ghSl]; rw [if_neg h0, if_neg h1]; omega)])
  rw [zeroH] at d6
  set B6 := install ghSl B5 (CloseoutRowsGateHeader.output (top x)) with hB6
  have b6 : ∀ t : Fin 743, (t.val ≠ 422 ∧ t.val ≠ 165 ∧ (t.val < 423 ∨ 569 ≤ t.val)) → B6 t = B5 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have := congrArg Fin.val e; simp only [ghSl] at this; split_ifs at this <;> omega)
  have b6port : B6 539 = frame (supw x) := (install_slot ghSl ghSl_inj B5 _ 118).trans (hp6 2)
  -- 7: the traversal of the support
  obtain ⟨o7, r7, u30, -, -⟩ := CloseoutWitness.CanonicalTest.fields_run (supw x)
  have d7 := (FrontLoopKit.step_of_ready r7).dock tr2Sl tr2Sl_inj (fun _ => 0) B6
    (fun _ => rfl) (by
      intro j
      show B6 (tr2Sl j) = (if j.val = 0 then frame (supw x) else [])
      by_cases h0 : j.val = 0
      · rw [if_pos h0, show tr2Sl j = (539 : Fin 743) from Fin.ext (by simp [tr2Sl, h0]), b6port]
      · have hj := j.isLt
        rw [if_neg h0, b6 _ (by simp only [tr2Sl]; rw [if_neg h0]; omega),
          b5 _ (by simp only [tr2Sl]; rw [if_neg h0]; omega),
          b4 _ (by simp only [tr2Sl]; rw [if_neg h0]; omega),
          b3 _ (by simp only [tr2Sl]; rw [if_neg h0]; omega),
          b2big _ (by simp only [tr2Sl]; rw [if_neg h0]; omega)])
  rw [zeroH] at d7
  set B7 := install tr2Sl B6 o7 with hB7
  have b7 : ∀ t : Fin 743, (t.val ≠ 539 ∧ (t.val < 569 ∨ 742 ≤ t.val)) → B7 t = B6 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have := congrArg Fin.val e; simp only [tr2Sl] at this; split_ifs at this <;> omega)
  have b7S : B7 598 = (sels x).flatMap frame :=
    (install_slot tr2Sl tr2Sl_inj B6 o7 30).trans (u30.trans (stream_sels x))
  -- 8: the selection
  obtain ⟨o8, s8, -, -, -, a3, a4⟩ := selStage (pairs x) (pairs_sel_ne x) Bw hBw n
  rw [pairs_fst x hsel, pairs_snd x hsel] at s8
  have d8 := s8.dock selSl selSl_inj (fun _ => 0) B7 (fun _ => rfl) (by
    intro j; rw [selIn_val]
    fin_cases j
    · show B7 278 = _
      rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4A]; rfl
    · show B7 4 = _
      rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        show (4 : Fin 743) = cropSl 1 from rfl, b2hit, c1]; rfl
    · show B7 598 = _; rw [b7S]; rfl
    · show B7 2 = _
      rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        b2 _ (by intro k; rw [cropSl_val]; fin_cases k <;> decide), b1 _ (by decide)]; simp [hB0, roundTIn]
    · show B7 3 = _
      rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        b2 _ (by intro k; rw [cropSl_val]; fin_cases k <;> decide), b1 _ (by decide)]; simp [hB0, roundTIn]
    · show B7 742 = _
      rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        b2big _ (by decide)]; rfl)
  rw [zeroH] at d8
  set B8 := install selSl B7 o8 with hB8
  have b8 : ∀ t : Fin 743, (∀ j, (selSl j).val ≠ t.val) → B8 t = B7 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq (d7.seq d8))))))
  have run' : Step workerT _ (fun _ => 0) B0 (fun _ => 0) B8 := run
  refine ⟨B8, FrontKit.ready_of_step
    (run'.enlarge (by unfold roundTCost; exact le_refl _)), ?_, ?_, ?_, ?_⟩
  · rw [b8 _ (by intro k; rw [selSl_val]; fin_cases k <;> decide), b7 _ (by decide), b6 _ (by decide),
      b5 _ (by decide), b4 _ (by decide), b3 _ (by decide), show (0 : Fin 743) = cropSl 0 from rfl, b2hit, c0]
  · rw [b8 _ (by intro k; rw [selSl_val]; fin_cases k <;> decide), b7 _ (by decide), b6 _ (by decide),
      b5 _ (by decide), b4 _ (by decide), b3 _ (by decide), show (1 : Fin 743) = cropSl 2 from rfl, b2hit, c2]
  · exact (install_slot selSl selSl_inj B7 o8 3).trans a3
  · exact (install_slot selSl selSl_inj B7 o8 4).trans a4

/-! ## The loop: every circuit -/

open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-- The round's scratch: every tape but the fields, the counter and the two accumulators. -/
def scrT (j : Fin 739) : Fin 743 := ⟨j.val + 4, by omega⟩

theorem scrT_inj : Function.Injective scrT := fun a b h => Fin.ext (by have := congrArg Fin.val h; simp [scrT] at this; omega)

theorem scrT_iff (t : Fin 743) : (∃ j, scrT j = t) ↔ 4 ≤ t.val := by
  constructor
  · rintro ⟨j, rfl⟩; simp [scrT]
  · intro h; exact ⟨⟨t.val - 4, by omega⟩, Fin.ext (by simp [scrT]; omega)⟩

/-- **Loop A for `THR∘THR` circuits.** -/
noncomputable def foldT := foldLoop (foldBody workerT scrT (idleA (743 + 2)))

/-- The retained bottoms of the first `i` circuits. -/
def bacT (xs : List ℕ) (i : ℕ) : List (List Bool) := ((xs.take i).map bwT).flatten

theorem bacT_succ (xs : List ℕ) (i : ℕ) (hi : i < xs.length) : bacT xs (i + 1) = bacT xs i ++ bwT xs[i] := by
  unfold bacT
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append, List.flatten_append,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem bwT_mem (x : ℕ) (w : List Bool) (hw : w ∈ bwT x) : w ∈ bw x := by
  have h1 := (selOf_sublist (pairs x)).subset hw
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
  exact (List.of_mem_zip hp).1

theorem bacT_ne (xs : List ℕ) (i : ℕ) : ∀ b ∈ bacT xs i, b ≠ [] := by
  intro b hb
  obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp hb
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hl
  exact bw_ne x b (bwT_mem x b hbl)

theorem bacT_prefix (xs : List ℕ) (i : ℕ) : bacT xs i <+: bacT xs xs.length := by
  unfold bacT
  rw [List.take_length]
  conv_rhs => rw [← List.take_append_drop i xs]
  rw [List.map_append, List.flatten_append]
  exact List.prefix_append _ _

theorem flat_sub_le {l1 l2 : List (List Bool)} (h : List.Sublist l1 l2) :
    (l1.flatMap frame).length ≤ (l2.flatMap frame).length := by
  induction h with
  | slnil => simp
  | cons a _ ih => simp only [List.flatMap_cons, List.length_append]; omega
  | cons_cons a _ ih => simp only [List.flatMap_cons, List.length_append]; omega

theorem bacT_sub (xs : List ℕ) (hsel : ∀ x ∈ xs, (sels x).length = (bw x).length) (i : ℕ) :
    List.Sublist (bacT xs i) (bacc xs i) := by
  unfold bacT bacc
  have : ∀ ys : List ℕ, (∀ x ∈ ys, (sels x).length = (bw x).length) →
      List.Sublist (ys.map bwT).flatten (ys.map bw).flatten := by
    intro ys
    induction ys with
    | nil => intro _; simp
    | cons y ys ih =>
      intro h
      simp only [List.map_cons, List.flatten_cons]
      exact (bwT_sublist y (h y (by simp))).append (ih (fun x hx => h x (by simp [hx])))
  exact this _ (fun x hx => hsel x (List.mem_of_mem_take hx))

/-- The round's entry at circuit `i`. -/
def Qt (xs : List ℕ) (total i : ℕ) : Fin 743 → List Bool :=
  roundTIn ((xs.map nf).flatten ++ [false]) (ZeroPadding.pad total (List.replicate i true))
    ((bacT xs i).flatMap frame) (false :: List.replicate (bacT xs i).length true)

/-- One round's uniform fuel: `c` circuits of width `≤ W`, `TB` cells of bottoms, `TN` bottoms (all, unfiltered). -/
def foldCwT (W c TB TN : ℕ) : ℕ :=
  1 + 1 + ((2 * (c * (18 * W + 16) + 29 * W + 25) + 2) + 1 + (50001 * (W + 1) ^ 2 + 1 +
    (16 * (1000000000000000000 * (W + 1) ^ 24) + 1 + (1 + 1 + (27000 * (W + 1) ^ 2 + 1 +
      (16 * (1000000000000000000 * (W + 1) ^ 24) + 1 +
        (2 * (6 * TB + 3 * TN + (8 * TB + (6 * W + 33) * TN + 1) + 10) + 2)))))))

theorem selCost_le (W : ℕ) : ∀ ps : List (List Bool × List Bool), (∀ p ∈ ps, p.2.length ≤ W) →
    selCost ps ≤ 8 * ((ps.map Prod.fst).flatMap frame).length + (6 * W + 33) * ps.length + 1
  | [], _ => by simp [selCost]
  | p :: ps, h => by
    have ih := selCost_le W ps (fun q hq => h q (by simp [hq]))
    have hp := h p (by simp)
    have hc : selCost (p :: ps) = (16 * p.1.length + 6 * p.2.length + 33) + selCost ps := by
      simp [selCost, List.map_cons, List.sum_cons]; omega
    rw [hc]
    simp only [List.map_cons, List.flatMap_cons, List.length_append, List.length_cons, frame_len]
    have : 6 * p.2.length ≤ 6 * W := by omega
    nlinarith

theorem roundTCost_le (xs : List ℕ) (W : ℕ) (hW : ∀ x ∈ xs, natBitLength x ≤ W)
    (hsel : ∀ x ∈ xs, (sels x).length = (bw x).length) (i : ℕ) (hi : i < xs.length) :
    roundTCost i W xs[i] (bacT xs i) (bacT xs i).length ≤
      foldCwT W xs.length ((bacc xs xs.length).flatMap frame).length (bacc xs xs.length).length := by
  have hmem : xs[i] ∈ xs := List.getElem_mem hi
  -- the unfiltered bottoms up to circuit `i` inclusive
  have hpre2 := bacc_prefix xs (i + 1)
  rw [bacc_succ xs i hi] at hpre2
  have hl1 : (bacc xs i ++ bw xs[i]).length ≤ (bacc xs xs.length).length := hpre2.length_le
  have hl2 : ((bacc xs i ++ bw xs[i]).flatMap frame).length ≤ ((bacc xs xs.length).flatMap frame).length :=
    prefix_flat_le hpre2
  rw [List.flatMap_append, List.length_append] at hl2
  rw [List.length_append] at hl1
  -- the retained ones so far
  have hT1 := flat_sub_le (bacT_sub xs hsel i)
  have hT2 := (bacT_sub xs hsel i).length_le
  generalize hxd : xs[i] = x at *
  have hx : natBitLength x ≤ W := hW _ hmem
  have hs := hsel _ hmem
  generalize ((bacc xs xs.length).flatMap frame).length = TB at *
  generalize (bacc xs xs.length).length = TN at *
  -- the selection
  have hsc := selCost_le W (pairs x) (by
    intro p hp
    obtain ⟨a, -, ha⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← ha, binary_length, supw_length]; exact hx)
  rw [pairs_fst _ hs] at hsc
  have hpl : (pairs x).length = (bw x).length := by
    unfold pairs; rw [List.length_zip]; omega
  rw [hpl] at hsc
  have hsc2 : (6 * W + 33) * (bw x).length ≤ (6 * W + 33) * TN := Nat.mul_le_mul_left _ (by omega)
  have hh : 50001 * ((pay x).length + 1) ^ 2 ≤ 50001 * (W + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [pay_length]; omega) _)
  have hg : 27000 * ((top x).length + 1) ^ 2 ≤ 27000 * (W + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [top_length]; omega) _)
  have ht : 16 * (1000000000000000000 * ((fld x).length + 1) ^ 24) ≤ 16 * (1000000000000000000 * (W + 1) ^ 24) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [fld_length]; omega) _))
  have ht2 : 16 * (1000000000000000000 * ((supw x).length + 1) ^ 24) ≤
      16 * (1000000000000000000 * (W + 1) ^ 24) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [supw_length]; omega) _))
  have hc : i * (18 * W + 16) ≤ xs.length * (18 * W + 16) := Nat.mul_le_mul_right _ hi.le
  unfold roundTCost foldCwT cropACost selWCost CloseoutRowsCircuitHeader.budget CloseoutRowsGateHeader.budget
    CloseoutWitness.CanonicalTest.budget CloseoutWitness.Reencode.polynomialBudget
  generalize (W + 1) ^ 24 = P at *
  generalize (W + 1) ^ 2 = Q at *
  generalize (bw x).length = nb at *
  generalize ((bw x).flatMap frame).length = fb at *
  generalize selCost (pairs x) = sc at *
  generalize ((bacT xs i).flatMap frame).length = tb at *
  generalize (bacT xs i).length = tn at *
  generalize xs.length * (18 * W + 16) = cw at *
  generalize i * (18 * W + 16) = iw at *
  generalize (6 * W + 33) * nb = z1 at *
  generalize (6 * W + 33) * TN = z2 at *
  omega

/-- **The `THR∘THR` loop is ready**: from the padded round tapes at circuit `0` and the unary count `|xs|`, the loop
ends at the padded round tapes at circuit `|xs|`: the retained bottoms of every circuit, in order, and their count. -/
theorem foldT_run (xs : List ℕ) (W : ℕ) (hW : ∀ x ∈ xs, natBitLength x ≤ W)
    (hsel : ∀ x ∈ xs, (sels x).length = (bw x).length) (total capT : ℕ) (hcap : total + 1 ≤ capT)
    (hc : xs.length ≤ total) (hS : ((xs.map nf).flatten ++ [false]).length ≤ total)
    (hB : ((bacc xs xs.length).flatMap frame).length ≤ total) (hN : (bacc xs xs.length).length + 1 ≤ total)
    (hcw : foldCwT W xs.length ((bacc xs xs.length).flatMap frame).length (bacc xs xs.length).length + 1 ≤ total) :
    ClockJoin.ReadyRun foldT
      (1 + 1 + (xs.length * (foldCwT W xs.length ((bacc xs xs.length).flatMap frame).length (bacc xs xs.length).length +
        1 + (2 * total + 4 + 1 + 0) + 2) + xs.length + 3 + 1 + 1))
      (Fin.addCases (roundTapes (padScratch scrT total (Qt xs total 0)) total capT)
        (fun _ => CompareMachine.word xs.length))
      (Fin.addCases (roundTapes (padScratch scrT total (Qt xs total xs.length)) total capT)
        (fun _ => CompareMachine.word xs.length)) := by
  set cw := foldCwT W xs.length ((bacc xs xs.length).flatMap frame).length (bacc xs xs.length).length with hcw'
  have hround : ∀ i, ∃ out : Fin 743 → List Bool, i < xs.length →
      ClockJoin.ReadyRun workerT cw (Qt xs total i) out ∧
      out 0 = (xs.map nf).flatten ++ [false] ∧ out 1 = ZeroPadding.pad total (List.replicate (i + 1) true) ∧
      out 2 = (bacT xs (i + 1)).flatMap frame ∧ out 3 = false :: List.replicate (bacT xs (i + 1)).length true := by
    intro i
    by_cases hi : i < xs.length
    · obtain ⟨out, h1, h2, h3, h4, h5⟩ := roundT_run xs W hW i hi (hsel _ (List.getElem_mem hi))
        (List.replicate (total - i - 1) false) (bacT xs i) (bacT_ne xs i) (bacT xs i).length
      refine ⟨out, fun _ => ⟨?_, h2, by rw [h3, pad_succ total i], ?_, ?_⟩⟩
      · unfold Qt; rw [pad_split total i (by omega)]
        exact ClockJoin.enlarge _ _ _ _ _ h1 (roundTCost_le xs W hW hsel i hi)
      · rw [h4, bacT_succ xs i hi]
      · rw [h5, bacT_succ xs i hi, List.length_append]
    · exact ⟨fun _ => [], fun h => absurd h hi⟩
  choose Q' hQ' using hround
  have hlenQ : ∀ i, i ≤ xs.length → ∀ t, (Qt xs total i t).length ≤ total := by
    intro i hi t
    have hpre := bacT_prefix xs i
    have hl1 := hpre.length_le
    have hl2 : ((bacT xs i).flatMap frame).length ≤ ((bacT xs xs.length).flatMap frame).length := prefix_flat_le hpre
    have hs1 := flat_sub_le (bacT_sub xs hsel xs.length)
    have hs2 := (bacT_sub xs hsel xs.length).length_le
    unfold Qt roundTIn
    split_ifs
    · exact hS
    · simp [ZeroPadding.pad]; omega
    · omega
    · simp; omega
    · simp
  have hwork : ∀ i, i < xs.length → ClockJoin.ReadyRun workerT cw (Qt xs total i) (Q' i) := fun i hi => (hQ' i hi).1
  exact uniformFold_ready workerT scrT scrT_inj (idleA (743 + 2)) total capT cw 0 xs.length hcap (Qt xs total) Q'
    hwork
    (fun i hi j => by
      have hl := ready_lengths (hwork i hi) total (hlenQ i hi.le) (scrT j)
      have : max total (cw + 1) = total := max_eq_left (by omega)
      omega)
    (fun i hi => by
      have e : blankScratch scrT (Q' i) = Qt xs total (i + 1) := by
        funext t
        unfold blankScratch
        by_cases ht : ∃ j, scrT j = t
        · rw [if_pos ht]
          have h4 := (scrT_iff t).mp ht
          unfold Qt roundTIn; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · rw [if_neg ht]
          have h4 : t.val < 4 := by by_contra hc'; exact ht ((scrT_iff t).mpr (by omega))
          obtain ⟨-, o0, o1, o2, o3⟩ := hQ' i hi
          unfold Qt roundTIn
          by_cases h0 : t.val = 0
          · rw [if_pos h0, show t = 0 from Fin.ext h0, o0]
          · by_cases h1 : t.val = 1
            · rw [if_neg h0, if_pos h1, show t = 1 from Fin.ext h1, o1]
            · by_cases h2 : t.val = 2
              · rw [if_neg h0, if_neg h1, if_pos h2, show t = 2 from Fin.ext h2, o2]
              · rw [if_neg h0, if_neg h1, if_neg h2, if_pos (by omega), show t = 3 from Fin.ext (by omega), o3]
      rw [e]; exact idleA_ready _ _)

end NearCubicWires.WireExponent3_5.UnionMachine.CWRoundT
