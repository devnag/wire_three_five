import Proof.Wire_3_5.Recovery.CertSched
import Proof.Wire_3_5.UnionMachine.CWWords
import Proof.Wire_3_5.UnionMachine.FrontLoopKit

/-! # C6 front, U5, the code writers: loop A's round — one circuit's bottoms

The carrier of a call is "the union of a named variable's atoms' bottom gates" (P3:3401-3410; `Stars.Carrier`), so the
carrier writer first collects the bottoms of every circuit it reads. A circuit's code is the tagged list
`[family tag, bottom count, bottoms, top]` whose third field is the balanced list of its bottoms' codes (`CarrierFormat.sym_fields` / `thr_fields`). One ROUND of loop A handles circuit `i` on a fixed bank of `423` tapes:
* `0` the fields `frame u`, `1` the round counter `1^i 0 r`, `2` the bottom accumulator (framed words), `3` the count
  accumulator `false :: 1^n`; `4` the word layer's cell;
* the crop (`CWWords.cropAW`): circuit `i`'s payload `frame (pay x)` on `5`, the header's constant `frame []` on `7`;
* base's circuit header (`CloseoutRowsCircuitHeader`, 242 tapes): the field words `frame (codeWord (pay x) k)`;
* base's balanced-list traversal (`CloseoutWitness.CanonicalTest`, 174 tapes) on field 2: its atom stream and count;
* the append (`CWWords.appendAW`): the atoms join the bottom accumulator, their count the count accumulator.

Paper quantity of the main type (**`roundA_run`**): the bottoms `bw x` of circuit `i` (the atoms of field 2 of its
code, at the code's width), appended with their count. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWRoundA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready FrontKit.ready_of_step)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## One circuit's bottoms -/

/-- The bottoms' field word of the circuit with code `x`: field 2 of its payload. -/
def fld (x : ℕ) : List Bool := CloseoutRowsCircuitHeader.codeWord (pay x) 2

/-- **The bottoms' words** of the circuit with code `x`: the atoms of its field 2, at the code's width. -/
def bw (x : ℕ) : List (List Bool) :=
  (PCPPNativeCanonicalTree.tree (RadixSemantics.value (fld x))).atoms.map (binary (fld x).length)

theorem fld_length (x : ℕ) : (fld x).length = natBitLength x := by
  unfold fld CloseoutRowsCircuitHeader.codeWord
  rw [(RecoveryFixedUnpair.word_lengths _).1, CompetitorWitnessTriple.word_length, pay_length]

theorem bw_ne (x : ℕ) : ∀ w ∈ bw x, w ≠ [] := by
  intro w hw
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hw
  intro h
  have h1 := congrArg List.length h
  rw [binary_length, fld_length, List.length_nil] at h1
  have := natBitLength_pos x
  omega

theorem stream_bw (x : ℕ) :
    PCPPNativeCanonicalWalk.atomStream (fld x).length (PCPPNativeCanonicalTree.tree (RadixSemantics.value (fld x))).atoms =
      (bw x).flatMap frame := by
  unfold PCPPNativeCanonicalWalk.atomStream bw
  rw [List.flatMap_map]

/-! ## The layout -/

def cellSl : Fin 1 → Fin 423 := fun _ => 4
def cropSl : Fin 7 → Fin 423 := ![0, 4, 1, 5, 6, 7, 8]
def hdSl (j : Fin 242) : Fin 423 := ⟨if j.val = 0 then 7 else if j.val = 1 then 5 else j.val + 7, by split_ifs <;> omega⟩
def trSl (j : Fin 174) : Fin 423 := ⟨if j.val = 0 then 125 else j.val + 248, by split_ifs <;> omega⟩
def apSl : Fin 6 → Fin 423 := ![278, 4, 289, 2, 3, 422]

theorem cellSl_inj : Function.Injective cellSl := fun a b _ => Subsingleton.elim a b
theorem cropSl_inj : Function.Injective cropSl := by decide
theorem hdSl_inj : Function.Injective hdSl := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [hdSl] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem trSl_inj : Function.Injective trSl := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [trSl] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem apSl_inj : Function.Injective apSl := by decide

theorem cropSl_val (j : Fin 7) : (cropSl j).val = [0, 4, 1, 5, 6, 7, 8].getD j.val 0 := by fin_cases j <;> rfl
theorem apSl_val (j : Fin 6) : (apSl j).val = [278, 4, 289, 2, 3, 422].getD j.val 0 := by fin_cases j <;> rfl

noncomputable def cellR := RecoveryFocus.machine cellSl NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def cropR := RecoveryFocus.machine cropSl (Rewind.machine cropAW.toProg.compile)
noncomputable def hdR := RecoveryFocus.machine hdSl CloseoutRowsCircuitHeader.machine
noncomputable def trR := RecoveryFocus.machine trSl CloseoutWitness.CanonicalTest.machine
noncomputable def apR := RecoveryFocus.machine apSl (Rewind.machine appendAW.toProg.compile)

/-- **Loop A's round worker.** -/
noncomputable def workerA :=
  Composition.machine cellR (Composition.machine cropR (Composition.machine hdR (Composition.machine trR apR)))

/-- The round's entry: the fields, the counter, the two accumulators; every other tape blank. -/
def roundAIn (S K B N : List Bool) : Fin 423 → List Bool :=
  fun t => if t.val = 0 then S else if t.val = 1 then K else if t.val = 2 then B else if t.val = 3 then N else []

theorem hdIn_val (bits : List Bool) (j : Fin 242) :
    CloseoutRowsCircuitHeader.input bits j = if j.val = 0 then [false] else if j.val = 1 then frame bits else [] := by
  refine Fin.addCases (m := 122) (n := 120) (fun a => ?_) (fun b => ?_) j
  · simp only [CloseoutRowsCircuitHeader.input, Fin.addCases_left, CompetitorWitnessTriple.input, Fin.val_castAdd]
    rfl
  · simp only [CloseoutRowsCircuitHeader.input, Fin.addCases_right, Fin.val_natAdd]
    rw [if_neg (by omega), if_neg (by omega)]

theorem zeroH (t : ℕ) (sl : Fin t → Fin 423) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- The round's fuel. -/
noncomputable def roundACost (i W : ℕ) (x : ℕ) (Bw : List (List Bool)) (n : ℕ) : ℕ :=
  1 + 1 + ((2 * cropACost i W + 2) + 1 + (CloseoutRowsCircuitHeader.budget (pay x) + 1 +
    (CloseoutWitness.CanonicalTest.budget (fld x) + 1 + (2 * appendACost (bw x) Bw (bw x).length n + 2))))

/-- **One round of loop A**: circuit `i`'s bottoms join the accumulator, their count the count; the counter advances. -/
theorem roundA_run (xs : List ℕ) (W : ℕ) (hW : ∀ x ∈ xs, natBitLength x ≤ W) (i : ℕ) (hi : i < xs.length)
    (rest : List Bool) (Bw : List (List Bool)) (hBw : ∀ b ∈ Bw, b ≠ []) (n : ℕ) :
    ∃ out, ClockJoin.ReadyRun workerA (roundACost i W xs[i] Bw n)
        (roundAIn ((xs.map nf).flatten ++ [false]) (List.replicate i true ++ (false :: rest)) (Bw.flatMap frame)
          (false :: List.replicate n true)) out ∧
      out 0 = (xs.map nf).flatten ++ [false] ∧ out 1 = List.replicate (i + 1) true ++ rest ∧
      out 2 = (Bw ++ bw xs[i]).flatMap frame ∧ out 3 = false :: List.replicate (n + (bw xs[i]).length) true := by
  set x := xs[i] with hx
  set S := (xs.map nf).flatten ++ [false] with hS
  set B0 := roundAIn S (List.replicate i true ++ (false :: rest)) (Bw.flatMap frame) (false :: List.replicate n true)
    with hB0
  have b0 : ∀ t : Fin 423, 4 ≤ t.val → B0 t = [] := by
    intro t ht; simp only [hB0, roundAIn]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 1: the cell
  have d1 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock cellSl cellSl_inj (fun _ => 0) B0 (fun _ => rfl)
    (fun _ => b0 4 (by decide))
  rw [zeroH] at d1
  set B1 := install cellSl B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 423, t.val ≠ 4 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b14 : B1 4 = [false] := install_slot cellSl cellSl_inj _ _ 0
  -- 2: the crop
  obtain ⟨o2, s2, c0, c1, c2, c3, ⟨r2, c4⟩, c5⟩ := cropAStage xs W hW [false] i hi rest
  have d2 := s2.dock cropSl cropSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [cropAIn_val]
    fin_cases j
    · show B1 0 = _; rw [b1 _ (by decide)]; simp [hB0, roundAIn, hS]
    · show B1 4 = _; rw [b14]; rfl
    · show B1 1 = _; rw [b1 _ (by decide)]; simp [hB0, roundAIn]
    · show B1 5 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 6 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 7 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B1 8 = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl)
  rw [zeroH] at d2
  set B2 := install cropSl B1 o2 with hB2
  have b2 : ∀ t : Fin 423, (∀ j, (cropSl j).val ≠ t.val) → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have b2hit : ∀ j, B2 (cropSl j) = o2 j := fun j => install_slot _ cropSl_inj _ _ _
  have b2big : ∀ t : Fin 423, 9 ≤ t.val → B2 t = [] := by
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
  have b3 : ∀ t : Fin 423, (t.val < 5 ∨ t.val = 6 ∨ t.val = 8 ∨ 249 ≤ t.val) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have := congrArg Fin.val e; simp only [hdSl] at this; split_ifs at this <;> omega)
  have b3port : B3 125 = frame (fld x) := (install_slot hdSl hdSl_inj B2 o3 118).trans (hp3 2)
  -- 4: the traversal of field 2
  obtain ⟨o4, r4, t30, t41, -⟩ := CloseoutWitness.CanonicalTest.fields_run (fld x)
  have d4 := (FrontLoopKit.step_of_ready r4).dock trSl trSl_inj (fun _ => 0) B3
    (fun _ => rfl) (by
      intro j
      show B3 (trSl j) = (if j.val = 0 then frame (fld x) else [])
      by_cases h0 : j.val = 0
      · rw [if_pos h0, show trSl j = (125 : Fin 423) from Fin.ext (by simp [trSl, h0]), b3port]
      · rw [if_neg h0, b3 _ (by simp only [trSl]; rw [if_neg h0]; omega),
          b2big _ (by simp only [trSl]; rw [if_neg h0]; omega)])
  rw [zeroH] at d4
  set B4 := install trSl B3 o4 with hB4
  have b4 : ∀ t : Fin 423, (t.val < 249 ∧ t.val ≠ 125 ∨ t.val = 422) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have := congrArg Fin.val e; simp only [trSl] at this; split_ifs at this <;> omega)
  have b4A : B4 278 = (bw x).flatMap frame := (install_slot trSl trSl_inj B3 o4 30).trans (t30.trans (stream_bw x))
  have b4C : B4 289 = false :: List.replicate (bw x).length true := by
    refine (install_slot trSl trSl_inj B3 o4 41).trans (t41.trans ?_)
    simp [bw, RepairSource.VerifierDecoding.CompareMachine.word]
  -- 5: the append
  obtain ⟨o5, s5, a0, a1, a2, a3, a4⟩ := appendAStage (bw x) Bw (bw_ne x) hBw (bw x).length n
  have d5 := s5.dock apSl apSl_inj (fun _ => 0) B4 (fun _ => rfl) (by
    intro j; rw [appendAIn_val]
    fin_cases j
    · show B4 278 = _; rw [b4A]; rfl
    · show B4 4 = _; rw [b4 _ (by decide), b3 _ (by decide), show (4 : Fin 423) = cropSl 1 from rfl, b2hit, c1]; rfl
    · show B4 289 = _; rw [b4C]; rfl
    · show B4 2 = _; rw [b4 _ (by decide), b3 _ (by decide), b2 _ (by intro k; rw [cropSl_val]; fin_cases k <;> decide),
        b1 _ (by decide)]; simp [hB0, roundAIn]
    · show B4 3 = _; rw [b4 _ (by decide), b3 _ (by decide), b2 _ (by intro k; rw [cropSl_val]; fin_cases k <;> decide),
        b1 _ (by decide)]; simp [hB0, roundAIn]
    · show B4 422 = _; rw [b4 _ (by decide), b3 _ (by decide), b2big _ (by decide)]; rfl)
  rw [zeroH] at d5
  set B5 := install apSl B4 o5 with hB5
  have b5 : ∀ t : Fin 423, (∀ j, (apSl j).val ≠ t.val) → B5 t = B4 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have run := d1.seq (d2.seq (d3.seq (d4.seq d5)))
  have run' : Step workerA _ (fun _ => 0) B0 (fun _ => 0) B5 := run
  refine ⟨B5, FrontKit.ready_of_step
    (run'.enlarge (by unfold roundACost; exact le_refl _)), ?_, ?_, ?_, ?_⟩
  · rw [b5 _ (by intro k; rw [apSl_val]; fin_cases k <;> decide), b4 _ (by decide), b3 _ (by decide),
      show (0 : Fin 423) = cropSl 0 from rfl, b2hit, c0]
  · rw [b5 _ (by intro k; rw [apSl_val]; fin_cases k <;> decide), b4 _ (by decide), b3 _ (by decide),
      show (1 : Fin 423) = cropSl 2 from rfl, b2hit, c2]
  · exact (install_slot apSl apSl_inj B4 o5 3).trans a3
  · exact (install_slot apSl apSl_inj B4 o5 4).trans a4

/-! ## Loop A: every circuit -/

open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-- A machine that halts at once. -/
def idleA (t : ℕ) : Machine t 1 := ⟨0, 0, fun _ => true, fun _ _ => none⟩

theorem idleA_ready (t : ℕ) (X : Fin t → List Bool) : ClockJoin.ReadyRun (idleA t) 0 X X :=
  ⟨_, runFrom_zero_of_halted (idleA t) _ rfl, rfl, fun _ => rfl, le_refl _⟩

/-- The round's scratch: every tape but the fields, the counter and the two accumulators. -/
def scrA (j : Fin 419) : Fin 423 := ⟨j.val + 4, by omega⟩

theorem scrA_inj : Function.Injective scrA := fun a b h => Fin.ext (by have := congrArg Fin.val h; simp [scrA] at this; omega)

theorem scrA_iff (t : Fin 423) : (∃ j, scrA j = t) ↔ 4 ≤ t.val := by
  constructor
  · rintro ⟨j, rfl⟩; simp [scrA]
  · intro h; exact ⟨⟨t.val - 4, by omega⟩, Fin.ext (by simp [scrA]; omega)⟩

/-- **Loop A.** -/
noncomputable def foldA := foldLoop (foldBody workerA scrA (idleA (423 + 2)))

/-- The bottoms of the first `i` circuits. -/
def bacc (xs : List ℕ) (i : ℕ) : List (List Bool) := ((xs.take i).map bw).flatten

theorem bacc_succ (xs : List ℕ) (i : ℕ) (hi : i < xs.length) : bacc xs (i + 1) = bacc xs i ++ bw xs[i] := by
  unfold bacc
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append, List.flatten_append,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem prefix_flat_le {a b : List (List Bool)} (h : a <+: b) : (a.flatMap frame).length ≤ (b.flatMap frame).length := by
  obtain ⟨t, rfl⟩ := h
  rw [List.flatMap_append, List.length_append]; omega

theorem pad_split (total i : ℕ) (hi : i < total) :
    ZeroPadding.pad total (List.replicate i true) =
      List.replicate i true ++ (false :: List.replicate (total - i - 1) false) := by
  unfold ZeroPadding.pad
  rw [List.length_replicate, ← List.replicate_succ]
  congr 2
  omega

theorem pad_succ (total i : ℕ) :
    List.replicate (i + 1) true ++ List.replicate (total - i - 1) false =
      ZeroPadding.pad total (List.replicate (i + 1) true) := by
  unfold ZeroPadding.pad; rw [List.length_replicate]; congr 2

theorem bacc_ne (xs : List ℕ) (i : ℕ) : ∀ b ∈ bacc xs i, b ≠ [] := by
  intro b hb
  obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp hb
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hl
  exact bw_ne x b hbl

theorem bacc_prefix (xs : List ℕ) (i : ℕ) : bacc xs i <+: bacc xs xs.length := by
  unfold bacc
  rw [List.take_length]
  conv_rhs => rw [← List.take_append_drop i xs]
  rw [List.map_append, List.flatten_append]
  exact List.prefix_append _ _

/-- The round's entry at circuit `i`. -/
def Qa (xs : List ℕ) (total i : ℕ) : Fin 423 → List Bool :=
  roundAIn ((xs.map nf).flatten ++ [false]) (ZeroPadding.pad total (List.replicate i true))
    ((bacc xs i).flatMap frame) (false :: List.replicate (bacc xs i).length true)

/-- One round's uniform fuel: `c` circuits of width `≤ W`, `TB` cells of bottoms, `TN` bottoms. -/
def foldCwA (W c TB TN : ℕ) : ℕ :=
  1 + 1 + ((2 * (c * (18 * W + 16) + 29 * W + 25) + 2) + 1 + (50001 * (W + 1) ^ 2 + 1 +
    (16 * (1000000000000000000 * (W + 1) ^ 24) + 1 + (2 * (15 * TB + 10 * TN + 14) + 2))))

theorem roundACost_le (xs : List ℕ) (W : ℕ) (hW : ∀ x ∈ xs, natBitLength x ≤ W) (i : ℕ) (hi : i < xs.length) :
    roundACost i W xs[i] (bacc xs i) (bacc xs i).length ≤
      foldCwA W xs.length ((bacc xs xs.length).flatMap frame).length (bacc xs xs.length).length := by
  have hx : natBitLength xs[i] ≤ W := hW _ (List.getElem_mem hi)
  have hpre1 := bacc_prefix xs i
  have hpre2 := bacc_prefix xs (i + 1)
  rw [bacc_succ xs i hi] at hpre2
  have hl1 : (bacc xs i ++ bw xs[i]).length ≤ (bacc xs xs.length).length := hpre2.length_le
  have hl2 : ((bacc xs i ++ bw xs[i]).flatMap frame).length ≤ ((bacc xs xs.length).flatMap frame).length :=
    prefix_flat_le hpre2
  rw [List.flatMap_append, List.length_append] at hl2
  rw [List.length_append] at hl1
  have hh : 50001 * ((pay xs[i]).length + 1) ^ 2 ≤ 50001 * (W + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [pay_length]; omega) _)
  have ht : 16 * (1000000000000000000 * ((fld xs[i]).length + 1) ^ 24) ≤ 16 * (1000000000000000000 * (W + 1) ^ 24) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [fld_length]; omega) _))
  have hc : i * (18 * W + 16) ≤ xs.length * (18 * W + 16) := Nat.mul_le_mul_right _ hi.le
  unfold roundACost foldCwA cropACost appendACost CloseoutRowsCircuitHeader.budget
    CloseoutWitness.CanonicalTest.budget CloseoutWitness.Reencode.polynomialBudget
  omega

/-- **Loop A is ready**: from the padded round tapes at circuit `0` and the unary count `|xs|`, the loop ends at the
padded round tapes at circuit `|xs|`: the bottoms of every circuit, in order, and their count. -/
theorem foldA_run (xs : List ℕ) (W : ℕ) (hW : ∀ x ∈ xs, natBitLength x ≤ W) (total capT : ℕ) (hcap : total + 1 ≤ capT)
    (hc : xs.length ≤ total) (hS : ((xs.map nf).flatten ++ [false]).length ≤ total)
    (hB : ((bacc xs xs.length).flatMap frame).length ≤ total) (hN : (bacc xs xs.length).length + 1 ≤ total)
    (hcw : foldCwA W xs.length ((bacc xs xs.length).flatMap frame).length (bacc xs xs.length).length + 1 ≤ total) :
    ClockJoin.ReadyRun foldA
      (1 + 1 + (xs.length * (foldCwA W xs.length ((bacc xs xs.length).flatMap frame).length (bacc xs xs.length).length +
        1 + (2 * total + 4 + 1 + 0) + 2) + xs.length + 3 + 1 + 1))
      (Fin.addCases (roundTapes (padScratch scrA total (Qa xs total 0)) total capT)
        (fun _ => CompareMachine.word xs.length))
      (Fin.addCases (roundTapes (padScratch scrA total (Qa xs total xs.length)) total capT)
        (fun _ => CompareMachine.word xs.length)) := by
  set cw := foldCwA W xs.length ((bacc xs xs.length).flatMap frame).length (bacc xs xs.length).length with hcw'
  have hround : ∀ i, ∃ out : Fin 423 → List Bool, i < xs.length →
      ClockJoin.ReadyRun workerA cw (Qa xs total i) out ∧
      out 0 = (xs.map nf).flatten ++ [false] ∧ out 1 = ZeroPadding.pad total (List.replicate (i + 1) true) ∧
      out 2 = (bacc xs (i + 1)).flatMap frame ∧ out 3 = false :: List.replicate (bacc xs (i + 1)).length true := by
    intro i
    by_cases hi : i < xs.length
    · obtain ⟨out, h1, h2, h3, h4, h5⟩ := roundA_run xs W hW i hi (List.replicate (total - i - 1) false) (bacc xs i)
        (bacc_ne xs i) (bacc xs i).length
      refine ⟨out, fun _ => ⟨?_, h2, by rw [h3, pad_succ total i], ?_, ?_⟩⟩
      · unfold Qa; rw [pad_split total i (by omega)]
        exact ClockJoin.enlarge _ _ _ _ _ h1 (roundACost_le xs W hW i hi)
      · rw [h4, bacc_succ xs i hi]
      · rw [h5, bacc_succ xs i hi, List.length_append]
    · exact ⟨fun _ => [], fun h => absurd h hi⟩
  choose Q' hQ' using hround
  have hlenQ : ∀ i, i ≤ xs.length → ∀ t, (Qa xs total i t).length ≤ total := by
    intro i hi t
    have hpre := bacc_prefix xs i
    have hl1 := hpre.length_le
    have hl2 : ((bacc xs i).flatMap frame).length ≤ ((bacc xs xs.length).flatMap frame).length := prefix_flat_le hpre
    unfold Qa roundAIn
    split_ifs
    · exact hS
    · simp [ZeroPadding.pad]; omega
    · omega
    · simp; omega
    · simp
  have hwork : ∀ i, i < xs.length → ClockJoin.ReadyRun workerA cw (Qa xs total i) (Q' i) := fun i hi => (hQ' i hi).1
  exact uniformFold_ready workerA scrA scrA_inj (idleA (423 + 2)) total capT cw 0 xs.length hcap (Qa xs total) Q'
    hwork
    (fun i hi j => by
      have hl := ready_lengths (hwork i hi) total (hlenQ i hi.le) (scrA j)
      have : max total (cw + 1) = total := max_eq_left (by omega)
      omega)
    (fun i hi => by
      have e : blankScratch scrA (Q' i) = Qa xs total (i + 1) := by
        funext t
        unfold blankScratch
        by_cases ht : ∃ j, scrA j = t
        · rw [if_pos ht]
          have h4 := (scrA_iff t).mp ht
          unfold Qa roundAIn; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · rw [if_neg ht]
          have h4 : t.val < 4 := by by_contra hc'; exact ht ((scrA_iff t).mpr (by omega))
          obtain ⟨-, o0, o1, o2, o3⟩ := hQ' i hi
          unfold Qa roundAIn
          by_cases h0 : t.val = 0
          · rw [if_pos h0, show t = 0 from Fin.ext h0, o0]
          · by_cases h1 : t.val = 1
            · rw [if_neg h0, if_pos h1, show t = 1 from Fin.ext h1, o1]
            · by_cases h2 : t.val = 2
              · rw [if_neg h0, if_neg h1, if_pos h2, show t = 2 from Fin.ext h2, o2]
              · rw [if_neg h0, if_neg h1, if_neg h2, if_pos (by omega), show t = 3 from Fin.ext (by omega), o3]
      rw [e]; exact idleA_ready _ _)

end NearCubicWires.WireExponent3_5.UnionMachine.CWRoundA
