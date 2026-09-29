import Proof.Wire_3_5.UnionMachine.CWEnvRound
import Proof.Wire_3_5.UnionMachine.CWCore

/-! # C6 front, U5, the code writers: a named carrier's envelope bit from its code

"at most `(n+1)^deg` atom occurrences, each with at most `(n+1)^deg` description bits" (P3:3083-3094,
`Stars.Carrier.WithinEnvelope`). The union front writes each variable's carrier code (the carrier writer's output
`frame (natWord X.code)`); this machine (`envCodeM`, 1192 tapes) decides the envelope on that code:
* the cell; the code's payload `frame (pay x)` (`CWWords.copyNatW`);
* base's balanced traversal: the atoms' framed words and their count `false :: 1^|X|`;
* the count check against the ruler `1^L` (`CWEnvChk.cntChkW`): the flag `[decide (|X| ≤ L)]`;
* the erase of the loop's scratch against the capacity ruler `1^T`, then the envelope loop (`CWEnvRound.foldE`): every
  atom's description bits against `1^L`;
* the flag framed on the output (`CWEnvChk.outW`).

Tapes: `0` the code `frame (natWord x)`, `1` the ruler `1^L`, `2` the output, `3` the cell, `4` the crop's ruler, `5` the
payload, `6` the crop's log, `7..179` the traversal (atoms on `36`, count on `47`), `180` the flag, `181` the count
check's log, `182` the loop's counter, `183..1188` its scratch, `1189` the capacity ruler `1^T`, `1190` its capacity
tape, `1191` the output's log.

Paper quantity of the main type (**`envCode_step`**): the envelope bit of the carrier with code `x`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWEnvCode
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords NearCubicWires.WireExponent3_5.UnionMachine.CWEnvChk
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvRound
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready FrontKit.ready_of_step)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.WireExponent3_5.Transfer

/-! ## The code's atoms -/

/-- **The atoms' words** of the code `x`: the traversal's atoms at the payload's width. -/
def atomsOf (x : ℕ) : List (List Bool) :=
  (PCPPNativeCanonicalTree.tree x).atoms.map (binary (natBitLength x))

theorem stream_atoms (x : ℕ) :
    PCPPNativeCanonicalWalk.atomStream (pay x).length (PCPPNativeCanonicalTree.tree (value (pay x))).atoms =
      (atomsOf x).flatMap frame := by
  unfold PCPPNativeCanonicalWalk.atomStream atomsOf
  rw [value_pay, pay_length, List.flatMap_map]

theorem atoms_len (x : ℕ) : (atomsOf x).length = (PCPPNativeCanonicalTree.tree x).atoms.length := by
  unfold atomsOf; rw [List.length_map]

theorem atoms_width (x : ℕ) : ∀ y ∈ atomsOf x, y.length = natBitLength x := by
  intro y hy
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hy
  exact binary_length _ _

/-! ## The crop of the code's payload -/

/-- The payload of the code's field, framed (streams `0` the code, `1` the ruler, `2` the payload). -/
def natCropW : WM 2 0 := copyNatW 0 1 2

def σNC (S : List Bool) : WState 2 0 := ⟨fun _ => 0, ![S, [], []], fun r => r.elim0, false⟩

def natCropIn (S : List Bool) : Fin 5 → List Bool :=
  Fin.addCases (m := 2 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σNC S)).A (fun _ => [])

theorem natCropIn_val (S : List Bool) (j : Fin 5) :
    natCropIn S j = if j.val = 0 then S else if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

theorem natCropStage (x : ℕ) : ∃ o : Fin 5 → List Bool,
    Step (Rewind.machine natCropW.toProg.compile) (2 * (natBitLength x * 29 + 13) + 2) (fun _ => 0)
      (natCropIn (frame (natWord x))) (fun _ => 0) o ∧
    o 0 = frame (natWord x) ∧ o 1 = [false] ∧ o 3 = frame (pay x) := by
  set σ := σNC (frame (natWord x)) with hσ
  obtain ⟨τ, hw, e0, -, -, -, e3, -, -, -, ec⟩ := copyNatW_spec 0 (0 : Fin 3) 1 2 (by decide) (by decide) (by decide) x
    [] [false] 0 σ (by simp [hσ, σNC, nf, frame_eq_frameP]) rfl rfl rfl rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 natCropW σ τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 5) = Fin.castAdd 1 (0 : Fin 4) from rfl, ho]; exact e0
  · rw [show (1 : Fin 5) = Fin.castAdd 1 (1 : Fin 4) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (3 : Fin 5) = Fin.castAdd 1 (3 : Fin 4) from rfl, ho]; show τ.st 2 = frame (pay x); rw [e3]; rfl

/-! ## The layout -/

def cellSl : Fin 1 → Fin 1192 := fun _ => 3
def cropSl : Fin 5 → Fin 1192 := ![0, 3, 4, 5, 6]
def travSl (j : Fin 174) : Fin 1192 := ⟨if j.val = 0 then 5 else j.val + 6, by split_ifs <;> omega⟩
def cntSl : Fin 5 → Fin 1192 := ![47, 3, 1, 180, 181]
def erSl (j : Fin (1007 + 1 + 1)) : Fin 1192 :=
  ⟨if j.val < 1007 then j.val + 182 else if j.val = 1007 then 1189 else 1190, by split_ifs <;> omega⟩
def foldSl (j : Fin (1010 + 2 + 1)) : Fin 1192 :=
  ⟨if j.val = 0 then 36 else if j.val = 1 then 182 else if j.val = 2 then 180 else if j.val = 3 then 1
    else if j.val < 1010 then j.val + 179 else if j.val = 1010 then 1189 else if j.val = 1011 then 1190 else 47,
    by split_ifs <;> omega⟩
def outSl : Fin 4 → Fin 1192 := ![180, 3, 2, 1191]

theorem cellSl_inj : Function.Injective cellSl := fun a b _ => Subsingleton.elim a b
theorem cropSl_inj : Function.Injective cropSl := by decide
theorem cntSl_inj : Function.Injective cntSl := by decide
theorem outSl_inj : Function.Injective outSl := by decide
theorem travSl_inj : Function.Injective travSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [travSl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem erSl_inj : Function.Injective erSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [erSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
set_option maxHeartbeats 2000000 in
theorem foldSl_inj : Function.Injective foldSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [foldSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega

theorem cropSl_val (j : Fin 5) : (cropSl j).val = [0, 3, 4, 5, 6].getD j.val 0 := by fin_cases j <;> rfl
theorem cntSl_val (j : Fin 5) : (cntSl j).val = [47, 3, 1, 180, 181].getD j.val 0 := by fin_cases j <;> rfl
theorem outSl_val (j : Fin 4) : (outSl j).val = [180, 3, 2, 1191].getD j.val 0 := by fin_cases j <;> rfl

noncomputable def cellR := RecoveryFocus.machine cellSl NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def cropR := RecoveryFocus.machine cropSl (Rewind.machine natCropW.toProg.compile)
noncomputable def travR := RecoveryFocus.machine travSl CloseoutWitness.CanonicalTest.machine
noncomputable def cntR := RecoveryFocus.machine cntSl (Rewind.machine cntChkW.toProg.compile)
noncomputable def erR := RecoveryFocus.machine erSl (RecoveryScratchErase.resetMachine 1007)
noncomputable def foldR := RecoveryFocus.machine foldSl foldE
noncomputable def outR := RecoveryFocus.machine outSl (Rewind.machine outW.toProg.compile)

/-- **The envelope machine.** -/
noncomputable def envCodeM :=
  Composition.machine cellR (Composition.machine cropR (Composition.machine travR (Composition.machine cntR
    (Composition.machine erR (Composition.machine foldR outR)))))

/-- The entry: the code, the ruler `1^L`, the capacity ruler `1^T`; every other tape blank. -/
def envCodeIn (x L T : ℕ) : Fin 1192 → List Bool :=
  fun t => if t.val = 0 then frame (natWord x) else if t.val = 1 then List.replicate L true
    else if t.val = 1189 then List.replicate T true else []

/-- The fuel. -/
noncomputable def envCodeCost (x T : ℕ) : ℕ :=
  1 + 1 + ((2 * (natBitLength x * 29 + 13) + 2) + 1 + (CloseoutWitness.CanonicalTest.budget (pay x) + 1 +
    ((2 * cntChkCost (atomsOf x).length + 2) + 1 + ((2 * T + 4) + 1 +
      ((1 + 1 + ((atomsOf x).length * (foldCwE (natBitLength x) (atomsOf x).length + 1 + (2 * T + 4 + 1 + 0) + 2) +
        (atomsOf x).length + 3 + 1 + 1)) + 1 + (2 * 12 + 2))))))

theorem zeroH (t : ℕ) (sl : Fin t → Fin 1192) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-! ## The loop's bank -/

/-- The envelope loop's bank at atom `i`, by tape. -/
theorem foldBankE_val (ys : List (List Bool)) (b0 : Bool) (L T i c : ℕ) (j : Fin (1010 + 2 + 1)) :
    Fin.addCases (m := 1010 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch scrE T (Qe ys b0 L T i)) T (T + 1)) (fun _ => CompareMachine.word c) j =
    if j.val = 0 then ys.flatMap frame
    else if j.val = 1 then ZeroPadding.pad T (List.replicate i true)
    else if j.val = 2 then [flagAt ys b0 L i]
    else if j.val = 3 then List.replicate L true
    else if j.val < 1010 then List.replicate T false
    else if j.val = 1010 then List.replicate T true
    else if j.val = 1011 then List.replicate (T + 1) false
    else CompareMachine.word c := by
  rw [CWCore.addCases_val]
  by_cases h1 : j.val < 1010 + 2
  · rw [dif_pos h1]; unfold roundTapes; rw [CWCore.addCases_val]
    by_cases h2 : j.val < 1010
    · rw [dif_pos h2]
      unfold padScratch scratchCap
      by_cases h3 : 4 ≤ j.val
      · rw [if_pos ((scrE_iff ⟨j.val, h2⟩).mpr h3)]
        simp only [Qe, roundEIn]
        have e0 : j.val ≠ 0 := by omega
        have e1 : j.val ≠ 1 := by omega
        have e2 : j.val ≠ 2 := by omega
        have e3 : j.val ≠ 3 := by omega
        simp [e0, e1, e2, e3, h2, ZeroPadding.pad]
      · rw [if_neg (fun hh => h3 ((scrE_iff ⟨j.val, h2⟩).mp hh))]
        simp only [Qe, roundEIn, ZeroPadding.pad_zero]
        have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
        rcases this with e | e | e | e <;> simp [e]
    · rw [dif_neg h2]
      have : j.val = 1010 ∨ j.val = 1011 := by omega
      rcases this with e | e <;> simp [e]
  · rw [dif_neg h1]
    have e : j.val = 1012 := by omega
    simp [e]

theorem flagAt_all (ys : List (List Bool)) (b0 : Bool) (L : ℕ) :
    flagAt ys b0 L ys.length = (b0 && ys.all fun y => decide (pbits y ≤ L)) := by
  unfold flagAt; rw [List.take_length]

/-! ## The run -/

/-- **The envelope machine's run**: on the code `x`, with the ruler `1^L` and a capacity `1^T` that dominates the
loop, the output is `frame [decide (|X| ≤ L) && ∀ atoms, pbits ≤ L]`; the code and both rulers are kept. -/
theorem envCode_step (x L T : ℕ) (hL : 1 ≤ L) (hdec : ∀ y ∈ atomsOf x, Dec y)
    (hc : (atomsOf x).length ≤ T) (hS : ((atomsOf x).flatMap frame).length ≤ T) (hLT : L ≤ T)
    (hcw : foldCwE (natBitLength x) (atomsOf x).length + 1 ≤ T) :
    ∃ out : Fin 1192 → List Bool,
      Step envCodeM (envCodeCost x T) (fun _ => 0) (envCodeIn x L T) (fun _ => 0) out ∧
      out 0 = frame (natWord x) ∧ out 1 = List.replicate L true ∧ out 1189 = List.replicate T true ∧
      out 2 = frame [decide ((atomsOf x).length ≤ L) && (atomsOf x).all fun y => decide (pbits y ≤ L)] := by
  set ys := atomsOf x with hys
  set N := ys.length with hN
  set B0 := envCodeIn x L T with hB0
  have b0 : ∀ t : Fin 1192, t.val ≠ 0 → t.val ≠ 1 → t.val ≠ 1189 → B0 t = [] := by
    intro t h0 h1 h2; simp only [hB0, envCodeIn]; rw [if_neg h0, if_neg h1, if_neg h2]
  -- 1: the cell
  have d1 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock cellSl cellSl_inj (fun _ => 0) B0 (fun _ => rfl)
    (fun _ => b0 3 (by decide) (by decide) (by decide))
  rw [zeroH] at d1
  set B1 := install cellSl B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 1192, t.val ≠ 3 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b13 : B1 3 = [false] := install_slot cellSl cellSl_inj _ _ 0
  -- 2: the payload
  obtain ⟨o2, s2, c0, c1, c3⟩ := natCropStage x
  have d2 := s2.dock cropSl cropSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [natCropIn_val]
    fin_cases j
    · show B1 0 = _; rw [b1 _ (by decide)]; simp [hB0, envCodeIn]
    · show B1 3 = _; rw [b13]; rfl
    · show B1 4 = _; rw [b1 _ (by decide), b0 _ (by decide) (by decide) (by decide)]; rfl
    · show B1 5 = _; rw [b1 _ (by decide), b0 _ (by decide) (by decide) (by decide)]; rfl
    · show B1 6 = _; rw [b1 _ (by decide), b0 _ (by decide) (by decide) (by decide)]; rfl)
  rw [zeroH] at d2
  set B2 := install cropSl B1 o2 with hB2
  have b2 : ∀ t : Fin 1192, (∀ j, (cropSl j).val ≠ t.val) → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have b2hit : ∀ j, B2 (cropSl j) = o2 j := fun j => install_slot _ cropSl_inj _ _ _
  have fresh2 : ∀ t : Fin 1192, 7 ≤ t.val → t.val ≠ 1189 → B2 t = [] := by
    intro t h1 h2
    rw [b2 _ (by intro j; rw [cropSl_val]; fin_cases j <;> simp <;> omega), b1 _ (by omega),
      b0 _ (by omega) (by omega) h2]
  -- 3: the traversal
  obtain ⟨o3, r3, t30, t41, -⟩ := CloseoutWitness.CanonicalTest.fields_run (pay x)
  have d3 := (FrontLoopKit.step_of_ready r3).dock travSl travSl_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro j
    show B2 (travSl j) = (if j.val = 0 then frame (pay x) else [])
    by_cases h0 : j.val = 0
    · rw [if_pos h0, show travSl j = cropSl 3 from Fin.ext (by simp [travSl, h0]; rfl), b2hit, c3]
    · have hj := j.isLt
      rw [if_neg h0, fresh2 _ (by simp only [travSl]; rw [if_neg h0]; omega) (by simp only [travSl]; rw [if_neg h0]; omega)])
  rw [zeroH] at d3
  set B3 := install travSl B2 o3 with hB3
  have b3 : ∀ t : Fin 1192, (t.val ≠ 5 ∧ (t.val < 7 ∨ 180 ≤ t.val)) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [travSl] at hv; have hj := j.isLt; split_ifs at hv <;> omega)
  have b3A : B3 36 = ys.flatMap frame := (install_slot travSl travSl_inj B2 o3 30).trans (t30.trans (stream_atoms x))
  have b3C : B3 47 = CompareMachine.word N := by
    refine (install_slot travSl travSl_inj B2 o3 41).trans (t41.trans ?_)
    rw [value_pay, hN, hys, atoms_len]
  -- 4: the count check
  obtain ⟨o4, s4, k0, k1, k2, k3⟩ := cntChkStage N L hL
  have d4 := s4.dock cntSl cntSl_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro j; rw [cntIn_val]
    fin_cases j
    · show B3 47 = _; rw [b3C]; rfl
    · show B3 3 = _; rw [b3 _ (by decide), show (3 : Fin 1192) = cropSl 1 from rfl, b2hit, c1]; rfl
    · show B3 1 = _
      rw [b3 _ (by decide), b2 _ (by intro k; rw [cropSl_val]; fin_cases k <;> decide), b1 _ (by decide)]
      simp [hB0, envCodeIn]
    · show B3 180 = _; rw [b3 _ (by decide), fresh2 _ (by decide) (by decide)]; rfl
    · show B3 181 = _; rw [b3 _ (by decide), fresh2 _ (by decide) (by decide)]; rfl)
  rw [zeroH] at d4
  set B4 := install cntSl B3 o4 with hB4
  have b4 : ∀ t : Fin 1192, (∀ j, (cntSl j).val ≠ t.val) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have b4hit : ∀ j, B4 (cntSl j) = o4 j := fun j => install_slot _ cntSl_inj _ _ _
  have fresh4 : ∀ t : Fin 1192, 182 ≤ t.val → t.val ≠ 1189 → B4 t = [] := by
    intro t h1 h2
    rw [b4 _ (by intro j; rw [cntSl_val]; fin_cases j <;> simp <;> omega), b3 _ (by omega), fresh2 _ (by omega) h2]
  -- 5: the loop's erase
  have d5 := (CWCore.erase_step 1007 T 0).dock erSl erSl_inj (fun _ => 0) B4 (fun _ => rfl) (by
    intro j; rw [CWCore.erIn_val]
    have hj := j.isLt
    by_cases h1 : j.val < 1007
    · rw [if_pos h1, fresh4 _ (by simp only [erSl]; rw [if_pos h1]; omega) (by simp only [erSl]; rw [if_pos h1]; omega)]
    · rw [if_neg h1]
      by_cases h2 : j.val = 1007
      · rw [if_pos h2, show erSl j = (1189 : Fin 1192) from Fin.ext (by simp [erSl, h2]),
          b4 _ (by intro k; rw [cntSl_val]; fin_cases k <;> decide), b3 _ (by decide),
          b2 _ (by intro k; rw [cropSl_val]; fin_cases k <;> decide), b1 _ (by decide)]
        simp [hB0, envCodeIn]
      · rw [if_neg h2, show erSl j = (1190 : Fin 1192) from Fin.ext (by simp only [erSl]; split_ifs <;> omega),
          fresh4 _ (by decide) (by decide)]; rfl)
  rw [zeroH] at d5
  set B5 := install erSl B4 (CWCore.erOut 1007 T 0) with hB5
  have b5 : ∀ t : Fin 1192, (t.val < 182 ∨ t.val = 1191) → B5 t = B4 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [erSl] at hv; have hj := j.isLt; split_ifs at hv <;> omega)
  have b5h : ∀ j, B5 (erSl j) = CWCore.erOut 1007 T 0 j := fun j => install_slot erSl erSl_inj B4 _ j
  -- 6: the envelope loop
  have fE := foldE_run ys (natBitLength x) (fun y hy => (atoms_width x y hy).le) hdec (decide (N ≤ L)) L T (T + 1)
    (le_refl _) hc hS hLT hcw
  have d6 := (FrontLoopKit.step_of_ready fE).dock foldSl foldSl_inj (fun _ => 0) B5 (fun _ => rfl) (by
    intro j
    rw [foldBankE_val]
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · rw [if_pos h0, show foldSl j = (36 : Fin 1192) from Fin.ext (by simp [foldSl, h0]), b5 _ (by decide),
        b4 _ (by intro k; rw [cntSl_val]; fin_cases k <;> decide), b3A]
    rw [if_neg h0]
    by_cases h1 : j.val = 1
    · rw [if_pos h1, show foldSl j = erSl 0 from Fin.ext (by simp [foldSl, erSl, h1]), b5h, CWCore.erOut_val]
      simp [ZeroPadding.pad]
    rw [if_neg h1]
    by_cases h2 : j.val = 2
    · rw [if_pos h2, show foldSl j = cntSl 3 from Fin.ext (by simp [foldSl, h2]; rfl), b5 _ (by decide), b4hit, k3]
      simp [flagAt]
    rw [if_neg h2]
    by_cases h3 : j.val = 3
    · rw [if_pos h3, show foldSl j = cntSl 2 from Fin.ext (by simp [foldSl, h3]; rfl), b5 _ (by decide), b4hit, k2]
    rw [if_neg h3]
    by_cases h4 : j.val < 1010
    · rw [if_pos h4, show foldSl j = erSl ⟨j.val - 3, by omega⟩ from
          Fin.ext (by simp only [foldSl, erSl]; split_ifs <;> omega), b5h, CWCore.erOut_val, if_pos (by simp; omega)]
    rw [if_neg h4]
    by_cases h5 : j.val = 1010
    · rw [if_pos h5, show foldSl j = erSl 1007 from Fin.ext (by simp [foldSl, erSl, h5]), b5h, CWCore.erOut_val]
      simp
    rw [if_neg h5]
    by_cases h6 : j.val = 1011
    · rw [if_pos h6, show foldSl j = erSl 1008 from Fin.ext (by simp [foldSl, erSl, h6]), b5h, CWCore.erOut_val]
      simp
    rw [if_neg h6, show foldSl j = cntSl 0 from Fin.ext (by simp only [foldSl]; split_ifs <;> first | omega | rfl),
      b5 _ (by decide), b4hit, k0])
  rw [zeroH] at d6
  set OE := Fin.addCases (m := 1010 + 2) (n := 1) (motive := fun _ => List Bool)
    (roundTapes (padScratch scrE T (Qe ys (decide (N ≤ L)) L T N)) T (T + 1))
    (fun _ => CompareMachine.word N) with hOE
  set B6 := install foldSl B5 OE with hB6
  have b6 : ∀ t : Fin 1192, (t.val < 180 ∧ t.val ≠ 1 ∧ t.val ≠ 36 ∧ t.val ≠ 47 ∨ t.val = 181 ∨ t.val = 1191) →
      B6 t = B5 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [foldSl] at hv; have hj := j.isLt; split_ifs at hv <;> omega)
  have b6h : ∀ j, B6 (foldSl j) = OE j := fun j => install_slot foldSl foldSl_inj B5 OE j
  have b6F : B6 180 = [decide (N ≤ L) && ys.all fun y => decide (pbits y ≤ L)] := by
    rw [show (180 : Fin 1192) = foldSl 2 from rfl, b6h, hOE, foldBankE_val]
    simp [hN, flagAt_all]
  -- 7: the output
  obtain ⟨o7, s7, -, -, w2⟩ := outStage (decide (N ≤ L) && ys.all fun y => decide (pbits y ≤ L))
  have d7 := s7.dock outSl outSl_inj (fun _ => 0) B6 (fun _ => rfl) (by
    intro j; rw [outIn_val]
    fin_cases j
    · show B6 180 = _; rw [b6F]; rfl
    · show B6 3 = _
      rw [b6 _ (by decide), b5 _ (by decide), show (3 : Fin 1192) = cntSl 1 from rfl, b4hit, k1]; rfl
    · show B6 2 = _
      rw [b6 _ (by decide), b5 _ (by decide), b4 _ (by intro k; rw [cntSl_val]; fin_cases k <;> decide),
        b3 _ (by decide), b2 _ (by intro k; rw [cropSl_val]; fin_cases k <;> decide), b1 _ (by decide),
        b0 _ (by decide) (by decide) (by decide)]; rfl
    · show B6 1191 = _
      rw [b6 _ (by decide), b5 _ (by decide), fresh4 _ (by decide) (by decide)]; rfl)
  rw [zeroH] at d7
  set B7 := install outSl B6 o7 with hB7
  have b7 : ∀ t : Fin 1192, (∀ j, (outSl j).val ≠ t.val) → B7 t = B6 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq d7)))))
  have run' : Step envCodeM _ (fun _ => 0) B0 (fun _ => 0) B7 := run
  refine ⟨B7, run'.enlarge (by unfold envCodeCost; exact le_refl _), ?_, ?_, ?_, ?_⟩
  · rw [b7 _ (by intro k; rw [outSl_val]; fin_cases k <;> decide), b6 _ (by decide), b5 _ (by decide),
      b4 _ (by intro k; rw [cntSl_val]; fin_cases k <;> decide), b3 _ (by decide),
      show (0 : Fin 1192) = cropSl 0 from rfl, b2hit, c0]
  · rw [b7 _ (by intro k; rw [outSl_val]; fin_cases k <;> decide), show (1 : Fin 1192) = foldSl 3 from rfl, b6h, hOE,
      foldBankE_val]
    simp
  · rw [b7 _ (by intro k; rw [outSl_val]; fin_cases k <;> decide), show (1189 : Fin 1192) = foldSl 1010 from rfl, b6h,
      hOE, foldBankE_val]
    simp
  · rw [show (2 : Fin 1192) = outSl 2 from rfl]
    exact (install_slot outSl outSl_inj B6 o7 2).trans w2

end NearCubicWires.WireExponent3_5.UnionMachine.CWEnvCode
