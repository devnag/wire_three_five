import Proof.Wire_3_5.UnionMachine.CWParTops

/-! # C6 front, U5, the code writers: the parity writer's bottoms loop, with its capacity

The parity's bottoms (P3:3092-3094) are written by the loop `CWParRound.foldP`, which runs on padded round tapes: its
scratch erased to `0^T` against a ruler `1^T`. This machine (`loopM`, 396 tapes) computes the ruler from `1^q` (base's
unary polynomial `C·(q+1)^24`), writes the counter's count word `[false]`, erases the loop's scratch, and runs the loop
driven by the count word `false :: 1^k`:
* tapes `0` `frame WLv.bits`, `1` `frame P3v.bits`, `2` the codes' accumulator, `3`, `4` the counter, `5..330` the
  loop's scratch, `331` its capacity tape, `332` the count word, `333..394` the polynomial (`1^q` on `333`, `1^T` on
  `384`), `395` spare.

Paper quantity of the main type (**`loop_step`**): the codes of all `k` bottoms of the encoding parity. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt NearCubicWires.WireExponent3_5.UnionMachine.CWParRound
open NearCubicWires.WireExponent3_5.UnionMachine.CWParDock (cell_dock)
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (erIn erOut erIn_val erOut_val erase_step addCases_val)
open NearCubicWires.WireExponent3_5.UnionMachine.CWMain (polyIn_val)
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.WireExponent3_5.Transfer

/-! ## The layout -/

def polySl (j : Fin 62) : Fin 396 := ⟨j.val + 333, by omega⟩
def erSl (j : Fin (326 + 1 + 1)) : Fin 396 :=
  ⟨if j.val < 326 then j.val + 5 else if j.val = 326 then 384 else 331, by split_ifs <;> omega⟩
def foldSl (j : Fin (331 + 2 + 1)) : Fin 396 :=
  ⟨if j.val < 331 then j.val else if j.val = 331 then 384 else if j.val = 332 then 331 else 332, by split_ifs <;> omega⟩

theorem polySl_inj : Function.Injective polySl := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp [polySl] at this; omega)
theorem erSl_inj : Function.Injective erSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [erSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem foldSl_inj : Function.Injective foldSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [foldSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega

/-- **The bottoms loop machine** at the capacity coefficient `C`. -/
noncomputable def loopM (C : ℕ) :=
  Composition.machine (RecoveryFocus.machine polySl (PCPSerializerCapacity.Power.machine 24 C))
    (Composition.machine (RecoveryFocus.machine (fun _ : Fin 1 => (4 : Fin 396)) NearCubicWires.WireExponent3_5.PrimT.cellM)
      (Composition.machine (RecoveryFocus.machine erSl (RecoveryScratchErase.resetMachine 326))
        (RecoveryFocus.machine foldSl foldP)))

/-- The loop machine's entry: the two codes, the count word, the ruler `1^q`. -/
def loopIn (W P K Q : List Bool) : Fin 396 → List Bool :=
  fun t => if t.val = 0 then W else if t.val = 1 then P else if t.val = 332 then K else if t.val = 333 then Q else []

/-- The loop's bank at bottom `j`, by tape. -/
theorem foldBankP_val (wl p3 T j c : ℕ) (i : Fin (331 + 2 + 1)) :
    Fin.addCases (m := 331 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch scrP T (Qp wl p3 j)) T (T + 1)) (fun _ => CompareMachine.word c) i =
    if h : i.val < 5 then Qp wl p3 j ⟨i.val, by omega⟩
    else if i.val < 331 then List.replicate T false
    else if i.val = 331 then List.replicate T true
    else if i.val = 332 then List.replicate (T + 1) false
    else CompareMachine.word c := by
  rw [addCases_val]
  by_cases h1 : i.val < 331 + 2
  · rw [dif_pos h1]; unfold roundTapes; rw [addCases_val]
    by_cases h2 : i.val < 331
    · rw [dif_pos h2]
      unfold padScratch scratchCap
      by_cases h3 : 5 ≤ i.val
      · rw [if_pos ((scrP_iff ⟨i.val, h2⟩).mpr h3)]
        simp only [Qp, roundPIn]
        have e0 : i.val ≠ 0 := by omega
        have e1 : i.val ≠ 1 := by omega
        have e2 : i.val ≠ 2 := by omega
        have e3 : i.val ≠ 3 := by omega
        have e4 : i.val ≠ 4 := by omega
        rw [dif_neg (show ¬ i.val < 5 by omega)]
        simp [e0, e1, e2, e3, e4, h2, ZeroPadding.pad]
      · rw [if_neg (fun hh => h3 ((scrP_iff ⟨i.val, h2⟩).mp hh)), ZeroPadding.pad_zero, dif_pos (by omega)]
    · rw [dif_neg h2]
      rw [dif_neg (by omega)]
      have : i.val = 331 ∨ i.val = 332 := by omega
      rcases this with e | e <;> simp [e]
  · rw [dif_neg h1, dif_neg (by omega)]
    have e : i.val = 333 := by omega
    simp [e]

/-- The loop machine's fuel. -/
noncomputable def loopCost (k q C cw : ℕ) : ℕ :=
  PCPSerializerCapacity.Power.budget 24 C q + 1 + (1 + 1 + ((2 * BlockPlatform.UnaryCalc.value 24 C q + 4) + 1 +
    (1 + 1 + (k * (cw + 1 + (2 * BlockPlatform.UnaryCalc.value 24 C q + 4 + 1 + 0) + 2) + k + 3 + 1 + 1))))

/-- **The bottoms loop**: from the shared codes, the count word and `1^q`, the codes of all `k` bottoms, for a
capacity `T = C·(q+1)^24` that dominates the rounds. -/
theorem loop_step (wl p3 k q C cw : ℕ)
    (hcw : ∀ j < k, roundPCost wl p3 j (accOf wl p3 j) ≤ cw)
    (hcwT : cw + 1 ≤ BlockPlatform.UnaryCalc.value 24 C q)
    (hlen : ∀ j ≤ k, ∀ t, (Qp wl p3 j t).length ≤ BlockPlatform.UnaryCalc.value 24 C q) :
    ∃ out : Fin 396 → List Bool,
      Step (loopM C) (loopCost k q C cw) (fun _ => 0)
        (loopIn (frame wl.bits) (frame p3.bits) (CompareMachine.word k) (List.replicate q true)) (fun _ => 0) out ∧
      out 0 = frame wl.bits ∧ out 1 = frame p3.bits ∧ out 2 = (accOf wl p3 k).flatMap frame ∧
      out 3 = sgl k.bits ∧ out 4 = CompareMachine.word k.bits.length ∧ out 332 = CompareMachine.word k := by
  set T := BlockPlatform.UnaryCalc.value 24 C q with hT
  set B0 := loopIn (frame wl.bits) (frame p3.bits) (CompareMachine.word k) (List.replicate q true) with hB0
  have f0 : ∀ t : Fin 396, t.val ≠ 0 → t.val ≠ 1 → t.val ≠ 332 → t.val ≠ 333 → B0 t = [] := by
    intro t h0 h1 h2 h3; simp only [hB0, loopIn]; rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]
  -- 1: the capacity `1^T`
  obtain ⟨o1, s1, -, q1⟩ := BlockPlatform.UnaryCalc.poly_step 24 C q
  have d1 := s1.dock polySl polySl_inj (fun _ => 0) B0 (fun _ => rfl) (by
    intro j; rw [polyIn_val]
    by_cases h0 : j.val = 0
    · rw [if_pos h0, show polySl j = (333 : Fin 396) from Fin.ext (by simp [polySl, h0])]; simp [hB0, loopIn]
    · rw [if_neg h0]; have hj := j.isLt
      rw [f0 _ (by simp [polySl]) (by simp [polySl]) (by simp [polySl]) (by simp [polySl]; omega)])
  rw [CWParDock.zeroH] at d1
  set B1 := install polySl B0 o1 with hB1
  have b1 : ∀ t : Fin 396, t.val < 333 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by have := congrArg Fin.val e; simp [polySl] at this; omega)
  have b1T : B1 384 = List.replicate T true := (install_slot polySl polySl_inj B0 o1 51).trans q1
  -- 2: the counter's count word `[false]`
  have d2 := cell_dock (4 : Fin 396) B1 (by rw [b1 _ (by decide), f0 _ (by decide) (by decide) (by decide) (by decide)])
  set B2 := install (fun _ : Fin 1 => (4 : Fin 396)) B1 (fun _ => [false]) with hB2
  have b2 : ∀ t : Fin 396, t.val ≠ 4 → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b24 : B2 4 = [false] := install_slot (fun _ : Fin 1 => (4 : Fin 396)) (fun a b _ => Subsingleton.elim a b) _ _ 0
  -- 3: the erase of the loop's scratch
  have d3 := (erase_step 326 T 0).dock erSl erSl_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro j; rw [erIn_val]
    have hj := j.isLt
    by_cases h1 : j.val < 326
    · rw [if_pos h1, show erSl j = ⟨j.val + 5, by omega⟩ from Fin.ext (by simp [erSl, h1]),
        b2 _ (by simp), b1 _ (by simp; omega), f0 _ (by simp) (by simp) (by simp; omega) (by simp; omega)]
    · rw [if_neg h1]
      by_cases h2 : j.val = 326
      · rw [if_pos h2, show erSl j = (384 : Fin 396) from Fin.ext (by simp [erSl, h2]), b2 _ (by decide), b1T]
      · rw [if_neg h2, show erSl j = (331 : Fin 396) from Fin.ext (by simp only [erSl]; split_ifs <;> omega),
          b2 _ (by decide), b1 _ (by decide), f0 _ (by decide) (by decide) (by decide) (by decide)]; rfl)
  rw [CWParDock.zeroH] at d3
  set B3 := install erSl B2 (erOut 326 T 0) with hB3
  have b3h : ∀ j, B3 (erSl j) = erOut 326 T 0 j := fun j => install_slot _ erSl_inj _ _ _
  have b3 : ∀ t : Fin 396, (t.val < 5 ∨ t.val = 332 ∨ (332 < t.val ∧ t.val ≠ 384)) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [erSl] at hv; have hj := j.isLt; split_ifs at hv <;> omega)
  -- 4: the loop
  have fP := foldP_run wl p3 k T (T + 1) cw (le_refl _) hcw hcwT hlen
  have d4 := (FrontLoopKit.step_of_ready fP).dock foldSl foldSl_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro i
    rw [foldBankP_val]
    have hi := i.isLt
    by_cases h5 : i.val < 5
    · rw [dif_pos h5, show foldSl i = ⟨i.val, by omega⟩ from Fin.ext (by simp [foldSl]; omega), b3 _ (by simp <;> omega)]
      simp only [Qp, roundPIn]
      by_cases h0 : i.val = 0
      · simp only [h0, if_true]; rw [b2 _ (by simp <;> omega), b1 _ (by simp <;> omega)]; simp [hB0, loopIn, h0]
      · by_cases h1 : i.val = 1
        · simp only [h1, if_true, show (1 : ℕ) ≠ 0 by decide, if_false]
          rw [b2 _ (by simp <;> omega), b1 _ (by simp <;> omega)]; simp [hB0, loopIn, h1]
        · by_cases h4 : i.val = 4
          · simp only [h4, show (4 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 2 by decide,
              show (4 : ℕ) ≠ 3 by decide, if_false, if_true]
            show B2 4 = _
            rw [b24]; simp [CompareMachine.word]
          · rw [b2 _ (by simp <;> omega), b1 _ (by simp <;> omega), f0 _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
              (by simp <;> omega)]
            have : i.val = 2 ∨ i.val = 3 := by omega
            rcases this with e | e <;> simp [e, accOf, sgl]
    · rw [dif_neg h5]
      by_cases h6 : i.val < 331
      · rw [if_pos h6, show foldSl i = erSl ⟨i.val - 5, by omega⟩ from
          Fin.ext (by simp only [foldSl, erSl]; split_ifs <;> omega), b3h, erOut_val, if_pos (by simp; omega)]
      · rw [if_neg h6]
        by_cases h7 : i.val = 331
        · rw [if_pos h7, show foldSl i = erSl 326 from Fin.ext (by simp [foldSl, erSl, h7]), b3h, erOut_val]; simp
        · rw [if_neg h7]
          by_cases h8 : i.val = 332
          · rw [if_pos h8, show foldSl i = erSl 327 from Fin.ext (by simp [foldSl, erSl, h8]), b3h, erOut_val]; simp
          · rw [if_neg h8, show foldSl i = (332 : Fin 396) from Fin.ext (by simp only [foldSl]; split_ifs <;> omega),
              b3 _ (by decide), b2 _ (by decide), b1 _ (by decide)]
            simp [hB0, loopIn])
  rw [CWParDock.zeroH] at d4
  set OE := Fin.addCases (m := 331 + 2) (n := 1) (motive := fun _ => List Bool)
    (roundTapes (padScratch scrP T (Qp wl p3 k)) T (T + 1)) (fun _ => CompareMachine.word k) with hOE
  set B4 := install foldSl B3 OE with hB4
  have b4h : ∀ i, B4 (foldSl i) = OE i := fun i => install_slot _ foldSl_inj _ _ _
  have out5 : ∀ n (hn : n < 5), B4 ⟨n, by omega⟩ = Qp wl p3 k ⟨n, by omega⟩ := by
    intro n hn
    rw [show (⟨n, _⟩ : Fin 396) = foldSl ⟨n, by omega⟩ from Fin.ext (by simp [foldSl]; omega), b4h, hOE,
      foldBankP_val, dif_pos hn]
  have run := d1.seq (d2.seq (d3.seq d4))
  have run' : Step (loopM C) _ (fun _ => 0) B0 (fun _ => 0) B4 := run
  refine ⟨B4, run'.enlarge (by unfold loopCost; exact le_refl _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 396) = ⟨0, by omega⟩ from rfl, out5 0 (by decide)]; simp [Qp, roundPIn]
  · rw [show (1 : Fin 396) = ⟨1, by omega⟩ from rfl, out5 1 (by decide)]; simp [Qp, roundPIn]
  · rw [show (2 : Fin 396) = ⟨2, by omega⟩ from rfl, out5 2 (by decide)]; simp [Qp, roundPIn]
  · rw [show (3 : Fin 396) = ⟨3, by omega⟩ from rfl, out5 3 (by decide)]; simp [Qp, roundPIn]
  · rw [show (4 : Fin 396) = ⟨4, by omega⟩ from rfl, out5 4 (by decide)]; simp [Qp, roundPIn]
  · rw [show (332 : Fin 396) = foldSl 333 from rfl, b4h, hOE, foldBankP_val]; simp

end NearCubicWires.WireExponent3_5.UnionMachine.CWParLoop
