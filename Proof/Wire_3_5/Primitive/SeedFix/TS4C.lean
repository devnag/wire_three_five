import Proof.Wire_3_5.Primitive.Writers.ThrData2

/-! # thrStage4U, part 5: the data stage's first three phases, and its collection after the hash numbers

P3:3068-3084 (lem:primitive: a call reads its circuits and carriers; the tuple's and the carriers' gate tables, the
slice lengths `thrCounts`): PA's v2 data stage (`ThrData2`) is the fill, the inputs, the tables, then the collection
`[0] ++ marks (unaryList thrCounts) ++ [0]`. v4 runs the first three unchanged (`preT2`, **`preA_step`**, with every
fact the collection and the outputs need), writes `[0] ++ marks (unaryList hashNums)` (part 4), and then runs the
collection without its leading `0` (`collectTail`, **`collectTail_spec`**: the counts appended after any prefix).

Paper quantities of the main types: the tables and the slice lengths `thrCounts` (the data word's second part). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## The collection after a prefix -/

/-- PA's collection without its leading `0`: the carriers' counts, the tuple's count, the closing `0`. -/
def collectTail : WM DS DR :=
  .seq (slotsC carC) (.seq (.seq (emitUW (sSym 0 5)) (emitPair sOUT rOP false)) (.wr sOUT false))

def collectTailCost (cx : List ℕ) (c : ℕ) : ℕ :=
  slotsCost carC cx + 1 + ((c * 19 + 1 + 1 + 15) + 1 + 1)

section Col
variable (cap : ℕ)

/-- **The collection after a prefix**: the output stream `pre` (head at its end) becomes
`pre ++ marks (unaryList (cx ++ [c])) ++ [0]`. -/
theorem collectTail_spec (σ : WState DS DR) (cx : List ℕ) (c : ℕ) (hx : cx.length ≤ 2)
    (hcx : ∀ k : Fin 2, ∀ h : k.val < cx.length, readTapeBit (σ.st (sCar k 0)) (σ.sh (sCar k 0)) = true ∧
      σ.st (sCar k 5) = List.replicate (cx.get ⟨k.val, h⟩) true ∧ σ.sh (sCar k 5) = 0)
    (hcx' : ∀ k : Fin 2, cx.length ≤ k.val → readTapeBit (σ.st (sCar k 0)) (σ.sh (sCar k 0)) = false)
    (hT : σ.st (sSym 0 5) = List.replicate c true ∧ σ.sh (sSym 0 5) = 0)
    (hOh : σ.sh sOUT = (σ.st sOUT).length) (hOP : σ.val rOP = 0)
    (hcap : 2 * (unaryList cx).length + 2 * (unaryList [c]).length + 2 ≤ cap) :
    ∃ τ : WState DS DR, WExec cap collectTail σ τ (collectTailCost cx c) ∧
      τ.st sOUT = σ.st sOUT ++ marks (unaryList (cx ++ [c])) ++ [false] ∧
      (∀ s, s ≠ sOUT → τ.st s = σ.st s) ∧ (∀ r, r ≠ rOP → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, q1, a1, b1, c1, d1, e1, g1, i1⟩ := slotsC_spec cap carC cx σ (by simpa [carC] using hx)
    (fun k h hl => by
      rw [carC_get]
      exact hcx ⟨k, by simpa [carC] using hl⟩ h)
    (fun k hl hk => by
      rw [carC_get]
      exact hcx' ⟨k, by simpa [carC] using hl⟩ hk)
    carC_no carC_pw hOh (by rw [hOP]; omega)
  have csh : ∀ j, τ1.sh (sSym 0 j) = σ.sh (sSym 0 j) := by
    intro j
    exact e1 _ (sSym_ne_low _ _ _ sOUT_low) (fun t ht => by
      simp only [carC, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact sSym_ne_sCar _ _ _ _)
  have cst : ∀ j, τ1.st (sSym 0 j) = σ.st (sSym 0 j) := by
    intro j
    exact d1 _ (sSym_ne_low _ _ _ sOUT_low)
  obtain ⟨hT5, hT5h⟩ := hT
  have hml := RepairOrdinary.Streaming.marks_length (List.replicate c true)
  have hu1 : (unaryList [c]).length = c + 1 := by simp [unaryList]
  have r1 : τ1.val rOP = 2 * (unaryList cx).length := by rw [c1, hOP]; ring
  have u1 := emitUW_spec cap (sSym 0 5) (sSym_ne_low _ _ _ sOUT_low) c τ1 (by rw [cst]; exact hT5)
    (by rw [csh]; exact hT5h) b1 (by rw [r1]; omega)
  set τ3 := (appendO τ1 sOUT rOP (marks (List.replicate c true))).seth (sSym 0 5) c with hτ3
  have u2 := emitPair_spec cap sOUT rOP false τ3
    (by simp [hτ3, Function.update_apply, Ne.symm (sSym_ne_low 0 5 sOUT sOUT_low), b1])
    (by simp [hτ3] at hml ⊢; rw [r1]; omega)
  set τ2 := appendO τ3 sOUT rOP [true, false] with hτ2
  have b2 : τ2.sh sOUT = (τ2.st sOUT).length := by
    simp [hτ2, hτ3, Function.update_apply, Ne.symm (sSym_ne_low 0 5 sOUT sOUT_low), b1] at hml ⊢ <;> omega
  have a2 : τ2.st sOUT = τ1.st sOUT ++ marks (unaryList [c]) := by
    rw [marks_unary_cons]
    simp [hτ2, hτ3, unaryList, marks, List.append_assoc]
  have d2 : ∀ s, s ≠ sOUT → τ2.st s = τ1.st s := fun s hs => by
    simp [hτ2, hτ3, Function.update_apply, hs]
  have g2 : ∀ r, r ≠ rOP → τ2.val r = τ1.val r := fun r hr => by
    simp [hτ2, hτ3, Function.update_apply, hr]
  have i2 : τ2.cell = τ1.cell := by simp [hτ2, hτ3]
  have q2 : WExec cap (.seq (emitUW (sSym 0 5)) (emitPair sOUT rOP false)) τ1 τ2 (c * 19 + 1 + 1 + 15) :=
    WExec.seq u1 u2
  have w3 := WExec.wr (cap := cap) sOUT false τ2
  refine ⟨τ2.sets sOUT (writeTapeBit (τ2.st sOUT) (τ2.sh sOUT) false), ?_, ?_, ?_, ?_, ?_⟩
  · exact WExec.cast cap (WExec.seq q1 (WExec.seq q2 w3)) rfl (by unfold collectTailCost; omega)
  · simp only [WState.sets_st, Function.update_apply, if_pos rfl]
    rw [b2, wtb_end, a2, a1, unaryList_append, marks_append]
    simp [List.append_assoc]
  · intro s hs
    simp only [WState.sets_st, Function.update_apply, if_neg hs]
    rw [d2 s hs, d1 s hs]
  · intro r hr
    simp only [WState.sets_val]
    rw [g2 r hr, g1 r hr]
  · simp only [WState.sets_cell]
    rw [i2, i1]

end Col

/-! ## The first three phases -/

/-- The fill, the inputs, the tables (PA's `coreT2` without its collection). -/
noncomputable def preT2 := Composition.machine (Composition.machine fillAct.compile setupW.toProg.compile) thrTabsM2

section Pre
variable {n : ℕ} (a' : ℕ) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))

noncomputable def preCost (L W : ℕ) : ℕ :=
  11 * W + 20 + 1 + 1 + 1 + setupCost n L (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) + 1 +
    thrTabsCost2 Cs L (oxOf carriers)

/-- **The first three phases**: from the stage's entry bank, the register-language state `σ2` with every fact the
collection and the stage's outputs need. -/
theorem preA_step (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L)
    (hcN : natBitLength n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ 2 * W + 2) :
    ∃ σ2 : WState DS DR,
      Step preT2 (preCost a' Cs carriers L W) (fun _ => 0)
        (rawIn (reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) n L W)
        (wenc (2 * W + 2) σ2).H (wenc (2 * W + 2) σ2).A ∧
      (∀ k : Fin 2, ∀ h : k.val < (carriers.map (·.length)).length,
        readTapeBit (σ2.st (sCar k 0)) (σ2.sh (sCar k 0)) = true ∧
        σ2.st (sCar k 5) = List.replicate ((carriers.map (·.length)).get ⟨k.val, h⟩) true ∧ σ2.sh (sCar k 5) = 0) ∧
      (∀ k : Fin 2, (carriers.map (·.length)).length ≤ k.val →
        readTapeBit (σ2.st (sCar k 0)) (σ2.sh (sCar k 0)) = false) ∧
      (σ2.st (sSym 0 5) = List.replicate (PrimT.ThrTab.tupleG Cs).length true ∧ σ2.sh (sSym 0 5) = 0) ∧
      σ2.st sOUT = [] ∧ σ2.sh sOUT = 0 ∧ σ2.val rOP = 0 ∧ σ2.val rN = 0 ∧
      σ2.st sIN = RepairOrdinary.frame (reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) ∧
      σ2.st (sSym 0 3) = (if a' = 0 then [] else
        FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, σ2.st (sCar k 3) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      (∀ k : Fin 2, carriers.length ≤ k.val → σ2.st (sCar k 3) = []) := by
  set w := reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl with hw
  set cap := 2 * W + 2 with hcap
  have hcl : (ReqBridge.thrCodes Cs).length = a' := by simp [ReqBridge.thrCodes]
  have h4 : 4 ≤ cap := by
    have hb : 1 ≤ natBitLength a' := by unfold natBitLength; omega
    have : 2 ^ 2 ≤ 2 ^ (natBitLength a' + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  -- 0: the fill and the cell
  have s0 := Exec.step (fillAct_exec w n L W)
  -- 1: the slots' inputs
  obtain ⟨τ1, q1, d1, b1, dx1, bx1, f1, i1, v1, c1⟩ := setup_spec cap n L true (ReqBridge.thrCodes Cs)
    (carriers.map Stars.Carrier.code) tl (σ0 w n L W) (by rw [hcl]; exact ha) (by simpa using hk)
    (by simp [σ0, hw]) rfl (by simp [σ0, sNT, sIN]) rfl (by simp [σ0, sLT, sIN, sNT]) rfl
    (fun i => ⟨σ0_sym w L W i 0, rfl, σ0_sym w L W i 1, rfl, σ0_sym w L W i 2, rfl⟩)
    (fun k => ⟨σ0_car w L W k 0, rfl, σ0_car w L W k 1, rfl, σ0_car w L W k 2, rfl⟩)
    rfl rfl rfl rfl rfl rfl rfl rfl hcN (by rw [hcl]; exact hcA) (by simpa using hcK) hcx hcy h4
  have s1 := Exec.step (WExec.exec cap q1)
  -- 2: the tables
  have keepS : ∀ i : Fin 4, ∀ j : Fin 1789, 3 ≤ j.val → τ1.st (sSym i j) = [] ∧ τ1.sh (sSym i j) = 0 := by
    intro i j hj
    have hnot : ∀ i', ¬ tmem (sSym i j) (symTrip i') := by
      intro i' hm
      simp only [symTrip, tmem, sSym_eq_iff] at hm
      rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp at hj
    have := f1 (sSym i j) hnot (fun k => not_tmem_carTrip_of_sym _ _ _) (sSym_ne_low _ _ _ (by decide))
    exact ⟨this.1.trans (σ0_sym w L W i j), this.2⟩
  have keepC : ∀ k : Fin 2, ∀ j : Fin 1357, 3 ≤ j.val → τ1.st (sCar k j) = [] ∧ τ1.sh (sCar k j) = 0 := by
    intro k j hj
    have hnot : ∀ k', ¬ tmem (sCar k j) (carTrip k') := by
      intro k' hm
      simp only [carTrip, tmem, sCar_eq_iff] at hm
      rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp at hj
    have := f1 (sCar k j) (fun i => not_tmem_symTrip_of_car _ _ _) hnot (sCar_ne_low _ _ _ (by decide))
    exact ⟨this.1.trans (σ0_car w L W k j), this.2⟩
  obtain ⟨σ2, s2, p2, px2, f2, v2, c2, n2⟩ := thrTabs2_step cap Cs L ha hL h2 (oxOf carriers)
    (fun k X hX => by
      unfold oxOf at hX
      exact hLX X (List.mem_of_getElem? hX))
    τ1
    (fun i h => by
      have := d1 i (by rw [hcl]; exact h)
      simpa [ReqBridge.thrCodes] using this)
    (fun i h => b1 i (by rw [hcl]; exact h))
    (fun k => by
      unfold oxOf
      by_cases hk' : k.val < carriers.length
      · rw [List.getElem?_eq_getElem hk']
        have := dx1 k (by simpa using hk')
        simpa [carPre] using this
      · rw [List.getElem?_eq_none (by omega)]
        exact bx1 k (by simpa using (by omega : carriers.length ≤ k.val)))
    keepS keepC
  have oOUT : σ2.st sOUT = [] ∧ σ2.sh sOUT = 0 := by
    have a := f2 sOUT (fun i j => sSym_ne_low _ _ _ sOUT_low) (fun k j => sCar_ne_low _ _ _ sOUT_low)
    have b := f1 sOUT (fun i => low_not_tmem_sym _ sOUT_low i) (fun k => low_not_tmem_car _ sOUT_low k) (by decide)
    refine ⟨by rw [a.1, b.1]; simp [σ0, sOUT, sIN, sNT, sLT, sCT, sAUX], by rw [a.2, b.2]; rfl⟩
  have core : Step preT2 (preCost a' Cs carriers L W) (fun _ => 0) (rawIn w n L W) (wenc cap σ2).H
      (wenc cap σ2).A := (s0.seq s1).seq s2
  refine ⟨σ2, core, ?_, ?_, ⟨p2.1, p2.2.1⟩, oOUT.1, oOUT.2, ?_, ?_, ?_, p2.2.2, ?_, ?_⟩
  · intro k h
    have hk' : k.val < carriers.length := by simpa using h
    have := px2 k
    simp only [oxOf, List.getElem?_eq_getElem hk', carPost] at this
    obtain ⟨x1, x2, x3, _⟩ := this
    exact ⟨x1, by simpa using x2, x3⟩
  · intro k h
    have hk' : carriers.length ≤ k.val := by simpa using h
    have := px2 k
    simp only [oxOf, List.getElem?_eq_none hk', carPost] at this
    exact this
  · rw [v2, v1 rOP (by decide) (by decide)]; rfl
  · rw [v2, v1 rN (by decide) (by decide)]; rfl
  · have a := f2 sIN (fun i j => sSym_ne_low _ _ _ (by decide)) (fun k j => sCar_ne_low _ _ _ (by decide))
    rw [a.1, i1]
    simp [σ0, hw]
  · intro k h
    have := px2 k
    simp only [oxOf, List.getElem?_eq_getElem h, carPost] at this
    exact this.2.2.2
  · intro k h
    rw [n2 k (by simp [oxOf, List.getElem?_eq_none h]) 3]
    exact (keepC k 3 (by decide)).1

end Pre

end NearCubicWires.WireExponent3_5.PrimT.TS4
