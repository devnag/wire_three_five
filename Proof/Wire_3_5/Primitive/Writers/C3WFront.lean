import Proof.Wire_3_5.Primitive.Writers.C3WLay

/-! # C3 request writer, part 7: the front (the raw request, `1^n`, the fill count)

Paper quantity: none (the machine plumbing of alg:compiler's request writer, P3:1886-1906). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.GeoFront
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.C3Phase NearCubicWires.WireExponent3_5.PrimAsm.C3Dock

namespace Lay
variable (L : Lay)

theorem ws_cIN : (L.ws cIN).val = 0 := rfl
theorem ws_cNT : (L.ws cNT).val = 2 := rfl
theorem ws_cCT : (L.ws cCT).val = 3 := rfl
theorem ws_sH : (L.ws sH).val = 5 := rfl
theorem ws_sQ : (L.ws sQ).val = 6 := rfl
theorem ws_sM : (L.ws sM).val = 7 := rfl
theorem ws_sP : (L.ws sP).val = 8 := rfl
theorem xraw_val : L.xraw.val = WT + 1 := rfl
theorem xlg_val : L.xlg.val = WT + 2 := rfl
theorem xpw_val (k : Fin L.Tu) : (L.xpw k).val = WT + 15 + k.val := rfl
theorem xrec_val : L.xrec.val = WT + 15 + L.Tu := rfl
theorem oG1_val : L.oG1 = WT + 16 + L.Tu := rfl

/-! ## The slots -/

def sl1 : Fin 3 → Fin L.U := ![L.ws cIN, L.xraw, L.xlg]

theorem sl1_val (j : Fin 3) : (L.sl1 j).val = if j = 0 then 0 else if j = 1 then WT + 1 else WT + 2 := by
  fin_cases j <;> rfl

theorem sl1_inj : Function.Injective L.sl1 := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [sl1_val, sl1_val] at hv
  have hWT : WT = 64 := rfl
  fin_cases a <;> fin_cases b <;> simp at hv ⊢ <;> omega

theorem sl1_ne (i : Fin L.U) (h0 : i.val ≠ 0) (h1 : i.val ≠ WT + 1) (h2 : i.val ≠ WT + 2) : ∀ j, L.sl1 j ≠ i := by
  intro j e
  have hv := congrArg Fin.val e
  rw [sl1_val] at hv
  split_ifs at hv <;> omega

def sl2 (j : Fin 12) : Fin L.U :=
  if j = 0 then L.xraw else if j = 8 then L.ws cNT else if j = 9 then L.xpw (UnaryCalc.inputTape L.Dv) else L.xcp j

theorem sl2_val (j : Fin 12) : (L.sl2 j).val =
    if j = 0 then WT + 1 else if j = 8 then 2 else if j = 9 then WT + 15 else WT + 3 + j.val := by
  unfold sl2
  split_ifs <;> rfl

theorem sl2_inj : Function.Injective L.sl2 := by
  have hWT : WT = 64 := rfl
  intro a b h
  have hv := congrArg Fin.val h
  rw [sl2_val, sl2_val, hWT] at hv
  fin_cases a <;> fin_cases b <;> simp at hv ⊢

theorem sl2_ne (i : Fin L.U) (h2 : i.val ≠ 2) (h : i.val < WT + 1 ∨ WT + 16 ≤ i.val) : ∀ j, L.sl2 j ≠ i := by
  intro j e
  have hv := congrArg Fin.val e
  rw [sl2_val] at hv
  have := j.isLt
  split_ifs at hv <;> omega

def sl3 (k : Fin L.Tu) : Fin L.U := if k = UnaryCalc.outputTape L.Dv then L.ws cCT else L.xpw k

theorem sl3_val (k : Fin L.Tu) : (L.sl3 k).val = if k = UnaryCalc.outputTape L.Dv then 3 else WT + 15 + k.val := by
  unfold sl3
  split_ifs <;> rfl

theorem sl3_inj : Function.Injective L.sl3 := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [sl3_val, sl3_val] at hv
  split_ifs at hv with ha hb hb
  · rw [ha, hb]
  · omega
  · omega
  · exact Fin.ext (by omega)

theorem sl3_ne (i : Fin L.U) (h3 : i.val ≠ 3) (h : i.val < WT + 15 ∨ WT + 15 + L.Tu ≤ i.val) : ∀ k, L.sl3 k ≠ i := by
  intro k e
  have hv := congrArg Fin.val e
  rw [sl3_val] at hv
  have := k.isLt
  split_ifs at hv <;> omega

def sl4 : Fin 6 → Fin L.U := ![L.ws cCT, L.ws sH, L.ws sQ, L.ws sM, L.ws sP, L.xrec]

theorem sl4_val (j : Fin 6) : (L.sl4 j).val =
    if j = 0 then 3 else if j = 1 then 5 else if j = 2 then 6 else if j = 3 then 7 else if j = 4 then 8
      else WT + 15 + L.Tu := by
  fin_cases j <;> rfl

theorem sl4_inj : Function.Injective L.sl4 := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [sl4_val, sl4_val] at hv
  have hWT : WT = 64 := rfl
  fin_cases a <;> fin_cases b <;> simp at hv ⊢ <;> omega

theorem sl4_ne (i : Fin L.U) (h3 : i.val ≠ 3) (h5 : i.val ≠ 5) (h6 : i.val ≠ 6) (h7 : i.val ≠ 7) (h8 : i.val ≠ 8)
    (hr : i.val ≠ WT + 15 + L.Tu) : ∀ j, L.sl4 j ≠ i := by
  intro j e
  have hv := congrArg Fin.val e
  rw [sl4_val] at hv
  split_ifs at hv <;> omega

/-! ## The front -/

/-- **The front**: `Unframe`, `CapReader` (`1^n`), `UnaryCalc` (`1^{Cv(n+1)^Dv}`), the append. -/
noncomputable def frontM :=
  Composition.machine (Composition.machine (Composition.machine (RecoveryFocus.machine L.sl1 unM)
    (RecoveryFocus.machine L.sl2 crM)) (RecoveryFocus.machine L.sl3 (PCPSerializerCapacity.Power.machine L.Dv L.Cv)))
    (RecoveryFocus.machine L.sl4 (appM 32))

/-- The front's fill count. -/
def fillW (n h Q m pr : ℕ) : ℕ := UnaryCalc.value L.Dv L.Cv n + 32 * (h + Q + m + pr)

/-- The front's steps. -/
def frCost (w : List Bool) (n h Q m pr : ℕ) : ℕ :=
  2 * (2 * w.length + 1) + 2 + 1 + crCost n + 1 + PCPSerializerCapacity.Power.budget L.Dv L.Cv n + 1 +
    appCost 32 (UnaryCalc.value L.Dv L.Cv n) h Q m pr

/-- **The front's run**: from the entry streams (`frame w` on `cIN`, the unary numbers), `1^n` on `cNT` and the
fill count on `cCT`; every tape from `oG1` on still blank. -/
theorem front_run (w sfx : List Bool) (n h Q m pr : ℕ) (hw : w = RepairRepresentation.natWord n ++ sfx)
    (B : Fin L.U → List Bool) (st : Fin (CN + 1) → List Bool) (hI : L.Inv B st (WT + 1))
    (hin : st cIN = frame w) (hN : st cNT = []) (hC : st cCT = []) (hH : st sH = List.replicate h true)
    (hQ : st sQ = List.replicate Q true) (hM : st sM = List.replicate m true)
    (hP : st sP = List.replicate pr true) :
    ∃ B', Step L.frontM (L.frCost w n h Q m pr) (fun _ => 0) B (fun _ => 0) B' ∧
      L.Inv B' (Function.update (Function.update st cNT (List.replicate n true)) cCT
        (List.replicate (L.fillW n h Q m pr) true)) L.oG1 := by
  have hWT : WT = 64 := rfl
  have hTu : 1 ≤ L.Tu := (UnaryCalc.inputTape L.Dv).pos
  obtain ⟨hs, hc, hr, hrc, hz⟩ := hI
  have hzx : ∀ i : Fin L.U, WT + 1 ≤ i.val → B i = [] := hz
  -- 1
  obtain ⟨B1, s1, b1in, b1raw, b1o⟩ := un_dock L.sl1 L.sl1_inj w (fun _ => 0) (fun _ => rfl) B
    (by show B (L.ws cIN) = _; rw [hs, hin]) (hzx L.xraw (by rw [xraw_val])) (hzx L.xlg (by rw [xlg_val]; omega))
  have o1 : ∀ i : Fin L.U, i.val ≠ 0 → i.val ≠ WT + 1 → i.val ≠ WT + 2 → B1 i = B i :=
    fun i a b c => b1o i (L.sl1_ne i a b c)
  -- 2
  obtain ⟨B2, s2, b2raw, b2nt, b2pw, b2o⟩ := cr_dock L.sl2 L.sl2_inj n sfx (fun _ => 0) (fun _ => rfl) B1
    (by show B1 L.xraw = _; rw [← hw]; exact b1raw)
    (by
      intro j hj
      rw [o1 _ (by rw [sl2_val]; split_ifs <;> omega) (by rw [sl2_val]; split_ifs <;> omega)
        (by rw [sl2_val]; split_ifs <;> omega)]
      by_cases j8 : j = 8
      · subst j8; show B (L.ws cNT) = []; rw [hs, hN]
      · exact hzx _ (by rw [sl2_val]; split_ifs <;> omega))
  have o2 : ∀ i : Fin L.U, i.val ≠ 2 → (i.val < WT + 1 ∨ WT + 16 ≤ i.val) → B2 i = B1 i :=
    fun i a b => b2o i (L.sl2_ne i a b)
  -- 3
  have hio := UnaryCalc.output_ne_input L.Dv
  obtain ⟨B3, s3, b3ct, b3in, b3o⟩ := uc_dock L.Dv L.Cv n L.sl3 L.sl3_inj (fun _ => 0) (fun _ => rfl) B2
    (by
      show B2 (if UnaryCalc.inputTape L.Dv = UnaryCalc.outputTape L.Dv then _ else _) = _
      rw [if_neg (Ne.symm hio)]
      exact b2pw)
    (by
      intro k hk
      by_cases ko : k = UnaryCalc.outputTape L.Dv
      · subst ko
        show B2 (if UnaryCalc.outputTape L.Dv = UnaryCalc.outputTape L.Dv then _ else _) = _
        rw [if_pos rfl, o2 _ (by rw [ws_cCT]; omega) (Or.inl (by rw [ws_cCT]; omega)),
          o1 _ (by rw [ws_cCT]; omega) (by rw [ws_cCT]; omega) (by rw [ws_cCT]; omega), hs, hC]
      · show B2 (if k = UnaryCalc.outputTape L.Dv then _ else _) = _
        rw [if_neg ko]
        have hk0 : k.val ≠ 0 := fun e => hk (Fin.ext e)
        have := k.isLt
        rw [o2 _ (by rw [xpw_val]; omega) (Or.inr (by rw [xpw_val]; omega)),
          o1 _ (by rw [xpw_val]; omega) (by rw [xpw_val]; omega) (by rw [xpw_val]; omega)]
        exact hzx _ (by rw [xpw_val]; omega))
  have o3 : ∀ i : Fin L.U, i.val ≠ 3 → (i.val < WT + 15 ∨ WT + 15 + L.Tu ≤ i.val) → B3 i = B2 i :=
    fun i a b => b3o i (L.sl3_ne i a b)
  have o123 : ∀ i : Fin L.U, i.val ≠ 0 → i.val ≠ 2 → i.val ≠ 3 → (i.val < WT + 1 ∨ WT + 15 + L.Tu ≤ i.val) →
      B3 i = B i := by
    intro i a b c d
    rw [o3 i c (by omega), o2 i b (by omega), o1 i a (by omega) (by omega)]
  -- 4
  have e4 : ∀ (i : Fin L.U) (x : List Bool), i.val ≠ 0 → i.val ≠ 2 → i.val ≠ 3 → i.val < WT + 1 → B i = x →
      B3 i = x := fun i x a b c d e => by rw [o123 i a b c (Or.inl d)]; exact e
  obtain ⟨B4, s4, b4ct, b4k, b4o⟩ := app_dock L.sl4 L.sl4_inj 32 (UnaryCalc.value L.Dv L.Cv n) h Q m pr
    (fun _ => 0) (fun _ => rfl) B3
    (by
      have e : L.sl3 (UnaryCalc.outputTape L.Dv) = L.ws cCT := by unfold sl3; rw [if_pos rfl]
      show B3 (L.ws cCT) = _
      rw [← e]; exact b3ct)
    (e4 (L.ws sH) _ (by rw [ws_sH]; omega) (by rw [ws_sH]; omega) (by rw [ws_sH]; omega) (by rw [ws_sH]; omega)
      (by rw [hs, hH]))
    (e4 (L.ws sQ) _ (by rw [ws_sQ]; omega) (by rw [ws_sQ]; omega) (by rw [ws_sQ]; omega) (by rw [ws_sQ]; omega)
      (by rw [hs, hQ]))
    (e4 (L.ws sM) _ (by rw [ws_sM]; omega) (by rw [ws_sM]; omega) (by rw [ws_sM]; omega) (by rw [ws_sM]; omega)
      (by rw [hs, hM]))
    (e4 (L.ws sP) _ (by rw [ws_sP]; omega) (by rw [ws_sP]; omega) (by rw [ws_sP]; omega) (by rw [ws_sP]; omega)
      (by rw [hs, hP]))
    (by
      show B3 L.xrec = []
      rw [o123 _ (by rw [xrec_val]; omega) (by rw [xrec_val]; omega) (by rw [xrec_val]; omega)
        (Or.inr (by rw [xrec_val]))]
      exact hzx _ (by rw [xrec_val]; omega))
  have o4 : ∀ i : Fin L.U, i.val ≠ 3 → i.val ≠ 5 → i.val ≠ 6 → i.val ≠ 7 → i.val ≠ 8 → i.val ≠ WT + 15 + L.Tu →
      B4 i = B3 i := fun i a b c d e f => b4o i (L.sl4_ne i a b c d e f)
  have hk : ∀ (j : Fin 6), j ≠ 0 → j ≠ 5 → B4 (L.sl4 j) = B3 (L.sl4 j) := b4k
  refine ⟨B4, Step.seq (Step.seq (Step.seq s1 s2) s3) s4, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    by_cases sC : s = cCT
    · subst sC; rw [Function.update_self]; exact b4ct
    · rw [Function.update_of_ne sC]
      by_cases sN : s = cNT
      · subst sN
        rw [Function.update_self, o4 _ (by rw [ws_cNT]; omega) (by rw [ws_cNT]; omega) (by rw [ws_cNT]; omega)
          (by rw [ws_cNT]; omega) (by rw [ws_cNT]; omega) (by rw [ws_cNT]; omega),
          o3 _ (by rw [ws_cNT]; omega) (Or.inl (by rw [ws_cNT]; omega))]
        exact b2nt
      · rw [Function.update_of_ne sN]
        have hsv := L.ws_lt s
        have vN : (L.ws s).val ≠ 2 := fun e => sN (L.ws_inj (Fin.ext (by rw [e]; rfl)))
        have vC : (L.ws s).val ≠ 3 := fun e => sC (L.ws_inj (Fin.ext (by rw [e]; rfl)))
        by_cases sI : s = cIN
        · subst sI
          rw [o4 _ (by omega) (by rw [ws_cIN]; omega) (by rw [ws_cIN]; omega) (by rw [ws_cIN]; omega)
            (by rw [ws_cIN]; omega) (by omega), o3 _ (by omega) (Or.inl (by omega)), o2 _ (by omega) (Or.inl (by omega))]
          rw [hin]; exact b1in
        · have vI : (L.ws s).val ≠ 0 := fun e => sI (L.ws_inj (Fin.ext (by rw [e]; rfl)))
          by_cases sHH : s = sH
          · subst sHH; rw [show L.ws sH = L.sl4 1 from rfl, hk 1 (by decide) (by decide)]; show B3 (L.ws sH) = _
            rw [o123 _ vI vN vC (Or.inl (by omega)), hs]
          · by_cases sQQ : s = sQ
            · subst sQQ; rw [show L.ws sQ = L.sl4 2 from rfl, hk 2 (by decide) (by decide)]; show B3 (L.ws sQ) = _
              rw [o123 _ vI vN vC (Or.inl (by omega)), hs]
            · by_cases sMM : s = sM
              · subst sMM; rw [show L.ws sM = L.sl4 3 from rfl, hk 3 (by decide) (by decide)]; show B3 (L.ws sM) = _
                rw [o123 _ vI vN vC (Or.inl (by omega)), hs]
              · by_cases sPP : s = sP
                · subst sPP; rw [show L.ws sP = L.sl4 4 from rfl, hk 4 (by decide) (by decide)]; show B3 (L.ws sP) = _
                  rw [o123 _ vI vN vC (Or.inl (by omega)), hs]
                · have v5 : (L.ws s).val ≠ 5 := fun e => sHH (L.ws_inj (Fin.ext (by rw [e]; rfl)))
                  have v6 : (L.ws s).val ≠ 6 := fun e => sQQ (L.ws_inj (Fin.ext (by rw [e]; rfl)))
                  have v7 : (L.ws s).val ≠ 7 := fun e => sMM (L.ws_inj (Fin.ext (by rw [e]; rfl)))
                  have v8 : (L.ws s).val ≠ 8 := fun e => sPP (L.ws_inj (Fin.ext (by rw [e]; rfl)))
                  rw [o4 _ vC v5 v6 v7 v8 (by omega), o123 _ vI vN vC (Or.inl (by omega)), hs]
  · rw [o4 _ (by rw [wc_val]; omega) (by rw [wc_val]; omega) (by rw [wc_val]; omega) (by rw [wc_val]; omega)
      (by rw [wc_val]; omega) (by rw [wc_val]; omega), o123 _ (by rw [wc_val]; omega) (by rw [wc_val]; omega)
      (by rw [wc_val]; omega) (Or.inl (by rw [wc_val]; omega)), hc]
  · intro r
    have := r.isLt
    have hCR : CR = 40 := rfl
    have hCN : CN = 22 := rfl
    rw [o4 _ (by rw [wr_val]; omega) (by rw [wr_val]; omega) (by rw [wr_val]; omega) (by rw [wr_val]; omega)
      (by rw [wr_val]; omega) (by rw [wr_val]; omega), o123 _ (by rw [wr_val]; omega) (by rw [wr_val]; omega)
      (by rw [wr_val]; omega) (Or.inl (by rw [wr_val]; omega)), hr]
  · have hv : L.wrec.val = WT := rfl
    rw [o4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      o123 _ (by omega) (by omega) (by omega) (Or.inl (by omega)), hrc]
  · intro x hx
    rw [oG1_val] at hx
    rw [o4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      o123 _ (by omega) (by omega) (by omega) (Or.inr (by omega))]
    exact hzx x (by omega)

end Lay

end NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
