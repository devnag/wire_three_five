import Proof.Wire_3_5.FinalPass.RadBW4
import Proof.Wire_3_5.UnionMachine.RadSpec3

/-! # RADIX stage 5b, part 5: the fields read in place (`RadSpec3.RadBlockW3`)

The RADIX setup calls the block writer once per digit on a fixed stream layout whose tapes never shrink, so the table
word and the digit's indices are read IN PLACE: `(st T).drop (sh T) = lw ++ restT`,
`(st GS).drop (sh GS) = gisWord gis ++ restG`, any heads. The programs are unchanged (`phB`, `phP`): they read
their words from the heads on and rewind by counted loops (`WM.rewind` by `|gisWord| − 1`, `|lw|`), so each head
returns to its own start.

* `read_drop`; **`phB3_spec`**, **`phP3_spec`** (`phB_spec`, `phP_spec` with the in-place hypotheses).

Paper quantity of the main types: the RADIX row's factor block's fields (row:radix, P3:2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.RadB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW NearCubicWires.WireExponent3_5.UnionMachine.RadSpec

variable {ns nr : ℕ} (cap : ℕ)

theorem read_drop (l w rest : List Bool) (h : ℕ) (hd : l.drop h = w ++ rest) (i : ℕ) (hi : i < w.length) :
    readTapeBit l (h + i) = w.getD i false := by
  unfold readTapeBit
  have e : l.getD (h + i) false = (l.drop h).getD i false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [e, hd, List.getD_append _ _ _ _ hi]

theorem phB3_spec (O GS : Fin (ns + 1)) (hOG : O ≠ GS) (Rg : Fin 64 ↪ Fin nr) (τ : WState ns nr) (gis : List ℕ)
    (G row Mg : ℕ) (restG : List Bool) (hGd : (τ.st GS).drop (τ.sh GS) = gisWord gis ++ restG)
    (h1 : τ.val (Rg 1) = G)
    (h2 : τ.val (Rg 2) = row) (h9 : τ.val (Rg 9) = 0) (h11 : τ.val (Rg 11) = 0) (h14 : τ.val (Rg 14) = 0)
    (h15 : τ.val (Rg 15) = 0) (h17 : τ.val (Rg 17) = 0) (h18 : τ.val (Rg 18) = 0) (h19 : τ.val (Rg 19) = 0)
    (h20 : τ.val (Rg 20) = 0) (h21 : τ.val (Rg 21) = 0) (h37 : τ.val (Rg 37) = 0) (ho : τ.sh O = (τ.st O).length)
    (hMg : ∀ gi ∈ gis, gi ≤ Mg) (hMc : Mg + 1 ≤ cap) (hgw : (gisWord gis).length ≤ cap) (hrow : 5 * row ≤ cap)
    (hcap : τ.val (Rg 7) + ((gLabs (4 * row) G gis).flatMap labE).length + 4 * (4 * (Mg + (4 * row + 4) * G) + 4) +
      (5 + labAdd (gLabs (4 * row) G gis)) + 4 * (2 * (Mg + (4 * row + 4) * G) + 10) + 7 * (Mg + (4 * row + 4) * G) +
      4 * row + G + 20 ≤ cap)
    (hB : τ.val (Rg 7) + (pieceB (gLabs (4 * row) G gis) (labSum (gLabs (4 * row) G gis))).length ≤ cap) :
    ∃ n, WExec cap (phB O GS Rg) τ
      (appendO τ O (Rg 7) (pieceB (gLabs (4 * row) G gis) (labSum (gLabs (4 * row) G gis)))) n ∧
      n ≤ gis.length * gisB (4 * row) G Mg + 40 * labSum (gLabs (4 * row) G gis) + 90 * row +
        5 * (gisWord gis).length + 200 := by
  have hR : ∀ i j : Fin 64, Rg i = Rg j ↔ i = j := fun i j => Rg.injective.eq_iff
  have hne : ∀ {i j : Fin 64}, i ≠ j → Rg i ≠ Rg j := fun h => Rg.injective.ne h
  have hBl : (pieceB (gLabs (4 * row) G gis) (labSum (gLabs (4 * row) G gis))).length =
      ((gLabs (4 * row) G gis).flatMap labE).length + 6 + 4 * labSum (gLabs (4 * row) G gis) + 4 := by
    unfold pieceB
    simp only [List.length_append, PrimAsm.FiltRecW.reps_length, m2, List.length_cons, List.length_nil]
    ring
  rw [hBl] at hB
  have b1 := add4_spec cap (Rg 2) (Rg 11) (Rg 9) (hne (by decide)) (hne (by decide)) (hne (by decide)) τ h9
    (by omega) (by omega)
  rw [h11, h2, Nat.zero_add] at b1
  have b2 := incN_spec cap (Rg 20) 5 (τ.setv (Rg 11) (4 * row))
    (by rw [wsetv_val_ne _ _ (hne (by decide)), h20]; omega)
  rw [wsetv_val_ne _ _ (hne (by decide)), h20, Nat.zero_add] at b2
  obtain ⟨τ2, hτ2⟩ : ∃ x, x = (τ.setv (Rg 11) (4 * row)).setv (Rg 20) 5 := ⟨_, rfl⟩
  rw [← hτ2] at b2
  have v2 : ∀ j : Fin 64, j ≠ 11 → j ≠ 20 → τ2.val (Rg j) = τ.val (Rg j) := by
    intro j a b; rw [hτ2]; simp [Function.update_apply, hR, a, b]
  have e3a : τ2.sh GS = τ.sh GS := by rw [hτ2]; simp
  have e3b : τ2.val (Rg 37) = 0 := by rw [v2 37 (by decide) (by decide), h37]
  have ho2 : τ2.sh O = (τ2.st O).length := by rw [hτ2]; simpa using ho
  have b3 := gisLoop_spec cap O GS hOG Rg (4 * row) G Mg gis τ2 5
    (fun i hi => by rw [hτ2]; simp only [WState.setv_st, WState.setv_sh]; exact read_drop _ _ _ _ hGd i hi)
    (by rw [hτ2]; simp [hR]) (by rw [v2 1 (by decide) (by decide), h1])
    (by rw [v2 15 (by decide) (by decide), h15]) (by rw [v2 14 (by decide) (by decide), h14])
    (by rw [v2 17 (by decide) (by decide), h17]) (by rw [v2 18 (by decide) (by decide), h18])
    (by rw [v2 19 (by decide) (by decide), h19]) (by rw [v2 21 (by decide) (by decide), h21])
    (by rw [hτ2]; simp) ho2 hMg hMc (by rw [e3b]; omega) (by rw [v2 7 (by decide) (by decide)]; exact hcap)
  rw [e3a, e3b, Nat.zero_add] at b3
  have hgw1 : 1 ≤ (gisWord gis).length := by unfold gisWord; simp
  obtain ⟨hh, hhh⟩ : ∃ x, x = (gisWord gis).length - 1 := ⟨_, rfl⟩
  rw [show τ.sh GS + (gisWord gis).length - 1 = τ.sh GS + hh by omega, ← hhh] at b3
  have v7 : τ2.val (Rg 7) = τ.val (Rg 7) := v2 7 (by decide) (by decide)
  have b4 := emitW_spec cap O (Rg 7) (m2 false ++ [true, false])
    (gS O GS Rg τ2 ((gLabs (4 * row) G gis).flatMap labE) (5 + labAdd (gLabs (4 * row) G gis)) (τ.sh GS + hh) hh)
    (gS_ho hOG τ2 ho2 _ _ _ _)
    (by rw [gS_val7, v7]; simp only [m2, List.length_append, List.length_cons, List.length_nil]; omega)
  rw [gS_append hOG] at b4
  have b5 := repW_spec cap O (Rg 7) (Rg 20) (hne (by decide)) (m2 false) (labSum (gLabs (4 * row) G gis))
    (gS O GS Rg τ2 ((gLabs (4 * row) G gis).flatMap labE ++ (m2 false ++ [true, false]))
      (5 + labAdd (gLabs (4 * row) G gis)) (τ.sh GS + hh) hh)
    (by rw [gS_val20]; rfl) (gS_ho hOG τ2 ho2 _ _ _ _)
    (by rw [gS_val7, v7]; simp only [m2, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [gS_append hOG, gS_setv20] at b5
  have b6 := emitW_spec cap O (Rg 7) ([true, false] ++ [true, false])
    (gS O GS Rg τ2 ((gLabs (4 * row) G gis).flatMap labE ++ (m2 false ++ [true, false]) ++
      reps (labSum (gLabs (4 * row) G gis)) (m2 false)) 0 (τ.sh GS + hh) hh)
    (gS_ho hOG τ2 ho2 _ _ _ _)
    (by
      rw [gS_val7, v7]
      simp only [m2, List.length_append, List.length_cons, List.length_nil, PrimAsm.FiltRecW.reps_length]
      omega)
  rw [gS_append hOG] at b6
  obtain ⟨U, hU⟩ : ∃ x, x = (gLabs (4 * row) G gis).flatMap labE ++ (m2 false ++ [true, false]) ++
      reps (labSum (gLabs (4 * row) G gis)) (m2 false) ++ ([true, false] ++ [true, false]) := ⟨_, rfl⟩
  rw [← hU] at b6
  have b7 := wrewind_spec cap GS (Rg 37) hh (gS O GS Rg τ2 U 0 (τ.sh GS + hh) hh) (by rw [gS_val37])
    (by rw [gS_val37]; omega)
  have b8 := wclear_spec cap (Rg 11) (4 * row)
    (((gS O GS Rg τ2 U 0 (τ.sh GS + hh) hh).setv (Rg 37) 0).seth GS ((gS O GS Rg τ2 U 0 (τ.sh GS + hh) hh).sh GS - hh))
    (by rw [WState.seth_val, wsetv_val_ne _ _ (hne (by decide)), gS_val, hτ2]; simp [hR])
    (by rw [WState.seth_val, wsetv_val_ne _ _ (hne (by decide)), gS_val, hτ2]; simp [hR]; try omega)
  have hUe : U = pieceB (gLabs (4 * row) G gis) (labSum (gLabs (4 * row) G gis)) := by rw [hU]; rfl
  have efin : ((((gS O GS Rg τ2 U 0 (τ.sh GS + hh) hh).setv (Rg 37) 0).seth GS ((gS O GS Rg τ2 U 0 (τ.sh GS + hh) hh).sh GS - hh)).setv
      (Rg 11) 0) = appendO τ O (Rg 7) U := by
    rw [hτ2]
    apply WState.eq
    · funext j
      simp only [WState.setv_sh, WState.seth_sh, gS_sh, appendO_sh]
      by_cases hjG : j = GS
      · subst hjG; simp [Function.update_apply, Ne.symm hOG]
      · by_cases hjO : j = O
        · subst hjO; simp [Function.update_apply, hjG]
        · simp [Function.update_apply, hjG, hjO]
    · simp [gS_st]
    · funext j
      simp only [WState.setv_val, WState.seth_val, appendO_val, gS_val, Function.update_apply]
      by_cases a11 : j = Rg 11 <;> by_cases a37 : j = Rg 37 <;> by_cases a20 : j = Rg 20 <;>
        by_cases a7 : j = Rg 7 <;> simp_all [hR]
    · simp [gS_cell]
  rw [efin] at b8
  refine ⟨_, WExec.cast cap (WExec.seq b1 (WExec.seq b2 (WExec.seq b3 (WExec.seq b4 (WExec.seq b5 (WExec.seq b6
    (WExec.seq b7 b8))))))) (by rw [hUe]) le_rfl, ?_⟩
  simp only [m2, List.length_append, List.length_cons, List.length_nil]
  omega

theorem phP3_spec (O T : Fin (ns + 1)) (hOT : O ≠ T) (Rg : Fin 64 ↪ Fin nr) (τ : WState ns nr) (lw : List Bool)
    (L t c : ℕ) (sgn : Bool) (restT : List Bool) (hTd : (τ.st T).drop (τ.sh T) = lw ++ restT)
    (h0 : τ.val (Rg 0) = L)
    (h3 : τ.val (Rg 3) = t) (h4 : τ.val (Rg 4) = if sgn then 1 else 0) (h6 : τ.val (Rg 6) = c)
    (hc : c = 4 * (lw.length + L + 1)) (h38 : τ.val (Rg 38) = 0) (h39 : τ.val (Rg 39) = 0)
    (h40 : τ.val (Rg 40) = 0) (h41 : τ.val (Rg 41) = 0) (h42 : τ.val (Rg 42) = 0) (h51 : τ.val (Rg 51) = 0)
    (h61 : τ.val (Rg 61) = 0) (h62 : τ.val (Rg 62) = 0) (ho : τ.sh O = (τ.st O).length) (hcc : c + 1 ≤ cap)
    (htc : t ≤ cap) (hP : τ.val (Rg 7) + (PrimAsm.PopRec.pieceP (lw.flatMap m2) t sgn c false).length ≤ cap) :
    ∃ n, WExec cap (phP O T Rg) τ (appendO τ O (Rg 7) (PrimAsm.PopRec.pieceP (lw.flatMap m2) t sgn c false)) n ∧
      n ≤ 1000 * (lw.length + L + t + c + 10) := by
  have hR : ∀ i j : Fin 64, Rg i = Rg j ↔ i = j := fun i j => Rg.injective.eq_iff
  have hne : ∀ {i j : Fin 64}, i ≠ j → Rg i ≠ Rg j := fun h => Rg.injective.ne h
  have hpl := PrimAsm.PopBlockW.pieceP_length (lw.flatMap m2) t sgn c false
  rw [hpl, flatMap_m2_length] at hP
  have hX0 : (xR Rg) 0 = Rg 7 := rfl
  have hX51 : (xR Rg) 51 = Rg 51 := rfl
  have hX61 : (xR Rg) 61 = Rg 61 := rfl
  have hX62 : (xR Rg) 62 = Rg 62 := rfl
  -- the table word's length
  obtain ⟨n1, p1, bd1⟩ := kComp_spec cap Rg τ lw.length L h0 (by rw [h6, hc]) h38 h39 h40 h42 (by omega)
  -- the table word
  have p2 := copyLoop_spec cap O T hOT (Rg 7) (Rg 41) (Rg 40) (hne (by decide)) (hne (by decide))
    (hne (by decide)) lw (τ.setv (Rg 40) lw.length) (by simp)
    (fun i hi => by simp only [WState.setv_st, WState.setv_sh]; exact read_drop _ _ _ _ hTd i hi)
    (by simpa using ho) (by rw [wsetv_val_ne _ _ (hne (by decide))]; omega)
    (by rw [wsetv_val_ne _ _ (hne (by decide)), h41]; omega) (by omega)
  obtain ⟨σ2, hσ2⟩ : ∃ x, x = ((((appendO (τ.setv (Rg 40) lw.length) O (Rg 7) (lw.flatMap m2)).seth T
      ((τ.setv (Rg 40) lw.length).sh T + lw.length)).setv (Rg 41)
      ((τ.setv (Rg 40) lw.length).val (Rg 41) + lw.length)).setv (Rg 40) 0) := ⟨_, rfl⟩
  rw [← hσ2] at p2
  have p3 := wrewind_spec cap T (Rg 41) lw.length σ2
    (by rw [hσ2]; simp [Function.update_apply, hR, h41]) (by rw [hσ2]; simp [Function.update_apply, hR, h41]; omega)
  have e3 : (σ2.setv (Rg 41) 0).seth T (σ2.sh T - lw.length) = appendO τ O (Rg 7) (lw.flatMap m2) := by
    rw [hσ2]
    apply WState.eq
    · funext j
      simp only [WState.setv_sh, WState.seth_sh, appendO_sh]
      by_cases hjT : j = T
      · subst hjT; simp [Function.update_apply, Ne.symm hOT]
      · by_cases hjO : j = O
        · subst hjO; simp [Function.update_apply, hjT]
        · simp [Function.update_apply, hjT, hjO]
    · simp
    · funext j
      simp only [WState.setv_val, WState.seth_val, appendO_val, Function.update_apply]
      by_cases a41 : j = Rg 41 <;> by_cases a40 : j = Rg 40 <;> by_cases a7 : j = Rg 7 <;> simp_all [hR]
    · simp
  rw [e3] at p3
  -- `[1,0]`, `unary t`, its end
  have p4 := emitW_spec cap O (Rg 7) [true, false] (appendO τ O (Rg 7) (lw.flatMap m2)) (aO_ho τ ho _)
    (by rw [aO_val_self, flatMap_m2_length]; simp; omega)
  rw [appendO_append] at p4
  have p5 := repRegW_spec cap O (Rg 7) (Rg 3) (Rg 38) (Rg 39) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (m2 true) (appendO τ O (Rg 7) (lw.flatMap m2 ++ [true, false]))
    (by rw [aO_val_ne _ _ (hne (by decide)), h38]) (by rw [aO_val_ne _ _ (hne (by decide)), h39]) (aO_ho τ ho _)
    (by rw [aO_val_ne _ _ (hne (by decide)), h3]; exact htc)
    (by
      rw [aO_val_self, aO_val_ne _ _ (r := Rg 3) (hne (by decide)), h3]
      simp only [flatMap_m2_length, m2, List.length_append, List.length_cons, List.length_nil]
      omega)
  rw [aO_val_ne _ _ (r := Rg 3) (hne (by decide)), h3, appendO_append] at p5
  have p6 := emitW_spec cap O (Rg 7) (m2 false ++ [true, false])
    (appendO τ O (Rg 7) (lw.flatMap m2 ++ [true, false] ++ reps t (m2 true))) (aO_ho τ ho _)
    (by rw [aO_val_self]; simp [flatMap_m2_length, m2, PrimAsm.FiltRecW.reps_length]; omega)
  rw [appendO_append] at p6
  obtain ⟨u6, hu6⟩ : ∃ x, x = lw.flatMap m2 ++ [true, false] ++ reps t (m2 true) ++ (m2 false ++ [true, false]) :=
    ⟨_, rfl⟩
  have hl6 : u6.length = 4 * lw.length + 2 + (4 * t + 6) := by
    rw [hu6]; simp [flatMap_m2_length, m2, PrimAsm.FiltRecW.reps_length]; ring
  rw [← hu6] at p6
  -- `51 := c + 1`
  have p7 := FinalPass.Hash4.wcopyR_spec cap (Rg 6) (Rg 51) (Rg 42) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (appendO τ O (Rg 7) u6) (by rw [aO_val_ne _ _ (hne (by decide)), h51])
    (by rw [aO_val_ne _ _ (hne (by decide)), h42]) (by rw [aO_val_ne _ _ (hne (by decide)), h6]; omega)
  rw [aO_val_ne _ _ (hne (by decide)), h6] at p7
  obtain ⟨τc, hτc⟩ : ∃ x, x = τ.setv (Rg 51) (c + 1) := ⟨_, rfl⟩
  have p8 : WExec cap (.inc (Rg 51)) ((appendO τ O (Rg 7) u6).setv (Rg 51) c) (appendO τc O (Rg 7) u6) 3 :=
    WExec.cast cap (inc_to cap (Rg 51) ((appendO τ O (Rg 7) u6).setv (Rg 51) c) c (by simp) (by omega))
      (by rw [wsetv_setv, hτc, appendO_setv _ O (Rg 7) (Rg 51) (hne (by decide))]) le_rfl
  have hoc : τc.sh O = (τc.st O).length := by rw [hτc]; simpa using ho
  have vc : ∀ j : Fin 64, j ≠ 51 → τc.val (Rg j) = τ.val (Rg j) := by
    intro j a; rw [hτc, wsetv_val_ne _ _ (hne a)]
  have vc7 : τc.val (Rg 7) = τ.val (Rg 7) := vc 7 (by decide)
  -- the scratch field
  have p9 := PrimAsm.PopBlockW.zf_spec cap O (xR Rg) (appendO τc O (Rg 7) u6) (c + 1)
    (by rw [hX51, aO_val_ne _ _ (hne (by decide)), hτc, wsetv_val_self])
    (by rw [hX61, aO_val_ne _ _ (hne (by decide)), vc 61 (by decide), h61])
    (by rw [hX62, aO_val_ne _ _ (hne (by decide)), vc 62 (by decide), h62]) (aO_ho τc hoc _) hcc
    (by rw [hX0, aO_val_self, vc7, hl6]; omega)
  rw [hX0, appendO_append] at p9
  -- the sign
  have p10 : WExec cap (.ifr (Rg 4) (emitW O (Rg 7) (m2 true ++ [true, false]))
      (emitW O (Rg 7) (m2 false ++ [true, false])))
      (appendO τc O (Rg 7) (u6 ++ (reps (c + 1) (m2 false) ++ [true, false])))
      (appendO τc O (Rg 7) (u6 ++ (reps (c + 1) (m2 false) ++ [true, false]) ++ (m2 sgn ++ [true, false])))
      (8 * 6 + 1) := by
    have hcap6 : (appendO τc O (Rg 7) (u6 ++ (reps (c + 1) (m2 false) ++ [true, false]))).val (Rg 7) +
        (m2 sgn ++ [true, false]).length ≤ cap := by
      rw [aO_val_self, vc7]; simp only [List.length_append, hl6, PrimAsm.FiltRecW.reps_length, m2, List.length_cons,
        List.length_nil]; omega
    have h4c : (appendO τc O (Rg 7) (u6 ++ (reps (c + 1) (m2 false) ++ [true, false]))).val (Rg 4) =
        if sgn then 1 else 0 := by rw [aO_val_ne _ _ (hne (by decide)), vc 4 (by decide), h4]
    cases sgn
    · have e := emitW_spec cap O (Rg 7) (m2 false ++ [true, false]) _ (aO_ho τc hoc _) hcap6
      rw [appendO_append] at e
      exact WExec.ifrF (by rw [h4c]; rfl) e
    · have e := emitW_spec cap O (Rg 7) (m2 true ++ [true, false]) _ (aO_ho τc hoc _) hcap6
      rw [appendO_append] at e
      exact WExec.ifrT (by rw [h4c]; decide) e
  obtain ⟨u10, hu10⟩ : ∃ x, x = u6 ++ (reps (c + 1) (m2 false) ++ [true, false]) ++ (m2 sgn ++ [true, false]) :=
    ⟨_, rfl⟩
  have hl10 : u10.length = 4 * lw.length + 2 + (4 * t + 6) + (4 * (c + 1) + 2) + 6 := by
    rw [hu10]; simp only [List.length_append, hl6, PrimAsm.FiltRecW.reps_length, m2, List.length_cons, List.length_nil]
    omega
  rw [← hu10] at p10
  -- 15 registers
  have p11 := PrimAsm.PopBlockW.zerosN_spec cap O (xR Rg) (c + 1) 15 (appendO τc O (Rg 7) u10)
    (by rw [hX51, aO_val_ne _ _ (hne (by decide)), hτc, wsetv_val_self])
    (by rw [hX61, aO_val_ne _ _ (hne (by decide)), vc 61 (by decide), h61])
    (by rw [hX62, aO_val_ne _ _ (hne (by decide)), vc 62 (by decide), h62]) (aO_ho τc hoc _) hcc
    (by rw [hX0, aO_val_self, vc7, hl10]; omega)
  rw [hX0, appendO_append] at p11
  -- the flag
  have p12 := emitW_spec cap O (Rg 7) (m2 false ++ [true, false])
    (appendO τc O (Rg 7) (u10 ++ reps 15 (reps (c + 1) (m2 false) ++ [true, false]))) (aO_ho τc hoc _)
    (by
      rw [aO_val_self, vc7]
      simp only [List.length_append, hl10, PrimAsm.FiltRecW.reps_length, m2, List.length_cons, List.length_nil]
      omega)
  rw [appendO_append] at p12
  have p13 := wclear_spec cap (Rg 51) (c + 1)
    (appendO τc O (Rg 7) (u10 ++ reps 15 (reps (c + 1) (m2 false) ++ [true, false]) ++
      (m2 false ++ [true, false])))
    (by rw [aO_val_ne _ _ (hne (by decide)), hτc, wsetv_val_self])
    (by rw [aO_val_ne _ _ (hne (by decide)), hτc, wsetv_val_self]; exact hcc)
  rw [← appendO_setv _ O (Rg 7) (Rg 51) (hne (by decide)), hτc, wsetv_setv, setv_eq_self τ (Rg 51) 0 h51] at p13
  have hfin : u10 ++ reps 15 (reps (c + 1) (m2 false) ++ [true, false]) ++ (m2 false ++ [true, false]) =
      PrimAsm.PopRec.pieceP (lw.flatMap m2) t sgn c false := by
    rw [hu10, hu6]; simp only [PrimAsm.PopRec.pieceP, List.append_assoc]
  rw [hτc] at p8 p9 p10 p11 p12
  refine ⟨_, WExec.cast cap (WExec.seq p1 (WExec.seq p2 (WExec.seq p3 (WExec.seq p4 (WExec.seq p5 (WExec.seq p6
    (WExec.seq p7 (WExec.seq p8 (WExec.seq p9 (WExec.seq p10 (WExec.seq p11 (WExec.seq p12 p13))))))))))))
    (by rw [hfin]) le_rfl, ?_⟩
  simp only [m2, List.length_append, List.length_cons, List.length_nil]
  omega

end NearCubicWires.WireExponent3_5.FinalPass.RadB
