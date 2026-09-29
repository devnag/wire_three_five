import Proof.Wire_3_5.FinalPass.RadBW1

/-! # RADIX stage 5b, part 2: the labels of one digit's occurrences (row:radix, P3:2585-2623)

The block's label fields `pieceB (labsOf G row gis) (labSum …)`: the labels of the digit's occurrences, read one
index at a time from the indices' stream `GS` (`gisWord gis`, heads `0`), four labels per occurrence by PA's
`Emit.gateBody`, the label log's field, the empty field.

* `gisLoop`/**`gisLoop_spec`**: the loop over the indices (`whs GS`), by induction on the indices;
* `phB`/**`phB_spec`**: `pieceB (labsOf G row gis) (labSum (labsOf G row gis))`, the stream `GS` and the scratch
  registers restored.

Paper quantity of the main types: the RADIX row's factor block's label fields (row:radix, P3:2598-2599). -/

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

/-! ## The indices' word -/

/-- One index's word `1 1^gi 0`. -/
def gw (gi : ℕ) : List Bool := true :: (List.replicate gi true ++ [false])

theorem gw_length (gi : ℕ) : (gw gi).length = gi + 2 := by simp [gw]

theorem gisWord_nil : gisWord [] = [false] := rfl

theorem gisWord_cons (gi : ℕ) (gis : List ℕ) : gisWord (gi :: gis) = gw gi ++ gisWord gis := by
  simp [gisWord, gw]

theorem gw_getD_ones (gi : ℕ) (rest : List Bool) (k : ℕ) (hk : k < gi) :
    (gw gi ++ rest).getD (1 + k) false = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [gw_length]; omega)]
  simp [gw, List.getElem?_append_left (show k < (List.replicate gi true).length by simp; omega), hk,
    show 1 + k = k + 1 by omega]

theorem gw_getD_end (gi : ℕ) (rest : List Bool) : (gw gi ++ rest).getD (1 + gi) false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [gw_length]; omega)]
  simp [gw, show 1 + gi = gi + 1 by omega]

theorem gw_getD_rest (gi : ℕ) (rest : List Bool) (i : ℕ) :
    (gw gi ++ rest).getD (gi + 2 + i) false = rest.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [gw_length]; omega), gw_length,
    List.getD_eq_getElem?_getD, show gi + 2 + i - (gi + 2) = i by omega]

/-! ## The labels -/

/-- The labels of the occurrences `gis` at row offset `r4`. -/
def gLabs (r4 G : ℕ) (gis : List ℕ) : List ℕ := gis.flatMap (gateLabs r4 G)

theorem labsOf_eq (G row : ℕ) (gis : List ℕ) : CompilerMachine.Pool.labsOf G row gis = gLabs (4 * row) G gis := by
  unfold CompilerMachine.Pool.labsOf gLabs gateLabs CompilerMachine.Pool.poolIndex
  congr 1; funext gi; congr 1; funext k; ring

theorem labAdd_append (a b : List ℕ) : labAdd (a ++ b) = labAdd a + labAdd b := by
  simp [labAdd, List.map_append, List.sum_append]

theorem gLabs_cons (r4 G gi : ℕ) (gis : List ℕ) : gLabs r4 G (gi :: gis) = gateLabs r4 G gi ++ gLabs r4 G gis := by
  simp [gLabs]

/-! ## The loop's state -/

section GS
variable (O GS : Fin (ns + 1)) (Rg : Fin 64 ↪ Fin nr)

/-- The loop's state: the output extended by `u` (counter `7`), the label log `20 = c`, the indices' head `h`, its
counter `37 = p`. -/
def gS (σ : WState ns nr) (u : List Bool) (c h p : ℕ) : WState ns nr :=
  (((appendO σ O (Rg 7) u).setv (Rg 20) c).seth GS h).setv (Rg 37) p

variable {O GS Rg}

theorem gS_val (σ : WState ns nr) (u : List Bool) (c h p : ℕ) (j : Fin nr) :
    (gS O GS Rg σ u c h p).val j = if j = Rg 37 then p else if j = Rg 20 then c else if j = Rg 7 then
      σ.val (Rg 7) + u.length else σ.val j := by
  simp only [gS, WState.setv_val, WState.seth_val, appendO_val, Function.update_apply]

theorem gS_sh (σ : WState ns nr) (u : List Bool) (c h p : ℕ) :
    (gS O GS Rg σ u c h p).sh = Function.update (Function.update σ.sh O (σ.sh O + u.length)) GS h := by
  simp [gS]

theorem gS_st (σ : WState ns nr) (u : List Bool) (c h p : ℕ) :
    (gS O GS Rg σ u c h p).st = Function.update σ.st O (σ.st O ++ u) := by
  simp [gS]

theorem gS_cell (σ : WState ns nr) (u : List Bool) (c h p : ℕ) : (gS O GS Rg σ u c h p).cell = σ.cell := by
  simp [gS]

theorem gS_gS (hOG : O ≠ GS) (σ : WState ns nr) (u u' : List Bool) (c h p c' h' p' : ℕ) :
    gS O GS Rg (gS O GS Rg σ u c h p) u' c' h' p' = gS O GS Rg σ (u ++ u') c' h' p' := by
  have hR : ∀ i j : Fin 64, Rg i = Rg j ↔ i = j := fun i j => Rg.injective.eq_iff
  apply WState.eq
  · funext j
    rw [gS_sh, gS_sh, gS_sh]
    by_cases hjG : j = GS
    · subst hjG; simp
    · by_cases hjO : j = O
      · subst hjO; simp [Function.update_apply, hjG, hOG]; omega
      · simp [Function.update_apply, hjG, hjO]
  · funext j
    rw [gS_st, gS_st, gS_st]
    by_cases hjO : j = O
    · subst hjO; simp
    · simp [Function.update_apply, hjO]
  · funext j
    simp only [gS_val]
    by_cases a37 : j = Rg 37 <;> by_cases a20 : j = Rg 20 <;> by_cases a7 : j = Rg 7 <;>
      simp_all [hR] <;> omega
  · rw [gS_cell, gS_cell, gS_cell]

theorem gS_append (hOG : O ≠ GS) (σ : WState ns nr) (u v : List Bool) (c h p : ℕ) :
    appendO (gS O GS Rg σ u c h p) O (Rg 7) v = gS O GS Rg σ (u ++ v) c h p := by
  have hR : ∀ i j : Fin 64, Rg i = Rg j ↔ i = j := fun i j => Rg.injective.eq_iff
  apply WState.eq
  · funext j
    rw [appendO_sh, gS_sh, gS_sh]
    by_cases hjG : j = GS
    · subst hjG; simp [Function.update_apply, Ne.symm hOG]
    · by_cases hjO : j = O
      · subst hjO; simp [Function.update_apply, hjG]; omega
      · simp [Function.update_apply, hjG, hjO]
  · funext j
    rw [appendO_st, gS_st, gS_st]
    by_cases hjO : j = O
    · subst hjO; simp
    · simp [Function.update_apply, hjO]
  · funext j
    rw [appendO_val, gS_val, gS_val]
    by_cases hj7 : j = Rg 7
    · subst hj7; simp [Function.update_apply, hR]; omega
    · rw [Function.update_of_ne hj7, gS_val]
      split_ifs <;> simp_all [hR]
  · rw [appendO_cell, gS_cell, gS_cell]

theorem gS_setv20 (σ : WState ns nr) (u : List Bool) (c h p c' : ℕ) :
    (gS O GS Rg σ u c h p).setv (Rg 20) c' = gS O GS Rg σ u c' h p := by
  have hR : ∀ i j : Fin 64, Rg i = Rg j ↔ i = j := fun i j => Rg.injective.eq_iff
  refine WState.eq rfl rfl ?_ rfl
  funext j
  simp only [WState.setv_val, Function.update_apply, gS_val]
  by_cases a37 : j = Rg 37 <;> by_cases a20 : j = Rg 20 <;> simp_all [hR]

theorem gS_nil (σ : WState ns nr) : gS O GS Rg σ [] (σ.val (Rg 20)) (σ.sh GS) (σ.val (Rg 37)) = σ := by
  apply WState.eq
  · funext j
    rw [gS_sh]
    by_cases hjG : j = GS
    · subst hjG; simp
    · by_cases hjO : j = O
      · subst hjO; simp [Function.update_apply, hjG]
      · simp [Function.update_apply, hjG, hjO]
  · funext j
    rw [gS_st]
    by_cases hjO : j = O
    · subst hjO; simp
    · simp [Function.update_apply, hjO]
  · funext j
    rw [gS_val]
    split_ifs <;> simp_all
  · rw [gS_cell]

end GS

/-! ## The loop -/

/-- One index: past its marker, `15 := gi` (counter `37`), the gate's four labels, `15 := 0`. -/
def gisBody (O GS : Fin (ns + 1)) (Rg : Fin 64 ↪ Fin nr) : WM ns nr :=
  .seq (WM.fwdC GS (Rg 37)) (.seq (WM.readU GS (Rg 37) (Rg 15)) (.seq (gateBody O (fL.trans Rg)) (WM.clear (Rg 15))))

/-- The loop over the indices (until the closing `0`). -/
def gisLoop (O GS : Fin (ns + 1)) (Rg : Fin 64 ↪ Fin nr) : WM ns nr := .whs GS (gisBody O GS Rg)

/-- One round's cost at indices below `Mg`. -/
def gisB (r4 G Mg : ℕ) : ℕ := 14 * Mg + 21 + gateCost r4 G Mg

theorem gisLoop_spec (O GS : Fin (ns + 1)) (hOG : O ≠ GS) (Rg : Fin 64 ↪ Fin nr) (r4 G Mg : ℕ) :
    ∀ (rest : List ℕ) (σ : WState ns nr) (c : ℕ),
    (∀ i < (gisWord rest).length, readTapeBit (σ.st GS) (σ.sh GS + i) = (gisWord rest).getD i false) →
    σ.val (Rg 11) = r4 → σ.val (Rg 1) = G → σ.val (Rg 15) = 0 → σ.val (Rg 14) = 0 → σ.val (Rg 17) = 0 →
    σ.val (Rg 18) = 0 → σ.val (Rg 19) = 0 → σ.val (Rg 21) = 0 → σ.val (Rg 20) = c →
    σ.sh O = (σ.st O).length → (∀ gi ∈ rest, gi ≤ Mg) → Mg + 1 ≤ cap →
    σ.val (Rg 37) + (gisWord rest).length ≤ cap →
    σ.val (Rg 7) + ((gLabs r4 G rest).flatMap labE).length + 4 * (4 * (Mg + (r4 + 4) * G) + 4) +
      (c + labAdd (gLabs r4 G rest)) + 4 * (2 * (Mg + (r4 + 4) * G) + 10) + 7 * (Mg + (r4 + 4) * G) + r4 + G + 20
      ≤ cap →
    WExec cap (gisLoop O GS Rg) σ
      (gS O GS Rg σ ((gLabs r4 G rest).flatMap labE) (c + labAdd (gLabs r4 G rest))
        (σ.sh GS + (gisWord rest).length - 1) (σ.val (Rg 37) + (gisWord rest).length - 1))
      (rest.length * gisB r4 G Mg + 1)
  | [], σ, c, hw, _, _, _, _, _, _, _, _, h20, _, _, _, _, _ => by
    have hb : wbit σ GS = false := by
      have := hw 0 (by simp [gisWord_nil])
      simpa [wbit, gisWord_nil] using this
    have e : gS O GS Rg σ ((gLabs r4 G []).flatMap labE) (c + labAdd (gLabs r4 G []))
        (σ.sh GS + (gisWord []).length - 1) (σ.val (Rg 37) + (gisWord []).length - 1) = σ := by
      have e1 : c + labAdd (gLabs r4 G []) = σ.val (Rg 20) := by rw [h20]; rfl
      rw [e1, gisWord_nil]
      exact gS_nil σ
    rw [e]
    exact WExec.mono (WExec.whsF hb) (by simp)
  | gi :: rest, σ, c, hw, h11, h1, h15, h14, h17, h18, h19, h21, h20, ho, hMg, hMc, h37c, hcap => by
    have hR : ∀ i j : Fin 64, Rg i = Rg j ↔ i = j := fun i j => Rg.injective.eq_iff
    have hne : ∀ {i j : Fin 64}, i ≠ j → Rg i ≠ Rg j := fun h => Rg.injective.ne h
    rw [gisWord_cons] at hw h37c
    have hgl := gw_length gi
    have hgi : gi ≤ Mg := hMg gi (by simp)
    have hb : wbit σ GS = true := by
      have := hw 0 (by simp [gw])
      simpa [wbit, gw] using this
    -- past the marker
    have s1 := wfwdC_spec cap GS (Rg 37) σ (by simp only [List.length_append] at h37c; omega)
    -- the index
    have s2 := wreadU_spec cap GS (Rg 37) (Rg 15) (hne (by decide)) gi
      ((σ.seth GS (σ.sh GS + 1)).setv (Rg 37) (σ.val (Rg 37) + 1))
      (fun k hk => by
        have := hw (1 + k) (by simp only [List.length_append]; omega)
        rw [gw_getD_ones gi _ k hk] at this
        simpa [Nat.add_assoc] using this)
      (by
        have := hw (1 + gi) (by simp only [List.length_append]; omega)
        rw [gw_getD_end] at this
        simpa [Nat.add_assoc] using this)
      (by simp only [List.length_append] at h37c; simp; omega)
      (by simp [Function.update_apply, hR, h15]; omega)
    obtain ⟨σ2, hσ2⟩ : ∃ x, x = (gS O GS Rg σ [] c (σ.sh GS + gi + 2) (σ.val (Rg 37) + gi + 2)).setv (Rg 15) gi :=
      ⟨_, rfl⟩
    have e2 : ((((σ.seth GS (σ.sh GS + 1)).setv (Rg 37) (σ.val (Rg 37) + 1)).seth GS
        (((σ.seth GS (σ.sh GS + 1)).setv (Rg 37) (σ.val (Rg 37) + 1)).sh GS + gi + 1)).setv (Rg 37)
        (((σ.seth GS (σ.sh GS + 1)).setv (Rg 37) (σ.val (Rg 37) + 1)).val (Rg 37) + gi + 1)).setv (Rg 15)
        (((σ.seth GS (σ.sh GS + 1)).setv (Rg 37) (σ.val (Rg 37) + 1)).val (Rg 15) + gi) = σ2 := by
      rw [hσ2]
      apply WState.eq
      · funext j
        simp only [WState.setv_sh, WState.seth_sh, gS_sh]
        by_cases hjG : j = GS
        · subst hjG; simp; omega
        · by_cases hjO : j = O
          · subst hjO; simp [Function.update_apply, hjG]
          · simp [Function.update_apply, hjG, hjO]
      · funext j
        simp only [WState.setv_st, WState.seth_st, gS_st]
        by_cases hjO : j = O
        · subst hjO; simp
        · simp [Function.update_apply, hjO]
      · funext j
        simp only [WState.setv_val, WState.seth_val, gS_val, Function.update_apply]
        by_cases a15 : j = Rg 15 <;> by_cases a37 : j = Rg 37 <;> by_cases a20 : j = Rg 20 <;>
          by_cases a7 : j = Rg 7 <;> simp_all [hR] <;> omega
      · simp [gS_cell]
    rw [e2] at s2
    -- the gate
    have hL0 : (fL.trans Rg) 0 = Rg 7 := rfl
    have hL1 : (fL.trans Rg) 1 = Rg 11 := rfl
    have hL2 : (fL.trans Rg) 2 = Rg 1 := rfl
    have hL5 : (fL.trans Rg) 5 = Rg 14 := rfl
    have hL6 : (fL.trans Rg) 6 = Rg 15 := rfl
    have hL8 : (fL.trans Rg) 8 = Rg 17 := rfl
    have hL9 : (fL.trans Rg) 9 = Rg 18 := rfl
    have hL10 : (fL.trans Rg) 10 = Rg 19 := rfl
    have hL11 : (fL.trans Rg) 11 = Rg 20 := rfl
    have hL12 : (fL.trans Rg) 12 = Rg 21 := rfl
    have v2 : ∀ j : Fin 64, j ≠ 15 → j ≠ 20 → j ≠ 37 → j ≠ 7 → σ2.val (Rg j) = σ.val (Rg j) := by
      intro j a b d e
      rw [hσ2, WState.setv_val, Function.update_of_ne (hne a), gS_val]
      simp [hR, b, d, e]
    have hlabs : (gLabs r4 G (gi :: rest)).flatMap labE =
        (gateLabs r4 G gi).flatMap labE ++ (gLabs r4 G rest).flatMap labE := by
      rw [gLabs_cons, List.flatMap_append]
    have hadd : labAdd (gLabs r4 G (gi :: rest)) = labAdd (gateLabs r4 G gi) + labAdd (gLabs r4 G rest) := by
      rw [gLabs_cons, labAdd_append]
    rw [hlabs, hadd] at hcap
    simp only [List.length_append] at hcap
    have s3 := gateBody_spec cap O (fL.trans Rg) σ2 r4 G gi c
      (by rw [hL1, v2 11 (by decide) (by decide) (by decide) (by decide), h11])
      (by rw [hL2, v2 1 (by decide) (by decide) (by decide) (by decide), h1])
      (by rw [hL6, hσ2]; simp)
      (by rw [hL5, v2 14 (by decide) (by decide) (by decide) (by decide), h14])
      (by rw [hL8, v2 17 (by decide) (by decide) (by decide) (by decide), h17])
      (by rw [hL9, v2 18 (by decide) (by decide) (by decide) (by decide), h18])
      (by rw [hL10, v2 19 (by decide) (by decide) (by decide) (by decide), h19])
      (by rw [hL12, v2 21 (by decide) (by decide) (by decide) (by decide), h21])
      (by rw [hL11, hσ2, WState.setv_val, Function.update_of_ne (hne (by decide)), gS_val]; simp [hR])
      (by rw [hσ2]; simp [gS_sh, gS_st, Function.update_apply, hOG, ho])
      (by
        have v7 : σ2.val (Rg 7) = σ.val (Rg 7) := by rw [hσ2]; simp [gS_val, hR]
        rw [hL0, v7]
        omega)
    rw [hL0, hL11, hL6] at s3
    -- clear the index
    have s4 := wclear_spec cap (Rg 15) (gi + 1)
      (((appendO σ2 O (Rg 7) ((gateLabs r4 G gi).flatMap labE)).setv (Rg 20) (c + labAdd (gateLabs r4 G gi))).setv
        (Rg 15) (gi + 1)) (by simp) (by simp; omega)
    obtain ⟨σ4, hσ4⟩ : ∃ x, x = gS O GS Rg σ ((gateLabs r4 G gi).flatMap labE) (c + labAdd (gateLabs r4 G gi))
        (σ.sh GS + gi + 2) (σ.val (Rg 37) + gi + 2) := ⟨_, rfl⟩
    have e4 : ((((appendO σ2 O (Rg 7) ((gateLabs r4 G gi).flatMap labE)).setv (Rg 20)
        (c + labAdd (gateLabs r4 G gi))).setv (Rg 15) (gi + 1)).setv (Rg 15) 0) = σ4 := by
      rw [wsetv_setv, hσ2, hσ4]
      apply WState.eq
      · funext j
        simp only [WState.setv_sh, appendO_sh, gS_sh]
        by_cases hjG : j = GS
        · subst hjG; simp [Function.update_apply, Ne.symm hOG]
        · by_cases hjO : j = O
          · subst hjO; simp [Function.update_apply, hjG]
          · simp [Function.update_apply, hjG, hjO]
      · funext j
        simp only [WState.setv_st, appendO_st, gS_st]
        by_cases hjO : j = O
        · subst hjO; simp
        · simp [Function.update_apply, hjO]
      · funext j
        simp only [WState.setv_val, appendO_val, gS_val, Function.update_apply]
        by_cases a15 : j = Rg 15 <;> by_cases a37 : j = Rg 37 <;> by_cases a20 : j = Rg 20 <;>
          by_cases a7 : j = Rg 7 <;> simp_all [hR] <;> omega
      · simp [gS_cell]
    rw [e4] at s4
    -- the rest
    have hσ4v : ∀ j : Fin 64, j ≠ 20 → j ≠ 37 → j ≠ 7 → σ4.val (Rg j) = σ.val (Rg j) := by
      intro j b d e
      rw [hσ4, gS_val]
      simp [hR, b, d, e]
    have hσ4sh : σ4.sh GS = σ.sh GS + gi + 2 := by rw [hσ4, gS_sh]; simp
    have hσ4st : σ4.st GS = σ.st GS := by rw [hσ4, gS_st]; simp [Function.update_apply, Ne.symm hOG]
    have hσ437 : σ4.val (Rg 37) = σ.val (Rg 37) + gi + 2 := by rw [hσ4, gS_val]; simp
    have hσ420 : σ4.val (Rg 20) = c + labAdd (gateLabs r4 G gi) := by rw [hσ4, gS_val]; simp [hR]
    have hσ47 : σ4.val (Rg 7) = σ.val (Rg 7) + ((gateLabs r4 G gi).flatMap labE).length := by
      rw [hσ4, gS_val]; simp [hR]
    have ih := gisLoop_spec O GS hOG Rg r4 G Mg rest σ4 (c + labAdd (gateLabs r4 G gi))
      (fun i hi => by
        rw [hσ4st, hσ4sh]
        have := hw (gi + 2 + i) (by simp only [List.length_append]; omega)
        rw [gw_getD_rest] at this
        simpa [Nat.add_assoc] using this)
      (by rw [hσ4v 11 (by decide) (by decide) (by decide), h11])
      (by rw [hσ4v 1 (by decide) (by decide) (by decide), h1])
      (by rw [hσ4v 15 (by decide) (by decide) (by decide), h15])
      (by rw [hσ4v 14 (by decide) (by decide) (by decide), h14])
      (by rw [hσ4v 17 (by decide) (by decide) (by decide), h17])
      (by rw [hσ4v 18 (by decide) (by decide) (by decide), h18])
      (by rw [hσ4v 19 (by decide) (by decide) (by decide), h19])
      (by rw [hσ4v 21 (by decide) (by decide) (by decide), h21])
      hσ420
      (by rw [hσ4]; simp [gS_sh, gS_st, Function.update_apply, hOG, ho])
      (fun g hg => hMg g (by simp [hg])) hMc
      (by rw [hσ437]; simp only [List.length_append] at h37c; omega)
      (by rw [hσ47]; omega)
    rw [hσ4sh, hσ437] at ih
    rw [hσ4, gS_gS hOG] at ih
    rw [hσ4] at s4
    have eh : σ.sh GS + gi + 2 + (gisWord rest).length - 1 = σ.sh GS + (gw gi ++ gisWord rest).length - 1 := by
      simp only [List.length_append, gw_length]; omega
    have ep : σ.val (Rg 37) + gi + 2 + (gisWord rest).length - 1 =
        σ.val (Rg 37) + (gw gi ++ gisWord rest).length - 1 := by
      simp only [List.length_append, gw_length]; omega
    rw [eh, ep] at ih
    refine WExec.cast cap (WExec.whsT hb (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ih) ?_ ?_
    · rw [hlabs, hadd, gisWord_cons, Nat.add_assoc c]
    · have hB : 14 * gi + 21 + gateCost r4 G gi ≤ gisB r4 G Mg := by
        have hgc := gateCost_mono r4 G gi Mg hgi
        unfold gisB; omega
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end NearCubicWires.WireExponent3_5.FinalPass.RadB
