import Proof.Wire_3_5.Primitive.SeedFix.CtrHalf

/-! # X3, part 12: the unblocked coordinates of the center (P3:1200, 1213-1215)

"The remaining `n − rb` coordinates are split between the sides" (P3:1213-1215, `centerSide`): the unblocked
coordinates of the center are the row's remaining bits (the left half's `hL`) and the column's (the right half's
`n − rb − hL`), XOR the offset (`CtrMath.cw_unbL`, `cw_unbR`). Here: `UH`, `UI`, `unb_step`, `unbLoop_spec`,
**`unb_spec`** (`L` coordinates `Tl[k0 + i] = v_{base+i} ⊕ offset` emitted).

Paper quantity of the main type: the unblocked coordinates of the center `List.ofFn (centerAt P σ row col)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Ctr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- The unblocked loop's fixed hypotheses. -/
structure UH (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (base k0 L : ℕ) (Tl offL : List Bool) (W v : ℕ) : Prop where
  rc : (R = zRow ∧ cnt = rgROWC) ∨ (R = zCol ∧ cnt = rgCOLC)
  str : σ0.st R = frameP (binary W v) ++ [false]
  wd : base + L ≤ W
  off : σ0.st zOff = frameP offL ++ [false]
  tl : ∀ i < L, Tl.getD (k0 + i) false = xor (v.testBit (base + i)) (offL.getD (k0 + i) false)
  ko : k0 + L ≤ offL.length
  kt : k0 + L ≤ Tl.length

/-- The unblocked loop's state after `i` coordinates. -/
structure UI (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (base c0 k0 L : ℕ) (Tl Y0 : List Bool) (i : ℕ) (τ : CS) :
    Prop where
  ku : τ.val rgKU = L - i
  z : τ.val rgZ = 0
  shR : τ.sh R = 2 * (base + i)
  cn : τ.val cnt = c0 + 2 * i
  out : OutAt Tl Y0 (k0 + i) τ
  st : ∀ j, j ≠ zCtr → τ.st j = σ0.st j
  sh : ∀ j, j ≠ zCtr → j ≠ zOff → j ≠ R → τ.sh j = σ0.sh j
  oth : ∀ r, r ∉ [rgKU, rgZ, cnt, rgOC, rgOFFC] → τ.val r = σ0.val r
  cell : τ.cell = σ0.cell

section Unb
variable (cap : ℕ)

/-- The unblocked loop. -/
def unbLoop (R : Fin 4) (cnt : Fin 26) : CM := .whr rgKU (.seq (.dec rgKU) (p2Data R cnt))

/-- The unblocked coordinates: `rgKU := src`, the loop. -/
def unbM (R : Fin 4) (cnt src : Fin 26) : CM := .seq (FinalPass.Hash4.wcopyR src rgKU rgT) (unbLoop R cnt)

theorem unb_step (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (base c0 k0 L : ℕ) (Tl offL Y0 : List Bool) (W v : ℕ)
    (hH : UH R cnt σ0 base k0 L Tl offL W v) (i : ℕ) (hi : i < L) (τ : CS)
    (hI : UI R cnt σ0 base c0 k0 L Tl Y0 i τ) (hc1 : c0 + 2 * L + 2 ≤ cap) (hc2 : 2 * (k0 + L) + 2 ≤ cap)
    (hc3 : L ≤ cap) :
    ∃ τ', WExec cap (.seq (.dec rgKU) (p2Data R cnt)) τ τ' 80 ∧ UI R cnt σ0 base c0 k0 L Tl Y0 (i + 1) τ' := by
  obtain ⟨hRC, hRO, hcn⟩ := rc_ne hH.rc
  have hko := hH.ko
  have hkt := hH.kt
  have hwd := hH.wd
  have e0 := WExec.dec (cap := cap) rgKU τ (by rw [hI.ku]; omega)
  obtain ⟨τ0, hτ0⟩ : ∃ y, y = τ.setv rgKU (τ.val rgKU - 1) := ⟨_, rfl⟩
  rw [← hτ0] at e0
  have g0 : ∀ r, r ≠ rgKU → τ0.val r = τ.val r := fun r hr => by rw [hτ0]; simp [Function.update_apply, hr]
  have hck : cnt ≠ rgKU := (hcn rgKU (by decide) (by decide)).symm
  have hcz : cnt ≠ rgZ := (hcn rgZ (by decide) (by decide)).symm
  obtain ⟨τ1, e1, a1, z1, w1, s1, o1, v1, c1⟩ := readB_spec cap R cnt hcz τ0
    (by rw [g0 rgZ (by decide)]; exact hI.z) (by rw [g0 cnt hck, hI.cn]; omega) (by omega)
  have hbit : readTapeBit (τ0.st R) (τ0.sh R + 1) = v.testBit (base + i) := by
    rw [hτ0]; simp only [WState.setv_st, WState.setv_sh]
    rw [hI.st R hRC, hI.shR, hH.str, show 2 * (base + i) + 1 = 2 * (base + i) + 1 from rfl]
    exact stream_bit W v _ (by omega)
  rw [hbit] at z1
  have hout1 : OutAt Tl Y0 (k0 + i) τ1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [s1, hτ0]; exact hI.out.st
    · rw [o1 zCtr (Ne.symm hRC), hτ0]; exact hI.out.sh
    · rw [v1 rgOC (by decide) (hcn rgOC (by decide) (by decide)), g0 rgOC (by decide)]; exact hI.out.oc
    · rw [o1 zOff (Ne.symm hRO), hτ0]; exact hI.out.osh
    · rw [v1 rgOFFC (by decide) (hcn rgOFFC (by decide) (by decide)), g0 rgOFFC (by decide)]; exact hI.out.ofc
  obtain ⟨τ2, e2, out2, so2, st2, v2, c2⟩ := emit_step cap Tl offL Y0 (k0 + i) rgZ (by decide) (by decide) τ1 hout1
    (by rw [s1, hτ0]; simp only [WState.setv_st]; rw [hI.st zOff (by decide), hH.off]) (by omega) (by omega)
    (v.testBit (base + i)) z1 (hH.tl i hi) (by omega)
  have e3 := wclear_spec cap rgZ (τ2.val rgZ) τ2 rfl
    (by rw [v2 rgZ (by decide) (by decide), z1]; have := Bool.toNat_le (v.testBit (base + i)); omega)
  have hz2 : τ2.val rgZ ≤ 1 := by rw [v2 rgZ (by decide) (by decide), z1]; exact Bool.toNat_le _
  have g : ∀ r, r ≠ rgZ → r ≠ rgOC → r ≠ rgOFFC → r ≠ cnt → r ≠ rgKU → (τ2.setv rgZ 0).val r = τ.val r := by
    intro r r1 r2 r3 r4 r5
    simp only [WState.setv_val, Function.update_apply, if_neg r1]
    rw [v2 r r2 r3, v1 r r1 r4, g0 r r5]
  refine ⟨_, WExec.mono (WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3))) (by omega), ?_⟩
  refine ⟨?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.setv_val, Function.update_apply, show ¬((25 : Fin 26) = 14) by decide, if_false]
    rw [v2 rgKU (by decide) (by decide), v1 rgKU (by decide) (hcn rgKU (by decide) (by decide)), hτ0]
    simp [hI.ku]; omega
  · simp only [WState.setv_sh]
    rw [(st2 R hRC hRO).2, a1, hτ0]; simp only [WState.setv_sh]; rw [hI.shR]; ring
  · simp only [WState.setv_val, Function.update_apply, if_neg hcz]
    rw [v2 cnt (hcn rgOC (by decide) (by decide)).symm (hcn rgOFFC (by decide) (by decide)).symm, w1, g0 cnt hck,
      hI.cn]; ring
  · rw [show k0 + (i + 1) = k0 + i + 1 by ring]
    exact ⟨by simpa using out2.st, by simpa using out2.sh, by simpa using out2.oc, by simpa using out2.osh,
      by simpa using out2.ofc⟩
  · intro j hj
    simp only [WState.setv_st]
    by_cases h0 : j = zOff
    · subst h0; rw [so2, s1, hτ0]; exact hI.st zOff (by decide)
    · rw [(st2 j hj h0).1, s1, hτ0]; exact hI.st j hj
  · intro j j1 j2 j3
    simp only [WState.setv_sh]
    rw [(st2 j j1 j2).2, o1 j j3, hτ0]; exact hI.sh j j1 j2 j3
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g r hr.2.1 hr.2.2.2.1 hr.2.2.2.2 hr.2.2.1 hr.1]
    exact hI.oth r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])
  · simp only [WState.setv_cell]; rw [c2, c1, hτ0]; exact hI.cell

theorem unbLoop_spec (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (base c0 k0 L : ℕ) (Tl offL Y0 : List Bool) (W v : ℕ)
    (hH : UH R cnt σ0 base k0 L Tl offL W v) (hc1 : c0 + 2 * L + 2 ≤ cap) (hc2 : 2 * (k0 + L) + 2 ≤ cap)
    (hc3 : L ≤ cap) :
    ∀ (m i : ℕ) (τ : CS), i + m = L → UI R cnt σ0 base c0 k0 L Tl Y0 i τ →
      ∃ τ', WExec cap (unbLoop R cnt) τ τ' (m * 82 + 1) ∧ UI R cnt σ0 base c0 k0 L Tl Y0 L τ' := by
  intro m
  induction m with
  | zero =>
    intro i τ him hI
    have : i = L := by omega
    subst this
    exact ⟨τ, WExec.mono (WExec.whrF (by rw [hI.ku]; omega)) (by omega), hI⟩
  | succ m ih =>
    intro i τ him hI
    obtain ⟨τ1, e1, h1⟩ := unb_step cap R cnt σ0 base c0 k0 L Tl offL Y0 W v hH i (by omega) τ hI hc1 hc2 hc3
    obtain ⟨τ2, e2, h2⟩ := ih (i + 1) τ1 (by omega) h1
    exact ⟨τ2, WExec.mono (WExec.whrT (by rw [hI.ku]; omega) e1 e2) (by ring_nf; omega), h2⟩

/-- **The unblocked coordinates**: `L = src` coordinates `Tl[k0 + i] = v_{base+i} ⊕ offset` emitted. -/
theorem unb_spec (R : Fin 4) (cnt src : Fin 26) (hsrc : src ∉ [rgKU, rgT, rgZ, rgOC, rgOFFC, rgROWC, rgCOLC])
    (base c0 k0 L : ℕ) (Tl offL Y0 : List Bool) (W v : ℕ) (σ : CS) (hH : UH R cnt σ base k0 L Tl offL W v)
    (hL : σ.val src = L) (hku : σ.val rgKU = 0) (hz : σ.val rgZ = 0) (ht : σ.val rgT = 0) (hR : σ.sh R = 2 * base)
    (hc : σ.val cnt = c0) (hout : OutAt Tl Y0 k0 σ) (hc1 : c0 + 2 * L + 2 ≤ cap) (hc2 : 2 * (k0 + L) + 2 ≤ cap) :
    ∃ τ, WExec cap (unbM R cnt src) σ τ (100 * L + 10) ∧ UI R cnt σ base c0 k0 L Tl Y0 L τ := by
  obtain ⟨hRC, hRO, hcn⟩ := rc_ne hH.rc
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsrc
  have i1 := FinalPass.Hash4.wcopyR_spec cap src rgKU rgT hsrc.1 hsrc.2.1 (by decide) σ hku ht (by omega)
  have hck : cnt ≠ rgKU := (hcn rgKU (by decide) (by decide)).symm
  have g : ∀ r, r ≠ rgKU → (σ.setv rgKU (σ.val src)).val r = σ.val r := fun r hr => by
    simp [Function.update_apply, hr]
  have hI0 : UI R cnt σ base c0 k0 L Tl Y0 0 (σ.setv rgKU (σ.val src)) := by
    refine ⟨by simp [hL], by rw [g rgZ (by decide)]; exact hz, by simpa using hR, by rw [g cnt hck, hc]; simp,
      ?_, fun _ _ => rfl, fun _ _ _ _ => rfl, ?_, rfl⟩
    · exact ⟨by simpa using hout.st, by simpa using hout.sh, by rw [g rgOC (by decide)]; simpa using hout.oc,
        by simpa using hout.osh, by rw [g rgOFFC (by decide)]; simpa using hout.ofc⟩
    · intro r hr
      exact g r (fun e => hr (by rw [e]; exact List.mem_cons_self))
  obtain ⟨τ, e2, h2⟩ := unbLoop_spec cap R cnt σ base c0 k0 L Tl offL Y0 W v hH hc1 hc2 (by omega) L 0 _ (by omega)
    hI0
  exact ⟨τ, WExec.mono (WExec.seq i1 e2) (by rw [hL]; omega), h2⟩

end Unb

end NearCubicWires.WireExponent3_5.PrimT.Ctr
