import Proof.Wire_3_5.Primitive.SeedFix.CtrBlock
import Proof.Wire_3_5.Selection.PointMath

/-! # X3, part 11: a half's blocks and its unblocked coordinates (P3:1212-1216)

"Assign `r/2` whole blocks to each side" (P3:1212-1213): the left half's `r/2` blocks carry the row's data bits, the
right half's the column's, `dB = b − s` bits per block (`C4GeoV.ctrBit`); the unblocked coordinates carry the
remaining row (left) and column (right) bits. Here:

* `stream_bit` (bit `j` of `v` read at cell `2j + 1` of `frameP (binary W v) ++ [false]`);
* `HI`, `half_step`, `halfLoop_spec`, **`half_spec`**: the `r/2` blocks of a half emitted;
* `UI`, `unb_step`, `unbLoop_spec`, **`unb_spec`**: `L` unblocked coordinates emitted.

Paper quantity of the main types: the halves of the center `List.ofFn (centerAt P σ row col)`. -/

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

theorem stream_bit (W v j : ℕ) (hj : j < W) :
    readTapeBit (frameP (binary W v) ++ [false]) (2 * j + 1) = v.testBit j := by
  rw [readTapeBit_frameP _ _ j (by rw [SignedSortKey.binary_length]; exact hj)]
  exact SelectionMachine.Point.binary_getD W v j hj

theorem notin_hb {R : Fin 4} {cnt : Fin 26} (h : (R = zRow ∧ cnt = rgROWC) ∨ (R = zCol ∧ cnt = rgCOLC))
    (r : Fin 26) (hr : r ∉ [rgKB, rgPAR, rgPW, rgKT, rgNP, rgE, rgCD, rgF, rgACC, rgZ, rgT, rgT2, rgRWC, rgKQ, rgBIT,
      rgHQ, rgOC, rgOFFC, rgROWC, rgCOLC]) : r ∉ rgKB :: blkRegs cnt := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
    tauto

section Half
variable (cap : ℕ)

/-- A half's block loop. -/
def halfLoop (R : Fin 4) (cnt : Fin 26) : CM := .whr rgKB (.seq (.dec rgKB) (blk R cnt))

/-- A half: `rgKB := r/2`, the block loop. -/
def halfM (R : Fin 4) (cnt : Fin 26) : CM := .seq (FinalPass.Hash4.wcopyR rgH rgKB rgT) (halfLoop R cnt)

/-- **A half's invariant** after `jj` blocks. -/
structure HI (P : StarParams) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (c0 k0 : ℕ) (Tl Y0 : List Bool) (jj : ℕ)
    (τ : CS) : Prop where
  kb : τ.val rgKB = P.r / 2 - jj
  zero : ZB τ
  shR : τ.sh R = 2 * (jj * dB P)
  cn : τ.val cnt = c0 + 2 * (jj * dB P)
  out : OutAt Tl Y0 (k0 + jj * P.b) τ
  st : ∀ i, i ≠ zCtr → τ.st i = σ0.st i
  sh : ∀ i, i ≠ zCtr → i ≠ zOff → i ≠ R → τ.sh i = σ0.sh i
  oth : ∀ r, r ∉ rgKB :: blkRegs cnt → τ.val r = σ0.val r
  cell : τ.cell = σ0.cell

/-- A half's fixed hypotheses: the stream holds `v` (width `W ≥ (r/2)·dB`), the offset, the center's blocks. -/
structure HH (P : StarParams) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (k0 : ℕ) (Tl offL : List Bool) (W v : ℕ) :
    Prop where
  rc : (R = zRow ∧ cnt = rgROWC) ∨ (R = zCol ∧ cnt = rgCOLC)
  str : σ0.st R = frameP (binary W v) ++ [false]
  wd : P.r / 2 * dB P ≤ W
  off : σ0.st zOff = frameP offL ++ [false]
  tl : ∀ jj < P.r / 2, ∀ q < P.b, Tl.getD (k0 + (jj * P.b + q)) false =
    xor (encB P (fun m => v.testBit (jj * dB P + m)) q) (offL.getD (k0 + (jj * P.b + q)) false)
  ko : k0 + P.r / 2 * P.b ≤ offL.length
  kt : k0 + P.r / 2 * P.b ≤ Tl.length
  b : σ0.val rgB = P.b
  s : σ0.val rgS = P.s
  h : σ0.val rgH = P.r / 2

theorem half_step (P : StarParams) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (c0 k0 : ℕ) (Tl offL Y0 : List Bool)
    (W v : ℕ) (hH : HH P R cnt σ0 k0 Tl offL W v) (jj : ℕ) (hj : jj < P.r / 2) (τ : CS)
    (hI : HI P R cnt σ0 c0 k0 Tl Y0 jj τ)
    (hc1 : c0 + 2 * (P.r / 2 * dB P) + 2 ≤ cap) (hc2 : 2 * (k0 + P.r / 2 * P.b) + 2 ≤ cap)
    (hc3 : 8 * (P.b + 2) ≤ cap) (hc4 : P.r / 2 ≤ cap) :
    ∃ τ', WExec cap (.seq (.dec rgKB) (blk R cnt)) τ τ' (blkCost P.b P.s + 2) ∧
      HI P R cnt σ0 c0 k0 Tl Y0 (jj + 1) τ' := by
  obtain ⟨hRC, hRO, hcn⟩ := rc_ne hH.rc
  have hjd : (jj + 1) * dB P ≤ P.r / 2 * dB P := Nat.mul_le_mul_right _ hj
  have hjb : (jj + 1) * P.b ≤ P.r / 2 * P.b := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at hjd hjb
  have e0 := WExec.dec (cap := cap) rgKB τ (by rw [hI.kb]; omega)
  obtain ⟨τ0, hτ0⟩ : ∃ y, y = τ.setv rgKB (τ.val rgKB - 1) := ⟨_, rfl⟩
  rw [← hτ0] at e0
  have g0 : ∀ r, r ≠ rgKB → τ0.val r = τ.val r := fun r hr => by rw [hτ0]; simp [Function.update_apply, hr]
  have hcb : cnt ≠ rgKB := (hcn rgKB (by decide) (by decide)).symm
  obtain ⟨⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩, zpw, zkt, zpar, zbit, zhq⟩ := hI.zero
  have hko := hH.ko
  have hkt := hH.kt
  have hH2 : P2H P (fun m => v.testBit (jj * dB P + m)) R cnt τ0 (2 * (jj * dB P)) (k0 + jj * P.b) Tl offL := by
    refine ⟨hH.rc, fun m hm => ?_, ?_, fun q hq => ?_, by omega, by omega⟩
    · rw [hτ0]; simp only [WState.setv_st]; rw [hI.st R hRC, hH.str]
      rw [show 2 * (jj * dB P) + 2 * m + 1 = 2 * (jj * dB P + m) + 1 by ring]
      exact stream_bit W v _ (by have := hH.wd; omega)
    · rw [hτ0]; simp only [WState.setv_st]; rw [hI.st zOff (by decide), hH.off]
    · rw [show k0 + jj * P.b + q = k0 + (jj * P.b + q) by ring]; exact hH.tl jj hj q hq
  have hout0 : OutAt Tl Y0 (k0 + jj * P.b) τ0 :=
    ⟨by rw [hτ0]; exact hI.out.st, by rw [hτ0]; exact hI.out.sh, by rw [g0 rgOC (by decide)]; exact hI.out.oc,
      by rw [hτ0]; exact hI.out.osh, by rw [g0 rgOFFC (by decide)]; exact hI.out.ofc⟩
  obtain ⟨τ1, e1, zb1, sh1, cn1, out1, st1, sR1, v1, c1⟩ := blk_spec cap P (fun m => v.testBit (jj * dB P + m)) R cnt
    (2 * (jj * dB P)) (c0 + 2 * (jj * dB P)) (k0 + jj * P.b) Tl offL Y0 τ0 hH2
    ⟨⟨by rw [g0 _ (by decide)]; exact z1, by rw [g0 _ (by decide)]; exact z2, by rw [g0 _ (by decide)]; exact z3,
      by rw [g0 _ (by decide)]; exact z4, by rw [g0 _ (by decide)]; exact z5, by rw [g0 _ (by decide)]; exact z6,
      by rw [g0 _ (by decide)]; exact z7, by rw [g0 _ (by decide)]; exact z8, by rw [g0 _ (by decide)]; exact z9,
      by rw [g0 _ (by decide)]; exact z10⟩, by rw [g0 _ (by decide)]; exact zpw, by rw [g0 _ (by decide)]; exact zkt,
      by rw [g0 _ (by decide)]; exact zpar, by rw [g0 _ (by decide)]; exact zbit, by rw [g0 _ (by decide)]; exact zhq⟩
    (by rw [hτ0]; exact hI.shR) (by rw [g0 cnt hcb]; exact hI.cn) hout0
    (by rw [g0 rgB (by decide), hI.oth rgB (notin_hb hH.rc rgB (by decide)), hH.b])
    (by rw [g0 rgS (by decide), hI.oth rgS (notin_hb hH.rc rgS (by decide)), hH.s])
    (by omega) (by omega) hc3
  refine ⟨τ1, WExec.mono (WExec.seq e0 e1) (by omega), ?_, zb1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v1 rgKB (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide, by decide, by decide, fun e => hcb e.symm, by decide, by decide⟩),
      hτ0]
    simp [hI.kb]; omega
  · rw [sh1]; ring
  · rw [cn1]; ring
  · rw [show k0 + (jj + 1) * P.b = k0 + jj * P.b + P.b by ring]; exact out1
  · intro i hi; rw [st1 i hi, hτ0]; exact hI.st i hi
  · intro i i1 i2 i3; rw [sR1 i i1 i2 i3, hτ0]; exact hI.sh i i1 i2 i3
  · intro r hr
    have hr' : r ∉ blkRegs cnt := fun m => hr (List.mem_cons_of_mem _ m)
    have hrk : r ≠ rgKB := fun e => hr (by rw [e]; exact List.mem_cons_self)
    rw [v1 r hr', g0 r hrk]; exact hI.oth r hr
  · rw [c1, hτ0]; exact hI.cell

theorem halfLoop_spec (P : StarParams) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (c0 k0 : ℕ) (Tl offL Y0 : List Bool)
    (W v : ℕ) (hH : HH P R cnt σ0 k0 Tl offL W v)
    (hc1 : c0 + 2 * (P.r / 2 * dB P) + 2 ≤ cap) (hc2 : 2 * (k0 + P.r / 2 * P.b) + 2 ≤ cap)
    (hc3 : 8 * (P.b + 2) ≤ cap) (hc4 : P.r / 2 ≤ cap) :
    ∀ (m jj : ℕ) (τ : CS), jj + m = P.r / 2 → HI P R cnt σ0 c0 k0 Tl Y0 jj τ →
      ∃ τ', WExec cap (halfLoop R cnt) τ τ' (m * (blkCost P.b P.s + 4) + 1) ∧
        HI P R cnt σ0 c0 k0 Tl Y0 (P.r / 2) τ' := by
  intro m
  induction m with
  | zero =>
    intro jj τ hjm hI
    have : jj = P.r / 2 := by omega
    subst this
    exact ⟨τ, WExec.mono (WExec.whrF (by rw [hI.kb]; omega)) (by omega), hI⟩
  | succ m ih =>
    intro jj τ hjm hI
    obtain ⟨τ1, e1, h1⟩ := half_step cap P R cnt σ0 c0 k0 Tl offL Y0 W v hH jj (by omega) τ hI hc1 hc2 hc3 hc4
    obtain ⟨τ2, e2, h2⟩ := ih (jj + 1) τ1 (by omega) h1
    exact ⟨τ2, WExec.mono (WExec.whrT (by rw [hI.kb]; omega) e1 e2) (by ring_nf; omega), h2⟩

/-- A half's steps. -/
def halfCost (P : StarParams) : ℕ := 18 * (P.r / 2) + 3 + 1 + ((P.r / 2) * (blkCost P.b P.s + 4) + 1)

/-- **A half**: its `r/2` blocks of the center emitted (P3:1212-1216). -/
theorem half_spec (P : StarParams) (R : Fin 4) (cnt : Fin 26) (c0 k0 : ℕ) (Tl offL Y0 : List Bool) (W v : ℕ)
    (σ : CS) (hH : HH P R cnt σ k0 Tl offL W v) (hzero : ZB σ) (hkb : σ.val rgKB = 0) (hR : σ.sh R = 0)
    (hc : σ.val cnt = c0) (hout : OutAt Tl Y0 k0 σ)
    (hc1 : c0 + 2 * (P.r / 2 * dB P) + 2 ≤ cap) (hc2 : 2 * (k0 + P.r / 2 * P.b) + 2 ≤ cap)
    (hc3 : 8 * (P.b + 2) ≤ cap) (hc4 : P.r / 2 ≤ cap) :
    ∃ τ, WExec cap (halfM R cnt) σ τ (halfCost P) ∧ HI P R cnt σ c0 k0 Tl Y0 (P.r / 2) τ := by
  obtain ⟨hRC, hRO, hcn⟩ := rc_ne hH.rc
  have hcb : cnt ≠ rgKB := (hcn rgKB (by decide) (by decide)).symm
  obtain ⟨⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩, zpw, zkt, zpar, zbit, zhq⟩ := hzero
  have i1 := FinalPass.Hash4.wcopyR_spec cap rgH rgKB rgT (by decide) (by decide) (by decide) σ hkb z7
    (by rw [hH.h]; exact hc4)
  have g : ∀ r, r ≠ rgKB → (σ.setv rgKB (σ.val rgH)).val r = σ.val r := fun r hr => by
    simp [Function.update_apply, hr]
  have hI0 : HI P R cnt σ c0 k0 Tl Y0 0 (σ.setv rgKB (σ.val rgH)) := by
    refine ⟨by simp [hH.h], ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, by simpa using hR,
      by rw [g cnt hcb, hc]; simp, ?_, fun _ _ => rfl, fun _ _ _ _ => rfl, ?_, rfl⟩
    all_goals first
      | (rw [g _ (by decide)]; assumption)
      | skip
    · exact ⟨by simpa using hout.st, by simpa using hout.sh, by rw [g rgOC (by decide)]; simpa using hout.oc,
        by simpa using hout.osh, by rw [g rgOFFC (by decide)]; simpa using hout.ofc⟩
    · intro r hr
      exact g r (fun e => hr (by rw [e]; exact List.mem_cons_self))
  obtain ⟨τ, e2, h2⟩ := halfLoop_spec cap P R cnt σ c0 k0 Tl offL Y0 W v hH hc1 hc2 hc3 hc4 (P.r / 2) 0 _ (by omega) hI0
  exact ⟨τ, WExec.mono (WExec.seq i1 e2) (by rw [hH.h]; unfold halfCost; omega), h2⟩

end Half

end NearCubicWires.WireExponent3_5.PrimT.Ctr
