import Proof.Wire_3_5.Primitive.SeedFix.CtrPass2b

/-! # X3, part 10: one block of the center (P3:1206-1216)

"Use all `2^s` cosets in each block" (P3:1206-1207) and the code's encoding (P3:1216): one block of the center is
the Hamming codeword of the block's data bits XOR the offset. The block program runs the first pass (the parity
bits packed, `p1_spec`) and the second pass (the `b` coordinates emitted, `p2_spec`). Here: `ZB` (every scratch
register `0`), **`p2_spec`**, **`blk_spec`**: from the block's start, the block's `b` center coordinates
`Tl[k0 + q]` on the center stream, the data stream past the block's `b − s` data bits, every scratch register back
at `0`.

Paper quantity of the main type: one block of the center `List.ofFn (centerAt P σ row col)`. -/

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

/-- Every scratch register of a block `0`. -/
def ZB (τ : CS) : Prop :=
  Zero1 τ ∧ τ.val rgPW = 0 ∧ τ.val rgKT = 0 ∧ τ.val rgPAR = 0 ∧ τ.val rgBIT = 0 ∧ τ.val rgHQ = 0

/-- The registers a block uses (`cnt` its stream's counter). -/
abbrev blkRegs (cnt : Fin 26) : List (Fin 26) :=
  [rgPAR, rgPW, rgKT, rgNP, rgE, rgCD, rgF, rgACC, rgZ, rgT, rgT2, rgRWC, rgKQ, rgBIT, rgHQ, cnt, rgOC, rgOFFC]

theorem cnt_p1 {R : Fin 4} {cnt : Fin 26} (h : (R = zRow ∧ cnt = rgROWC) ∨ (R = zCol ∧ cnt = rgCOLC)) :
    cnt ∉ p1Regs := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide

theorem notin_p2 {R : Fin 4} {cnt : Fin 26} (h : (R = zRow ∧ cnt = rgROWC) ∨ (R = zCol ∧ cnt = rgCOLC))
    (r : Fin 26) (hr : r ∉ [rgKQ, rgNP, rgE, rgPAR, rgZ, rgBIT, rgHQ, rgT, rgT2, rgOC, rgOFFC, rgROWC, rgCOLC]) :
    r ∉ p2Regs cnt := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
    tauto

section Block
variable (cap : ℕ)

/-- The second pass: the power tracker at `1`, `rgKQ := b`, the loop, the tracker cleared. -/
def p2 (R : Fin 4) (cnt : Fin 26) : CM :=
  .seq (.inc rgNP) (.seq (FinalPass.Hash4.wcopyR rgB rgKQ rgT) (.seq (p2Loop R cnt) (.seq (WM.clear rgNP)
    (WM.clear rgE))))

/-- The second pass's steps. -/
def p2Cost (b : ℕ) : ℕ := 300 * (b + 2) * (b + 2)

theorem p2_spec (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (cnt : Fin 26) (b0 c0 k0 : ℕ) (Tl offL Y0 : List Bool)
    (σ : CS) (hH : P2H P zb R cnt σ b0 k0 Tl offL) (hpar : σ.val rgPAR = packB (parL P zb)) (hz : Zero1 σ)
    (hbit : σ.val rgBIT = 0) (hhq : σ.val rgHQ = 0) (hR : σ.sh R = b0) (hc : σ.val cnt = c0)
    (hout : OutAt Tl Y0 k0 σ) (hb : σ.val rgB = P.b)
    (hc1 : c0 + 2 * dB P + 2 ≤ cap) (hc2 : 2 * (k0 + P.b) + 2 ≤ cap) (hc3 : 8 * (P.b + 2) ≤ cap) :
    ∃ τ, WExec cap (p2 R cnt) σ τ (p2Cost P.b) ∧ P2S P zb R cnt σ b0 c0 k0 Tl Y0 P.b τ ∧
      τ.val rgNP = 0 ∧ τ.val rgE = 0 ∧ τ.val rgKQ = 0 := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hz
  have hS0 : P2S P zb R cnt σ b0 c0 k0 Tl Y0 0 σ :=
    ⟨by rw [hpar]; rfl, z6, hbit, hhq, z7, z8, by rw [hR]; rfl, by rw [hc]; rfl, by simpa using hout,
      fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl⟩
  have i1 := WExec.inc (cap := cap) rgNP σ (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv rgNP (σ.val rgNP + 1) := ⟨_, rfl⟩
  rw [← hσ1] at i1
  have i2 := FinalPass.Hash4.wcopyR_spec cap rgB rgKQ rgT (by decide) (by decide) (by decide) σ1
    (by rw [hσ1]; simp [z10]) (by rw [hσ1]; simp [z7]) (by rw [hσ1]; simp [hb]; omega)
  obtain ⟨σ2, hσ2⟩ : ∃ y, y = σ1.setv rgKQ (σ1.val rgB) := ⟨_, rfl⟩
  rw [← hσ2] at i2
  have hS2 : P2S P zb R cnt σ b0 c0 k0 Tl Y0 0 σ2 :=
    P2S.congr hH hS0 (fun r r1 _ r3 => by rw [hσ2, hσ1]; simp [Function.update_apply, r1, r3])
      (by rw [hσ2, hσ1]; rfl) (by rw [hσ2, hσ1]; rfl) (by rw [hσ2, hσ1]; rfl)
  have hk2 : σ2.val rgKQ = P.b - 0 := by rw [hσ2, hσ1]; simp [hb]
  have hp2 : PowT 0 (σ2.val rgNP) (σ2.val rgE) := by
    rw [hσ2, hσ1]; simp [z1, z2]; exact powT_zero
  obtain ⟨σ3, i3, k3, p3, s3⟩ := p2Loop_spec cap P zb R cnt σ b0 c0 k0 Tl offL Y0 hH hc1 hc2 hc3 P.b 0 σ2 (by omega)
    hk2 hp2 hS2
  obtain ⟨u1, u2⟩ := powT_le p3
  have i4 := wclear_spec cap rgNP (σ3.val rgNP) σ3 rfl (by omega)
  have i5 := wclear_spec cap rgE ((σ3.setv rgNP 0).val rgE) (σ3.setv rgNP 0) rfl (by simp; omega)
  have hsc : 3 + 1 + (18 * σ1.val rgB + 3 + 1 + (P.b * (200 * (P.b + 2) + 2) + 1 + 1 + (3 * σ3.val rgNP + 1 + 1 +
      (3 * (σ3.setv rgNP 0).val rgE + 1)))) ≤ p2Cost P.b := by
    have e1 : σ1.val rgB = P.b := by rw [hσ1]; simp [hb]
    have e2 : (σ3.setv rgNP 0).val rgE = σ3.val rgE := by simp
    rw [e1, e2]
    unfold p2Cost
    nlinarith
  refine ⟨_, WExec.mono (WExec.seq i1 (WExec.seq i2 (WExec.seq i3 (WExec.seq i4 i5)))) hsc, ?_, ?_, ?_, ?_⟩
  · exact P2S.congr hH s3 (fun r r1 r2 _ => by simp [Function.update_apply, r1, r2]) rfl rfl rfl
  · simp [Function.update_apply]
  · simp
  · simp [k3]

/-- **One block**: the first pass, then the second. -/
def blk (R : Fin 4) (cnt : Fin 26) : CM := .seq (p1 R) (p2 R cnt)

/-- One block's steps. -/
def blkCost (b s : ℕ) : ℕ := p1Cost b s + 1 + p2Cost b

theorem blk_spec (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (cnt : Fin 26) (b0 c0 k0 : ℕ) (Tl offL Y0 : List Bool)
    (σ : CS) (hH : P2H P zb R cnt σ b0 k0 Tl offL) (hzero : ZB σ) (hR : σ.sh R = b0) (hc : σ.val cnt = c0)
    (hout : OutAt Tl Y0 k0 σ) (hb : σ.val rgB = P.b) (hs : σ.val rgS = P.s)
    (hc1 : c0 + 2 * dB P + 2 ≤ cap) (hc2 : 2 * (k0 + P.b) + 2 ≤ cap) (hc3 : 8 * (P.b + 2) ≤ cap) :
    ∃ τ, WExec cap (blk R cnt) σ τ (blkCost P.b P.s) ∧ ZB τ ∧ τ.sh R = b0 + 2 * dB P ∧
      τ.val cnt = c0 + 2 * dB P ∧ OutAt Tl Y0 (k0 + P.b) τ ∧ (∀ i, i ≠ zCtr → τ.st i = σ.st i) ∧
      (∀ i, i ≠ zCtr → i ≠ zOff → i ≠ R → τ.sh i = σ.sh i) ∧ (∀ r, r ∉ blkRegs cnt → τ.val r = σ.val r) ∧
      τ.cell = σ.cell := by
  obtain ⟨hRC, hRO, hcn⟩ := rc_ne hH.rc
  obtain ⟨hz, hpw, hkt, hpar, hbit, hhq⟩ := hzero
  obtain ⟨τ1, e1, a1, b1, c1, d1, f1, s1, h1, v1, k1⟩ := p1_spec cap P zb R b0 σ hH.dat hR hb hs hz hpw hkt hpar hc3
  have g1 : ∀ r, r ∉ p1Regs → τ1.val r = σ.val r := v1
  have hH1 : P2H P zb R cnt τ1 b0 k0 Tl offL :=
    ⟨hH.rc, by rw [s1]; exact hH.dat, by rw [s1]; exact hH.off, hH.tl, hH.ko, hH.kt⟩
  have hout1 : OutAt Tl Y0 k0 τ1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [s1]; exact hout.st
    · rw [h1 zCtr (Ne.symm hRC)]; exact hout.sh
    · rw [g1 rgOC (by decide)]; exact hout.oc
    · rw [h1 zOff (Ne.symm hRO)]; exact hout.osh
    · rw [g1 rgOFFC (by decide)]; exact hout.ofc
  have hc1' : τ1.val cnt = c0 := by rw [g1 cnt (cnt_p1 hH.rc)]; exact hc
  obtain ⟨τ2, e2, s2, n2, m2, k2⟩ := p2_spec cap P zb R cnt b0 c0 k0 Tl offL Y0 τ1 hH1 a1 d1
    (by rw [g1 rgBIT (by decide)]; exact hbit) (by rw [g1 rgHQ (by decide)]; exact hhq) f1 hc1' hout1
    (by rw [g1 rgB (by decide)]; exact hb) hc1 hc2 hc3
  have nb := nd_b P
  have hpar2 : τ2.val rgPAR = 0 := by
    rw [s2.par, npar_b]
    have : (parL P zb).drop P.s = [] := List.drop_of_length_le (by rw [parL_length])
    rw [this]; rfl
  have g2 : ∀ r, r ∉ p2Regs cnt → τ2.val r = τ1.val r := s2.oth
  refine ⟨τ2, WExec.seq e1 e2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10⟩ := d1
    refine ⟨⟨n2, m2, ?_, ?_, ?_, s2.z, s2.tt, s2.t2, ?_, k2⟩, ?_, ?_, hpar2, s2.bit, s2.hq⟩
    · rw [g2 rgCD (notin_p2 hH.rc rgCD (by decide))]; exact y3
    · rw [g2 rgF (notin_p2 hH.rc rgF (by decide))]; exact y4
    · rw [g2 rgACC (notin_p2 hH.rc rgACC (by decide))]; exact y5
    · rw [g2 rgRWC (notin_p2 hH.rc rgRWC (by decide))]; exact y9
    · rw [g2 rgPW (notin_p2 hH.rc rgPW (by decide))]; exact b1
    · rw [g2 rgKT (notin_p2 hH.rc rgKT (by decide))]; exact c1
  · rw [s2.shR, nb]
  · rw [s2.cn, nb]
  · exact s2.out
  · intro i hi; rw [s2.st i hi, s1]
  · intro i i1 i2 i3; rw [s2.sh i i1 i2 i3, h1 i i3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g2 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2])]
    exact g1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.1])
  · rw [s2.cell, k1]

end Block

end NearCubicWires.WireExponent3_5.PrimT.Ctr
