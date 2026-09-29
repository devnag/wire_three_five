import Proof.Wire_3_5.Primitive.SeedFix.CtrPass1

/-! # X3, part 5: all of a block's parity bits packed (P3:1202-1206)

"The syndrome `Hx` uniquely specifies `e`" (P3:1204-1206): the `s` parity bits of a block are its syndrome's bits.
The first pass runs one scan per `t < s` (`p1Loop_spec`), packs parity `t` into `rgPAR` at weight `2^t`
(`packA`), doubles `rgPW`, and returns the stream to the block's start. Here:

* `packA_spec`, `dblPW_spec`, **`scan1_spec`** (one parity bit packed, every tracker back at `0`);
* **`p1_spec`**: `rgPAR = packB (parL P zb)`, the block's `s` parity bits.

Paper quantity of the main type: the block's parity bits `parL P zb` (its syndrome). -/

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

section Par
variable (cap : ℕ)

/-- Parity `t` packed: `rgPAR += rgACC·rgPW`, `rgACC := 0`. -/
def packA : CM :=
  .ifr rgACC (.seq (FinalPass.Hash4.wcopyR rgPW rgT2 rgT) (.seq (WM.move rgT2 rgPAR) (.dec rgACC))) .skip

theorem packA_spec (τ : CS) (a : Bool) (w : ℕ) (hA : τ.val rgACC = a.toNat) (hT : τ.val rgT = 0)
    (hT2 : τ.val rgT2 = 0) (hpw : τ.val rgPW = w) (hc1 : τ.val rgPAR + w ≤ cap) (hc2 : w + 1 ≤ cap) :
    ∃ τ', WExec cap packA τ τ' (30 * w + 20) ∧ τ'.val rgPAR = τ.val rgPAR + a.toNat * w ∧ τ'.val rgACC = 0 ∧
      τ'.val rgT = 0 ∧ τ'.val rgT2 = 0 ∧ τ'.st = τ.st ∧ τ'.sh = τ.sh ∧
      (∀ r, r ≠ rgPAR → r ≠ rgACC → r ≠ rgT2 → τ'.val r = τ.val r) ∧ τ'.cell = τ.cell := by
  cases a
  · exact ⟨τ, WExec.mono (WExec.ifrF (by simpa using hA) (WExec.skip τ)) (by omega), by simp, by simpa using hA,
      hT, hT2, rfl, rfl, fun _ _ _ _ => rfl, rfl⟩
  · have s1 := FinalPass.Hash4.wcopyR_spec cap rgPW rgT2 rgT (by decide) (by decide) (by decide) τ hT2 hT (by omega)
    set τ1 := τ.setv rgT2 (τ.val rgPW) with hτ1
    have s2 := wmove_spec cap rgT2 rgPAR (by decide) (τ1.val rgT2) τ1 rfl (by simp [hτ1]; omega)
      (by simp [hτ1]; omega)
    set τ2 := (τ1.setv rgT2 0).setv rgPAR (τ1.val rgPAR + τ1.val rgT2) with hτ2
    have s3 := WExec.dec (cap := cap) rgACC τ2 (by simp [hτ2, hτ1, hA]; omega)
    have w1 : τ1.val rgT2 = w := by simp [hτ1, hpw]
    refine ⟨_, WExec.mono (WExec.ifrT (by simp [hA]) (WExec.seq s1 (WExec.seq s2 s3))) (by rw [w1]; omega),
      ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl⟩
    · simp [hτ2, hτ1, hpw]
    · simp [hτ2, hτ1, hA]
    · simp [hτ2, hτ1, hT]
    · simp [hτ2, hτ1]
    · intro r r1 r2 r3
      simp [hτ2, hτ1, Function.update_apply, r1, r2, r3]

/-- `rgPW := 2·rgPW`. -/
def dblPW : CM := .seq (FinalPass.Hash4.wcopyR rgPW rgT2 rgT) (WM.move rgT2 rgPW)

theorem dblPW_spec (τ : CS) (w : ℕ) (hT : τ.val rgT = 0) (hT2 : τ.val rgT2 = 0) (hpw : τ.val rgPW = w)
    (hc : 2 * w + 1 ≤ cap) :
    ∃ τ', WExec cap dblPW τ τ' (30 * w + 10) ∧ τ'.val rgPW = 2 * w ∧ τ'.val rgT = 0 ∧ τ'.val rgT2 = 0 ∧
      τ'.st = τ.st ∧ τ'.sh = τ.sh ∧ (∀ r, r ≠ rgPW → r ≠ rgT2 → τ'.val r = τ.val r) ∧ τ'.cell = τ.cell := by
  have s1 := FinalPass.Hash4.wcopyR_spec cap rgPW rgT2 rgT (by decide) (by decide) (by decide) τ hT2 hT (by omega)
  set τ1 := τ.setv rgT2 (τ.val rgPW) with hτ1
  have s2 := wmove_spec cap rgT2 rgPW (by decide) (τ1.val rgT2) τ1 rfl (by simp [hτ1]; omega)
    (by simp [hτ1]; omega)
  have w1 : τ1.val rgT2 = w := by simp [hτ1, hpw]
  refine ⟨_, WExec.mono (WExec.seq s1 s2) (by rw [w1]; omega), ?_, ?_, ?_, rfl, rfl, ?_, rfl⟩
  · simp [hτ1, hpw]; ring
  · simp [hτ1, hT]
  · simp [hτ1]
  · intro r r1 r2
    simp [hτ1, Function.update_apply, r1, r2]

/-- The four trackers cleared. -/
def clr4 : CM := .seq (WM.clear rgNP) (.seq (WM.clear rgE) (.seq (WM.clear rgCD) (WM.clear rgF)))

theorem clr4_spec (τ : CS) (hc : τ.val rgNP ≤ cap ∧ τ.val rgE ≤ cap ∧ τ.val rgCD ≤ cap ∧ τ.val rgF ≤ cap) :
    WExec cap clr4 τ ((((τ.setv rgNP 0).setv rgE 0).setv rgCD 0).setv rgF 0)
      (3 * (τ.val rgNP + τ.val rgE + τ.val rgCD + τ.val rgF) + 7) := by
  obtain ⟨c1, c2, c3, c4⟩ := hc
  have s1 := wclear_spec cap rgNP (τ.val rgNP) τ rfl c1
  have s2 := wclear_spec cap rgE ((τ.setv rgNP 0).val rgE) (τ.setv rgNP 0) rfl (by simp; omega)
  have s3 := wclear_spec cap rgCD (((τ.setv rgNP 0).setv rgE 0).val rgCD) ((τ.setv rgNP 0).setv rgE 0) rfl
    (by simp; omega)
  have s4 := wclear_spec cap rgF ((((τ.setv rgNP 0).setv rgE 0).setv rgCD 0).val rgF)
    (((τ.setv rgNP 0).setv rgE 0).setv rgCD 0) rfl (by simp; omega)
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_
  simp
  omega

/-- The zero registers of a block's passes. -/
def Zero1 (τ : CS) : Prop :=
  τ.val rgNP = 0 ∧ τ.val rgE = 0 ∧ τ.val rgCD = 0 ∧ τ.val rgF = 0 ∧ τ.val rgACC = 0 ∧ τ.val rgZ = 0 ∧
    τ.val rgT = 0 ∧ τ.val rgT2 = 0 ∧ τ.val rgRWC = 0 ∧ τ.val rgKQ = 0

/-- The scan's set-up: `rgNP := 1`, `rgCD := rgPW`, bit `t` of `1`, `rgKQ := b`. -/
def scanInit : CM :=
  .seq (.inc rgNP) (.seq (FinalPass.Hash4.wcopyR rgPW rgCD rgT) (.seq bitStep (FinalPass.Hash4.wcopyR rgB rgKQ rgT)))

theorem scanInit_spec (P : StarParams) (zb : ℕ → Bool) (t : ℕ) (ht : t < P.s) (R : Fin 4) (b0 : ℕ) (σ : CS)
    (hR : σ.sh R = b0) (hpw : σ.val rgPW = 2 ^ t) (hb : σ.val rgB = P.b) (hz : Zero1 σ)
    (hcap : 8 * (P.b + 2) ≤ cap) :
    ∃ σ4, WExec cap scanInit σ σ4 (60 * (P.b + 2)) ∧ P1I P zb t R σ b0 0 σ4 := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hz
  have hpt := pow_lt_b P t ht
  have i1 := WExec.inc (cap := cap) rgNP σ (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv rgNP (σ.val rgNP + 1) := ⟨_, rfl⟩
  rw [← hσ1] at i1
  have i2 := FinalPass.Hash4.wcopyR_spec cap rgPW rgCD rgT (by decide) (by decide) (by decide) σ1
    (by simp [hσ1, z3]) (by simp [hσ1, z7]) (by simp [hσ1]; omega)
  obtain ⟨σ2, hσ2⟩ : ∃ y, y = σ1.setv rgCD (σ1.val rgPW) := ⟨_, rfl⟩
  rw [← hσ2] at i2
  obtain ⟨σ3, i3, b3, t3, s3, h3, v3, c3⟩ := bitStep_spec cap σ2 t 0
    (by have := bitT_zero t; simpa [hσ2, hσ1, hpw, z4] using this) (by simp [hσ2, hσ1, hpw])
    (by simp [hσ2, hσ1, z7]) (by omega)
  have hb3 : σ3.val rgB = P.b := by rw [v3 rgB (by decide) (by decide)]; simp [hσ2, hσ1, hb]
  have i4 := FinalPass.Hash4.wcopyR_spec cap rgB rgKQ rgT (by decide) (by decide) (by decide) σ3
    (by rw [v3 rgKQ (by decide) (by decide)]; simp [hσ2, hσ1, z10]) t3 (by rw [hb3]; omega)
  obtain ⟨σ4, hσ4⟩ : ∃ y, y = σ3.setv rgKQ (σ3.val rgB) := ⟨_, rfl⟩
  rw [← hσ4] at i4
  have g4 : ∀ r, r ≠ rgKQ → r ≠ rgCD → r ≠ rgF → r ≠ rgNP → σ4.val r = σ.val r := by
    intro r r1 r2 r3 r4
    rw [hσ4]
    simp only [WState.setv_val, Function.update_apply, if_neg r1]
    rw [v3 r r2 r3, hσ2, hσ1]
    simp [Function.update_apply, r2, r4]
  have hc2 : σ1.val rgPW = 2 ^ t := by simp [hσ1, hpw]
  refine ⟨σ4, WExec.mono (WExec.seq i1 (WExec.seq i2 (WExec.seq i3 i4))) (by rw [hc2, hb3]; omega), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ4]; simp [hb3]
  · have e1 : σ4.val rgNP = 1 := by
      rw [hσ4]; simp [v3 rgNP (by decide) (by decide), hσ2, hσ1, z1]
    have e2 : σ4.val rgE = 0 := by rw [g4 rgE (by decide) (by decide) (by decide) (by decide), z2]
    rw [e1, e2]; exact powT_zero
  · have e1 : σ4.val rgCD = σ3.val rgCD := by rw [hσ4]; simp
    have e2 : σ4.val rgF = σ3.val rgF := by rw [hσ4]; simp
    rw [e1, e2]; exact b3
  · rw [g4 rgPW (by decide) (by decide) (by decide) (by decide), hpw]
  · rw [g4 rgACC (by decide) (by decide) (by decide) (by decide), z5]; rfl
  · rw [g4 rgZ (by decide) (by decide) (by decide) (by decide), z6]
  · rw [hσ4]; simp [t3]
  · rw [g4 rgT2 (by decide) (by decide) (by decide) (by decide), z8]
  · rw [g4 rgRWC (by decide) (by decide) (by decide) (by decide), z9]; rfl
  · rw [hσ4]; simp [h3, hσ2, hσ1, hR]; rfl
  · rw [hσ4]; simp [s3, hσ2, hσ1]
  · intro i hi; rw [hσ4]; simp [h3, hσ2, hσ1]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g4 r hr.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.1
  · rw [hσ4]; simp [c3, hσ2, hσ1]

/-- The scan's end: the stream back, the trackers cleared, parity `t` packed, `rgPW` doubled. -/
def scanFin (R : Fin 4) : CM := .seq (Flips.rew1 R rgRWC) (.seq clr4 (.seq packA dblPW))

theorem scanFin_spec (P : StarParams) (zb : ℕ → Bool) (t : ℕ) (ht : t < P.s) (R : Fin 4) (b0 : ℕ) (σ0 : CS)
    (τ : CS) (h5 : P1I P zb t R σ0 b0 P.b τ) (hpar : σ0.val rgPAR < 2 ^ t) (hcap : 8 * (P.b + 2) ≤ cap) :
    ∃ τ', WExec cap (scanFin R) τ τ' (100 * (P.b + 2)) ∧
      τ'.val rgPAR = σ0.val rgPAR + (parB P zb t).toNat * 2 ^ t ∧ τ'.val rgPW = 2 ^ (t + 1) ∧ Zero1 τ' ∧
      τ'.sh R = b0 ∧ τ'.st = σ0.st ∧ (∀ i, i ≠ R → τ'.sh i = σ0.sh i) ∧
      (∀ r, r ∉ [rgPAR, rgPW, rgNP, rgE, rgCD, rgF, rgACC, rgZ, rgT, rgT2, rgRWC, rgKQ] → τ'.val r = σ0.val r) ∧
      τ'.cell = σ0.cell := by
  have hpt := pow_lt_b P t ht
  have hdb : dB P ≤ P.b := by unfold dB; omega
  have nb := nd_b P
  obtain ⟨σ6, i6, a6, r6, s6, h6, v6, c6⟩ := back_spec cap R rgRWC (2 * nd P P.b) τ b0 h5.rwc h5.shR (by omega)
  obtain ⟨cd1, cd2, f1⟩ := bitT_pos h5.bt
  obtain ⟨u1, u2⟩ := powT_le h5.pw
  have hc6 : σ6.val rgNP ≤ cap ∧ σ6.val rgE ≤ cap ∧ σ6.val rgCD ≤ cap ∧ σ6.val rgF ≤ cap := by
    rw [v6 rgNP (by decide), v6 rgE (by decide), v6 rgCD (by decide), v6 rgF (by decide)]
    refine ⟨by omega, by omega, by omega, by omega⟩
  have i7 := clr4_spec cap σ6 hc6
  obtain ⟨σ7, hσ7⟩ : ∃ y, y = (((σ6.setv rgNP 0).setv rgE 0).setv rgCD 0).setv rgF 0 := ⟨_, rfl⟩
  rw [← hσ7] at i7
  have g7 : ∀ r, r ≠ rgNP → r ≠ rgE → r ≠ rgCD → r ≠ rgF → r ≠ rgRWC → σ7.val r = τ.val r := by
    intro r r1 r2 r3 r4 r5
    rw [hσ7]
    simp only [WState.setv_val, Function.update_apply, if_neg r1, if_neg r2, if_neg r3, if_neg r4]
    exact v6 r r5
  have gp : σ7.val rgPAR = σ0.val rgPAR := by
    rw [g7 rgPAR (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5.oth rgPAR (by decide)
  obtain ⟨σ8, i8, p8, a8, t8, u8, s8, sh8, v8, c8⟩ := packA_spec cap σ7 (parB P zb t) (2 ^ t)
    (by rw [g7 rgACC (by decide) (by decide) (by decide) (by decide) (by decide), h5.acc, nb]; rfl)
    (by rw [g7 rgT (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5.tt)
    (by rw [g7 rgT2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5.t2)
    (by rw [g7 rgPW (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5.pwr)
    (by rw [gp]; omega) (by omega)
  obtain ⟨σ9, i9, p9, t9, u9, s9, sh9, v9, c9⟩ := dblPW_spec cap σ8 (2 ^ t) t8 u8
    (by rw [v8 rgPW (by decide) (by decide) (by decide), g7 rgPW (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h5.pwr) (by omega)
  have hc7 : σ6.val rgNP + σ6.val rgE + σ6.val rgCD + σ6.val rgF ≤ 5 * (P.b + 1) + 1 := by
    rw [v6 rgNP (by decide), v6 rgE (by decide), v6 rgCD (by decide), v6 rgF (by decide)]
    omega
  refine ⟨σ9, WExec.mono (WExec.seq i6 (WExec.seq i7 (WExec.seq i8 i9))) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v9 rgPAR (by decide) (by decide), p8, gp]
  · rw [p9, pow_succ]; ring
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, t9, u9, ?_, ?_⟩
    · rw [v9 rgNP (by decide) (by decide), v8 rgNP (by decide) (by decide) (by decide), hσ7]; simp
    · rw [v9 rgE (by decide) (by decide), v8 rgE (by decide) (by decide) (by decide), hσ7]; simp
    · rw [v9 rgCD (by decide) (by decide), v8 rgCD (by decide) (by decide) (by decide), hσ7]; simp
    · rw [v9 rgF (by decide) (by decide), v8 rgF (by decide) (by decide) (by decide), hσ7]; simp
    · rw [v9 rgACC (by decide) (by decide)]; exact a8
    · rw [v9 rgZ (by decide) (by decide), v8 rgZ (by decide) (by decide) (by decide),
        g7 rgZ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5.z
    · rw [v9 rgRWC (by decide) (by decide), v8 rgRWC (by decide) (by decide) (by decide), hσ7]; simp [r6]
    · rw [v9 rgKQ (by decide) (by decide), v8 rgKQ (by decide) (by decide) (by decide),
        g7 rgKQ (by decide) (by decide) (by decide) (by decide) (by decide), h5.kq]; simp
  · rw [sh9, sh8, hσ7]; simp [a6]
  · rw [s9, s8, hσ7]; simp [s6, h5.st]
  · intro i hi
    rw [sh9, sh8, hσ7]; simp [h6 i hi, h5.sh i hi]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hr
    rw [v9 r n2 n10, v8 r n1 n7 n10, g7 r n3 n4 n5 n6 n11]
    exact h5.oth r (by simp [n3, n4, n5, n6, n7, n8, n9, n10, n11, n12])
  · rw [c9, c8, hσ7]; simp [c6, h5.cell]

/-- **One parity bit**: the scan's set-up, the scan, its end. -/
def scan1 (R : Fin 4) : CM := .seq scanInit (.seq (p1Loop R) (scanFin R))

/-- One parity bit's steps. -/
def scanCost (b : ℕ) : ℕ := 300 * (b + 2) * (b + 2)

theorem scan1_spec (P : StarParams) (zb : ℕ → Bool) (t : ℕ) (ht : t < P.s) (R : Fin 4) (b0 : ℕ) (σ : CS)
    (hzb : ∀ m < dB P, readTapeBit (σ.st R) (b0 + 2 * m + 1) = zb m) (hR : σ.sh R = b0)
    (hpw : σ.val rgPW = 2 ^ t) (hb : σ.val rgB = P.b) (hz : Zero1 σ) (hpar : σ.val rgPAR < 2 ^ t)
    (hcap : 8 * (P.b + 2) ≤ cap) :
    ∃ τ, WExec cap (scan1 R) σ τ (scanCost P.b) ∧ τ.val rgPAR = σ.val rgPAR + (parB P zb t).toNat * 2 ^ t ∧
      τ.val rgPW = 2 ^ (t + 1) ∧ Zero1 τ ∧ τ.sh R = b0 ∧ τ.st = σ.st ∧ (∀ i, i ≠ R → τ.sh i = σ.sh i) ∧
      (∀ r, r ∉ [rgPAR, rgPW, rgNP, rgE, rgCD, rgF, rgACC, rgZ, rgT, rgT2, rgRWC, rgKQ] → τ.val r = σ.val r) ∧
      τ.cell = σ.cell := by
  obtain ⟨σ4, i4, hI0⟩ := scanInit_spec cap P zb t ht R b0 σ hR hpw hb hz hcap
  obtain ⟨σ5, i5, h5⟩ := p1Loop_spec cap P zb t ht R σ b0 hzb hcap P.b 0 σ4 (by omega) hI0
  obtain ⟨τ, i6, f1, f2, f3, f4, f5, f6, f7, f8⟩ := scanFin_spec cap P zb t ht R b0 σ σ5 h5 hpar hcap
  have hsq : 60 * (P.b + 2) + 1 + (P.b * (200 * (P.b + 2) + 2) + 1 + 1 + 100 * (P.b + 2)) ≤ scanCost P.b := by
    unfold scanCost; nlinarith
  exact ⟨τ, WExec.mono (WExec.seq i4 (WExec.seq i5 i6)) hsq, f1, f2, f3, f4, f5, f6, f7, f8⟩

end Par

end NearCubicWires.WireExponent3_5.PrimT.Ctr
