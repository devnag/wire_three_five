import Proof.Wire_3_5.Primitive.SeedFix.CtrPass2

/-! # X3, part 9: the second pass of a block (P3:1206-1216)

"A fixed linear basis of each code gives polynomial-time encoding" (P3:1216): at a parity position `2^u − 1` the
second pass emits parity bit `u`, the low bit of the packed `rgPAR` (`halfW`), XOR the offset (`p2Par_spec`,
`enc_par`); `p2Mid_spec` joins the two branches; the loop over the block's `b` positions (`p2Loop_spec`) and
**`p2_spec`**: the block's `b` center coordinates `Tl[k0 + q]` emitted, the stream past the block's data bits.

Paper quantity of the main type: one block of the center `List.ofFn (centerAt P σ row col)` (P3:1206-1216). -/

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

section Pass2b
variable (cap : ℕ)

/-- A parity position of the second pass. -/
def p2Par : CM := .seq halfW (.seq (emitX rgBIT) (.seq (WM.clear rgBIT) (WM.move rgHQ rgPAR)))

theorem p2Par_spec (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (b0 c0 k0 : ℕ)
    (Tl offL Y0 : List Bool) (hH : P2H P zb R cnt σ0 b0 k0 Tl offL) (q : ℕ) (hq : q < P.b) (τ : CS)
    (hS : P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 q τ) (hP : PowT q (τ.val rgNP) (τ.val rgE)) (hE : τ.val rgE = 0)
    (hc2 : 2 * (k0 + P.b) + 2 ≤ cap) (hc3 : 8 * (P.b + 2) ≤ cap) :
    ∃ τ', WExec cap p2Par τ τ' (30 * (P.b + 4)) ∧ P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 (q + 1) τ' ∧
      τ'.val rgNP = τ.val rgNP ∧ τ'.val rgE = τ.val rgE ∧ τ'.val rgKQ = τ.val rgKQ := by
  obtain ⟨hRC, hRO, hcn⟩ := rc_ne hH.rc
  have hbs := P.b_succ
  have hpar : isPar P q = true := (powT_par P hq hP).2 hE
  obtain ⟨u, hu, he, hlt⟩ := hP
  have hqu : q + 1 = 2 ^ u := by omega
  have hus2 : 2 ^ u < 2 ^ P.s := by omega
  have hus : u < P.s := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hus2
  have hq' : q = 2 ^ u - 1 := by omega
  have hnpq : npar P q = u := by rw [hq']; exact npar_pow P u (le_of_lt hus)
  have hn : nd P (q + 1) = nd P q := by rw [nd_succ, if_pos hpar]; rfl
  have hnp : npar P (q + 1) = u + 1 := by rw [npar_succ, if_pos hpar, hnpq]
  have hdrop : (parL P zb).drop u = parB P zb u :: (parL P zb).drop (u + 1) := by
    rw [List.drop_eq_getElem_cons (by rw [parL_length]; exact hus)]
    simp [parL]
  have hpv : τ.val rgPAR = packB (parB P zb u :: (parL P zb).drop (u + 1)) := by rw [hS.par, hnpq, hdrop]
  have hpvlt : τ.val rgPAR < P.b + 1 := by
    rw [hS.par]; have := packB_drop_lt (parL P zb) (npar P q); rw [parL_length] at this; omega
  obtain ⟨τ1, e1, p1, bh1, bl1, hl1, s1, h1, v1, c1⟩ := halfW_spec cap (τ.val rgPAR) τ rfl (by rw [hS.bit]; omega)
    (by omega) (by rw [hS.hq]; omega) (by omega)
  rw [hS.hq, hS.bit] at bh1
  have hbit1 : τ1.val rgBIT = (parB P zb u).toNat := by
    have := packB_mod (parB P zb u) ((parL P zb).drop (u + 1)); rw [← hpv] at this; omega
  have hhq1 : τ1.val rgHQ = packB ((parL P zb).drop (u + 1)) := by
    have := packB_div (parB P zb u) ((parL P zb).drop (u + 1)); rw [← hpv] at this; omega
  have hout1 : OutAt Tl Y0 (k0 + q) τ1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [s1]; exact hS.out.st
    · rw [h1]; exact hS.out.sh
    · rw [v1 rgOC (by decide) (by decide) (by decide)]; exact hS.out.oc
    · rw [h1]; exact hS.out.osh
    · rw [v1 rgOFFC (by decide) (by decide) (by decide)]; exact hS.out.ofc
  obtain ⟨τ2, e2, out2, so2, st2, v2, c2⟩ := emit_step cap Tl offL Y0 (k0 + q) rgBIT (by decide) (by decide) τ1 hout1
    (by rw [s1, hS.st zOff (by decide), hH.off]) (by have := hH.ko; omega) (by have := hH.kt; omega)
    (parB P zb u) hbit1 (by rw [hH.tl q hq, hq', enc_par P zb u hus]) (by omega)
  have e3 := wclear_spec cap rgBIT (τ2.val rgBIT) τ2 rfl
    (by rw [v2 rgBIT (by decide) (by decide), hbit1]; have := Bool.toNat_le (parB P zb u); omega)
  have hq3 : (τ2.setv rgBIT 0).val rgHQ = packB ((parL P zb).drop (u + 1)) := by
    simp only [WState.setv_val, Function.update_apply]; simp only [show ¬((19 : Fin 26) = 20) by decide, if_false]
    rw [v2 rgHQ (by decide) (by decide), hhq1]
  have hp3 : (τ2.setv rgBIT 0).val rgPAR = 0 := by
    simp only [WState.setv_val, Function.update_apply]; simp only [show ¬((15 : Fin 26) = 20) by decide, if_false]
    rw [v2 rgPAR (by decide) (by decide), p1]
  have hql : packB ((parL P zb).drop (u + 1)) ≤ P.b := by
    have := packB_drop_lt (parL P zb) (u + 1); rw [parL_length] at this; omega
  have e4 := wmove_spec cap rgHQ rgPAR (by decide) ((τ2.setv rgBIT 0).val rgHQ) (τ2.setv rgBIT 0) rfl
    (by rw [hq3]; omega) (by rw [hq3, hp3]; omega)
  have g : ∀ r, r ≠ rgBIT → r ≠ rgHQ → r ≠ rgPAR → r ≠ rgOC → r ≠ rgOFFC →
      (((τ2.setv rgBIT 0).setv rgHQ 0).setv rgPAR ((τ2.setv rgBIT 0).val rgPAR + (τ2.setv rgBIT 0).val rgHQ)).val r =
        τ.val r := by
    intro r r1 r2 r3 r4 r5
    simp only [WState.setv_val, Function.update_apply, if_neg r1, if_neg r2, if_neg r3]
    rw [v2 r r4 r5, v1 r r3 r1 r2]
  have hbit2 : τ2.val rgBIT ≤ 1 := by
    rw [v2 rgBIT (by decide) (by decide), hbit1]; exact Bool.toNat_le _
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) (by rw [hq3]; omega), ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hset : ∀ (σ : CS) (x : ℕ), (σ.setv rgPAR x).val rgPAR = x := fun σ x => by simp
      rw [hset, hq3, hp3, hnp]; simp
    · rw [g rgZ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hS.z
    · simp [Function.update_apply]
    · simp [Function.update_apply]
    · rw [g rgT (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hS.tt
    · rw [g rgT2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hS.t2
    · simp only [WState.setv_sh]
      rw [(st2 R hRC hRO).2, h1, hS.shR, hn]
    · rw [g cnt (hcn rgBIT (by decide) (by decide)).symm (hcn rgHQ (by decide) (by decide)).symm
        (hcn rgPAR (by decide) (by decide)).symm (hcn rgOC (by decide) (by decide)).symm
        (hcn rgOFFC (by decide) (by decide)).symm, hS.cn, hn]
    · have e : k0 + (q + 1) = k0 + q + 1 := by ring
      rw [e]
      exact ⟨by simpa using out2.st, by simpa using out2.sh, by simpa using out2.oc, by simpa using out2.osh,
        by simpa using out2.ofc⟩
    · intro i hi
      simp only [WState.setv_st]
      by_cases h0 : i = zOff
      · subst h0; rw [so2, s1]; exact hS.st zOff (by decide)
      · rw [(st2 i hi h0).1, s1]; exact hS.st i hi
    · intro i i1 i2 i3
      simp only [WState.setv_sh]
      rw [(st2 i i1 i2).2, h1]; exact hS.sh i i1 i2 i3
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.2]
      exact hS.oth r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2])
    · simp only [WState.setv_cell]; rw [c2, c1]; exact hS.cell
  · rw [g rgNP (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [g rgE (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [g rgKQ (by decide) (by decide) (by decide) (by decide) (by decide)]

/-- One position of the second pass: data or parity. -/
def p2Mid (R : Fin 4) (cnt : Fin 26) : CM := .ifr rgE (p2Data R cnt) p2Par

theorem p2Mid_spec (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (b0 c0 k0 : ℕ)
    (Tl offL Y0 : List Bool) (hH : P2H P zb R cnt σ0 b0 k0 Tl offL) (q : ℕ) (hq : q < P.b) (τ : CS)
    (hS : P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 q τ) (hP : PowT q (τ.val rgNP) (τ.val rgE))
    (hc1 : c0 + 2 * dB P + 2 ≤ cap) (hc2 : 2 * (k0 + P.b) + 2 ≤ cap) (hc3 : 8 * (P.b + 2) ≤ cap) :
    ∃ τ', WExec cap (p2Mid R cnt) τ τ' (30 * (P.b + 4) + 71) ∧ P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 (q + 1) τ' ∧
      τ'.val rgNP = τ.val rgNP ∧ τ'.val rgE = τ.val rgE ∧ τ'.val rgKQ = τ.val rgKQ := by
  by_cases hE : τ.val rgE = 0
  · obtain ⟨τ', e, h1, h2, h3, h4⟩ := p2Par_spec cap P zb R cnt σ0 b0 c0 k0 Tl offL Y0 hH q hq τ hS hP hE hc2 hc3
    exact ⟨τ', WExec.mono (WExec.ifrF hE e) (by omega), h1, h2, h3, h4⟩
  · have hd : isPar P q = false := by
      cases h : isPar P q
      · rfl
      · exact absurd ((powT_par P hq hP).1 h) hE
    obtain ⟨τ', e, h1, h2, h3, h4⟩ := p2Data_spec cap P zb R cnt σ0 b0 c0 k0 Tl offL Y0 hH q hq τ hS hd hc1 hc2
    exact ⟨τ', WExec.mono (WExec.ifrT hE e) (by omega), h1, h2, h3, h4⟩

/-- The second pass's state survives changes to `rgNP`, `rgE`, `rgKQ`. -/
theorem P2S.congr {P : StarParams} {zb : ℕ → Bool} {R : Fin 4} {cnt : Fin 26} {σ0 : CS} {b0 c0 k0 : ℕ}
    {Tl offL Y0 : List Bool} (hH : P2H P zb R cnt σ0 b0 k0 Tl offL) {q : ℕ} {τ τ' : CS}
    (h : P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 q τ)
    (hv : ∀ r, r ≠ rgNP → r ≠ rgE → r ≠ rgKQ → τ'.val r = τ.val r) (hst : τ'.st = τ.st) (hsh : τ'.sh = τ.sh)
    (hc : τ'.cell = τ.cell) : P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 q τ' := by
  obtain ⟨hRC, hRO, hcn⟩ := rc_ne hH.rc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv rgPAR (by decide) (by decide) (by decide)]; exact h.par
  · rw [hv rgZ (by decide) (by decide) (by decide)]; exact h.z
  · rw [hv rgBIT (by decide) (by decide) (by decide)]; exact h.bit
  · rw [hv rgHQ (by decide) (by decide) (by decide)]; exact h.hq
  · rw [hv rgT (by decide) (by decide) (by decide)]; exact h.tt
  · rw [hv rgT2 (by decide) (by decide) (by decide)]; exact h.t2
  · rw [hsh]; exact h.shR
  · rw [hv cnt (hcn rgNP (by decide) (by decide)).symm (hcn rgE (by decide) (by decide)).symm
      (hcn rgKQ (by decide) (by decide)).symm]; exact h.cn
  · exact ⟨by rw [hst]; exact h.out.st, by rw [hsh]; exact h.out.sh,
      by rw [hv rgOC (by decide) (by decide) (by decide)]; exact h.out.oc, by rw [hsh]; exact h.out.osh,
      by rw [hv rgOFFC (by decide) (by decide) (by decide)]; exact h.out.ofc⟩
  · intro i hi; rw [hst]; exact h.st i hi
  · intro i i1 i2 i3; rw [hsh]; exact h.sh i i1 i2 i3
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hv r hr.2.1 hr.2.2.1 hr.1]
    exact h.oth r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2])
  · rw [hc]; exact h.cell

/-- One position of the second pass with the power tracker. -/
def p2Body (R : Fin 4) (cnt : Fin 26) : CM := .seq (p2Mid R cnt) powStep

/-- The second pass's loop. -/
def p2Loop (R : Fin 4) (cnt : Fin 26) : CM := .whr rgKQ (.seq (.dec rgKQ) (p2Body R cnt))

theorem p2_step (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (b0 c0 k0 : ℕ)
    (Tl offL Y0 : List Bool) (hH : P2H P zb R cnt σ0 b0 k0 Tl offL) (q : ℕ) (hq : q < P.b) (τ : CS)
    (hk : τ.val rgKQ = P.b - q) (hP : PowT q (τ.val rgNP) (τ.val rgE)) (hS : P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 q τ)
    (hc1 : c0 + 2 * dB P + 2 ≤ cap) (hc2 : 2 * (k0 + P.b) + 2 ≤ cap) (hc3 : 8 * (P.b + 2) ≤ cap) :
    ∃ τ', WExec cap (.seq (.dec rgKQ) (p2Body R cnt)) τ τ' (200 * (P.b + 2)) ∧ τ'.val rgKQ = P.b - (q + 1) ∧
      PowT (q + 1) (τ'.val rgNP) (τ'.val rgE) ∧ P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 (q + 1) τ' := by
  have e0 := WExec.dec (cap := cap) rgKQ τ (by rw [hk]; omega)
  obtain ⟨τ0, hτ0⟩ : ∃ y, y = τ.setv rgKQ (τ.val rgKQ - 1) := ⟨_, rfl⟩
  rw [← hτ0] at e0
  have hS0 : P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 q τ0 :=
    P2S.congr hH hS (fun r _ _ r3 => by rw [hτ0]; simp [Function.update_apply, r3]) (by rw [hτ0]; rfl)
      (by rw [hτ0]; rfl) (by rw [hτ0]; rfl)
  have hP0 : PowT q (τ0.val rgNP) (τ0.val rgE) := by rw [hτ0]; simpa using hP
  obtain ⟨τ1, e1, h1, n1, m1, k1⟩ := p2Mid_spec cap P zb R cnt σ0 b0 c0 k0 Tl offL Y0 hH q hq τ0 hS0 hP0 hc1 hc2 hc3
  obtain ⟨τ2, e2, p2, t2, u2, s2, sh2, v2, c2⟩ := powStep_spec cap τ1 q (by rw [n1, m1]; exact hP0)
    (by have := h1.tt; exact this) (h1.t2) (by omega)
  refine ⟨τ2, WExec.mono (WExec.seq e0 (WExec.seq e1 e2)) (by omega), ?_, p2, ?_⟩
  · rw [v2 rgKQ (by decide) (by decide), k1, hτ0]; simp [hk]; omega
  · exact P2S.congr hH h1 (fun r r1 r2 _ => v2 r r1 r2) s2 sh2 c2

theorem p2Loop_spec (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (b0 c0 k0 : ℕ)
    (Tl offL Y0 : List Bool) (hH : P2H P zb R cnt σ0 b0 k0 Tl offL)
    (hc1 : c0 + 2 * dB P + 2 ≤ cap) (hc2 : 2 * (k0 + P.b) + 2 ≤ cap) (hc3 : 8 * (P.b + 2) ≤ cap) :
    ∀ (m q : ℕ) (τ : CS), q + m = P.b → τ.val rgKQ = P.b - q → PowT q (τ.val rgNP) (τ.val rgE) →
      P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 q τ →
      ∃ τ', WExec cap (p2Loop R cnt) τ τ' (m * (200 * (P.b + 2) + 2) + 1) ∧ τ'.val rgKQ = 0 ∧
        PowT P.b (τ'.val rgNP) (τ'.val rgE) ∧ P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 P.b τ' := by
  intro m
  induction m with
  | zero =>
    intro q τ hqm hk hP hS
    have : q = P.b := by omega
    subst this
    exact ⟨τ, WExec.mono (WExec.whrF (by rw [hk]; omega)) (by omega), by rw [hk]; omega, hP, hS⟩
  | succ m ih =>
    intro q τ hqm hk hP hS
    obtain ⟨τ1, e1, k1, p1, s1⟩ := p2_step cap P zb R cnt σ0 b0 c0 k0 Tl offL Y0 hH q (by omega) τ hk hP hS hc1 hc2 hc3
    obtain ⟨τ2, e2, k2, p2, s2⟩ := ih (q + 1) τ1 (by omega) k1 p1 s1
    exact ⟨τ2, WExec.mono (WExec.whrT (by rw [hk]; omega) e1 e2) (by ring_nf; omega), k2, p2, s2⟩

end Pass2b

end NearCubicWires.WireExponent3_5.PrimT.Ctr
