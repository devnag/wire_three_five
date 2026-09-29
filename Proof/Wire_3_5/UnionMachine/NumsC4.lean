import Proof.Wire_3_5.UnionMachine.NumsC3

/-! # NW phase (c), part 4: `rest_run` (the run after the front)

From `n` in `rN`, the mode bit in `rM`, every other register `0`, the head of `sIn` at `h ≤ T_f`: `rest_run` leaves
`e = n − k` in `rE`, `T_f = KT·(n+2)^{ZT}` in `rT`, every other register as before, the head at `0`, the streams and
the cell kept, within `restCost`.

Paper quantities of the main type: the shift `n − k` and the width `T_f` (P3:3044-3048, P3:1188-1189). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2

theorem g_mem (j : Fin 10) : g j ∈ rsC := (mem_rsC _).2 (Or.inr ⟨j, rfl⟩)

theorem zeroL_sh {ns nr : ℕ} (σ : WState ns nr) (rs : List (Fin nr)) : (zeroL σ rs).sh = σ.sh := rfl
theorem zeroL_st {ns nr : ℕ} (σ : WState ns nr) (rs : List (Fin nr)) : (zeroL σ rs).st = σ.st := rfl
theorem zeroL_cell {ns nr : ℕ} (σ : WState ns nr) (rs : List (Fin nr)) : (zeroL σ rs).cell = σ.cell := rfl
theorem sb_mem (j : Fin 20) : starBlk j ∈ rsC := (mem_rsC _).2 (Or.inl ⟨j, rfl⟩)

theorem rest_run (x cap cr KT ZT n h : ℕ) (P : Shared.StarParams) (hPn : P.n = n)
    (hrP : P.r = Ledger.rowBr cr P.n) (σ : St x) (vN : σ.val rN = n)
    (v0 : ∀ q, q ≠ rN → q ≠ rM → σ.val q = 0) (hh : σ.sh (sIn x) = h) (hZT : 1 ≤ ZT)
    (hTf : KT * (n + 2) ^ ZT ≤ cap) (hKT : 1 ≤ KT) (hhT : h ≤ KT * (n + 2) ^ ZT)
    (hcS : 4 * (n + 3) + 2 * cr + 20 ≤ cap) :
    ∃ c, WExec cap (restProg x cr KT ZT) σ
      (((σ.seth (sIn x) 0).setv rE (n - P.k)).setv rT (KT * (n + 2) ^ ZT)) c ∧
      c ≤ restCost n cr P.k KT ZT (KT * (n + 2) ^ ZT) := by
  obtain ⟨Tf, hTfd⟩ : ∃ v, v = KT * (n + 2) ^ ZT := ⟨_, rfl⟩
  rw [← hTfd] at hTf hhT ⊢
  have hpow : n + 2 ≤ (n + 2) ^ ZT := by
    calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ (n + 2) ^ ZT := Nat.pow_le_pow_right (by omega) hZT
  have hpj : ∀ j, j ≤ ZT → KT * (n + 2) ^ j ≤ Tf := fun j hj => by
    rw [hTfd]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hj)
  have hKTf : KT ≤ Tf := by have := hpj 0 (Nat.zero_le _); rwa [pow_zero, Nat.mul_one] at this
  have hn2 : n + 2 ≤ Tf := by
    rw [hTfd]
    calc n + 2 ≤ 1 * (n + 2) ^ ZT := by rw [one_mul]; exact hpow
      _ ≤ KT * (n + 2) ^ ZT := Nat.mul_le_mul_right _ hKT
  have hk : P.k ≤ n := hPn ▸ NumsX.rs_le P
  -- the register facts
  have nNM : rN ≠ rM := by decide
  have nNE : rN ≠ rE := by decide
  have nNT : rN ≠ rT := by decide
  have nME : rM ≠ rE := by decide
  have nMT : rM ≠ rT := by decide
  have nET : rE ≠ rT := by decide
  have e0 : RS 0 = rE := rfl
  have e1 : RS 1 = starBlk 9 := rfl
  have e2 : RS 2 = g 4 := rfl
  have e3 : RS 3 = g 5 := rfl
  have f0 : R6 0 = rT := rfl
  have f1 : R6 1 = g 6 := rfl
  have f2 : R6 2 = g 7 := rfl
  have f3 : R6 3 = g 4 := rfl
  have f4 : R6 4 = g 5 := rfl
  have f5 : R6 5 = g 9 := rfl
  -- 4: `starBlk 0 := n`
  have h4 := FinalPass.Hash4.wcopyR_spec cap rN (starBlk 0) (g 4) (sb_ne 0).1.symm (g_ne 4).1.symm (sb_g 0 4) σ
    (v0 _ (sb_ne 0).1 (sb_ne 0).2.1) (v0 _ (g_ne 4).1 (g_ne 4).2.1) (by rw [vN]; omega)
  rw [vN] at h4
  obtain ⟨σ4, hσ4⟩ : ∃ s, s = σ.setv (starBlk 0) n := ⟨_, rfl⟩
  rw [← hσ4] at h4
  have w4 : ∀ q, q ≠ starBlk 0 → σ4.val q = σ.val q := fun q hq => by rw [hσ4]; simp [hq]
  have w4S : σ4.val (starBlk 0) = n := by rw [hσ4]; simp
  -- 5: the star numbers
  have h5 := StarNums.starNums_spec cap cr 0 starBlk P hrP σ4 (by rw [w4S, hPn])
    (fun i hi => by rw [w4 _ (sb_inj hi)]; exact v0 _ (sb_ne i).1 (sb_ne i).2.1) (by rw [hPn]; omega)
  rw [hPn] at h5
  obtain ⟨σ5, hσ5⟩ : ∃ s, s = StarNums.starOut σ4 starBlk P 0 := ⟨_, rfl⟩
  rw [← hσ5] at h5
  have w5 : ∀ q, (∀ j, q ≠ starBlk j) → σ5.val q = σ.val q := fun q hq => by
    rw [hσ5, starOut_off _ _ _ _ _ hq, w4 _ (hq 0)]
  have w5k : σ5.val (starBlk 9) = P.k := by rw [hσ5]; exact starOut_k _ _ _ _
  have w5s : ∀ j, σ5.val (starBlk j) ≤ n + 2 := fun j => by
    rw [hσ5, ← hPn]
    exact starOut_small σ4 starBlk P (by rw [w4S, hPn])
      (fun i hi => by rw [w4 _ (sb_inj hi)]; exact v0 _ (sb_ne i).1 (sb_ne i).2.1) j
  have rN_nb : ∀ j, rN ≠ starBlk j := fun j => (sb_ne j).1.symm
  have rE_nb : ∀ j, rE ≠ starBlk j := fun j => (sb_ne j).2.2.1.symm
  have rT_nb : ∀ j, rT ≠ starBlk j := fun j => (sb_ne j).2.2.2.symm
  have g_nb : ∀ i j, g i ≠ starBlk j := fun i j => (sb_g j i).symm
  have w5N : σ5.val rN = n := by rw [w5 _ rN_nb, vN]
  have w5E : σ5.val rE = 0 := by rw [w5 _ rE_nb]; exact v0 _ nNE.symm nME.symm
  have w5T : σ5.val rT = 0 := by rw [w5 _ rT_nb]; exact v0 _ nNT.symm nMT.symm
  have w5g : ∀ j, σ5.val (g j) = 0 := fun j => by rw [w5 _ (g_nb j)]; exact v0 _ (g_ne j).1 (g_ne j).2.1
  -- 6: `rE := n`
  have h6 := FinalPass.Hash4.wcopyR_spec cap rN rE (g 4) nNE (g_ne 4).1.symm (g_ne 4).2.2.1.symm σ5 w5E (w5g 4)
    (by rw [w5N]; omega)
  rw [w5N] at h6
  obtain ⟨σ6, hσ6⟩ : ∃ s, s = σ5.setv rE n := ⟨_, rfl⟩
  rw [← hσ6] at h6
  -- 7: `rE := n − k`
  have h7 := UnaryArith.subW_spec cap RS σ6 (by rw [e2, hσ6]; simp [(g_ne 4).2.2.1, w5g])
    (by rw [e3, hσ6]; simp [(g_ne 5).2.2.1, w5g]) (by rw [e0, hσ6]; simp; omega)
    (by rw [e1, hσ6]; simp [(rE_nb 9).symm, w5k]; omega)
  have v6E : σ6.val rE = n := by rw [hσ6]; simp
  have v6k : σ6.val (starBlk 9) = P.k := by rw [hσ6]; simp [(rE_nb 9).symm, w5k]
  rw [e0, e1, v6E, v6k] at h7
  obtain ⟨σ7, hσ7⟩ : ∃ s, s = σ6.setv rE (n - P.k) := ⟨_, rfl⟩
  rw [← hσ7] at h7
  -- 8: `rT := KT`
  have v7T : σ7.val rT = 0 := by rw [hσ7, hσ6]; simp [nET.symm, w5T]
  have h8 := StarNums.incN_spec cap rT KT σ7 (by rw [v7T]; omega)
  rw [v7T, Nat.zero_add] at h8
  obtain ⟨σ8, hσ8⟩ : ∃ s, s = σ7.setv rT KT := ⟨_, rfl⟩
  rw [← hσ8] at h8
  -- 9, 10: `g 6 := n + 2`
  have v8N : σ8.val rN = n := by rw [hσ8, hσ7, hσ6]; simp [nNT, nNE, w5N]
  have v8g : ∀ j, σ8.val (g j) = 0 := fun j => by
    rw [hσ8, hσ7, hσ6]; simp [(g_ne j).2.2.2, (g_ne j).2.2.1, w5g]
  have h9 := FinalPass.Hash4.wcopyR_spec cap rN (g 6) (g 4) (g_ne 6).1.symm (g_ne 4).1.symm
    (g_inj (by decide)) σ8 (v8g 6) (v8g 4) (by rw [v8N]; omega)
  rw [v8N] at h9
  obtain ⟨σ9, hσ9⟩ : ∃ s, s = σ8.setv (g 6) n := ⟨_, rfl⟩
  rw [← hσ9] at h9
  have h10 := StarNums.incN_spec cap (g 6) 2 σ9 (by rw [hσ9]; simp; omega)
  have v9g6 : σ9.val (g 6) = n := by rw [hσ9]; simp
  rw [v9g6] at h10
  obtain ⟨σ10, hσ10⟩ : ∃ s, s = σ9.setv (g 6) (n + 2) := ⟨_, rfl⟩
  rw [← hσ10] at h10
  -- 11: `rT := KT·(n+2)^{ZT}`
  have v10 : ∀ j : Fin 10, j ≠ 6 → σ10.val (g j) = 0 := fun j hj => by
    rw [hσ10, hσ9]; simp [g_inj hj, v8g]
  have v10T : σ10.val rT = KT := by
    rw [hσ10, hσ9, hσ8]; simp [(g_ne 6).2.2.2.symm]
  have v10g6 : σ10.val (g 6) = n + 2 := by rw [hσ10]; simp
  obtain ⟨c11, h11, hc11⟩ := powN_spec cap R6 Tf hTf ZT σ10 (by rw [f2]; exact v10 7 (by decide))
    (by rw [f3]; exact v10 4 (by decide)) (by rw [f4]; exact v10 5 (by decide)) (by rw [f5]; exact v10 9 (by decide))
    (by rw [f1, v10g6]; omega) (fun j hj => by rw [f0, f1, v10T, v10g6]; exact hpj j hj)
  rw [f0, f1, v10T, v10g6, ← hTfd] at h11
  rw [f1, v10g6] at hc11
  obtain ⟨σ11, hσ11⟩ : ∃ s, s = σ10.setv rT Tf := ⟨_, rfl⟩
  rw [← hσ11] at h11
  -- 12: clear the block and the scratch
  have v11 : ∀ q, q ≠ rT → q ≠ g 6 → q ≠ rE → σ11.val q = σ5.val q := fun q h1 h2 h3 => by
    rw [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6]; simp [h1, h2, h3]
  have s11 : ∀ r ∈ rsC, σ11.val r ≤ n + 2 := fun r hr => by
    have hro := rsC_roles r hr
    by_cases hg6 : r = g 6
    · subst hg6; rw [hσ11]; simp [(g_ne 6).2.2.2, v10g6]
    · rw [v11 r hro.2.2.2.1 hg6 hro.2.2.1]
      rcases (mem_rsC r).1 hr with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact w5s j
      · rw [w5g]; omega
  obtain ⟨c12, h12, hc12⟩ := clearL_spec cap (n + 2) (by omega) rsC σ11 s11
  obtain ⟨σ12, hσ12⟩ : ∃ s, s = zeroL σ11 rsC := ⟨_, rfl⟩
  rw [← hσ12] at h12
  have rT_nr : rT ∉ rsC := fun hm => (rsC_roles _ hm).2.2.2.1 rfl
  have v12T : σ12.val rT = Tf := by rw [hσ12]; simp [zeroL, rT_nr, hσ11]
  have v12g : ∀ j, σ12.val (g j) = 0 := fun j => by rw [hσ12]; simp [zeroL, g_mem]
  -- 13, 14: `g 8 := T_f`, rewind
  have h13 := FinalPass.Hash4.wcopyR_spec cap rT (g 8) (g 4) (g_ne 8).2.2.2.symm (g_ne 4).2.2.2.symm
    (g_inj (by decide)) σ12 (v12g 8) (v12g 4) (by rw [v12T]; exact hTf)
  rw [v12T] at h13
  obtain ⟨σ13, hσ13⟩ : ∃ s, s = σ12.setv (g 8) Tf := ⟨_, rfl⟩
  rw [← hσ13] at h13
  have h14 := wrewind_spec cap (sIn x) (g 8) Tf σ13 (by rw [hσ13]; simp) (by rw [hσ13]; simp; exact hTf)
  -- the heads, streams, cell
  have so5 := starOut_st σ4 starBlk P 0
  rw [← hσ5] at so5
  have sh13 : σ13.sh = σ.sh := by
    simp only [hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, WState.setv_sh, zeroL_sh, so5.2.1, hσ4]
  have st13 : σ13.st = σ.st := by
    simp only [hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, WState.setv_st, zeroL_st, so5.1, hσ4]
  have ce13 : σ13.cell = σ.cell := by
    simp only [hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, WState.setv_cell, zeroL_cell, so5.2.2, hσ4]
  refine ⟨_, WExec.cast cap (WExec.seq h4 (WExec.seq h5 (WExec.seq h6 (WExec.seq h7 (WExec.seq h8 (WExec.seq h9
    (WExec.seq h10 (WExec.seq h11 (WExec.seq h12 (WExec.seq h13 h14)))))))))) ?_ le_rfl, ?_⟩
  · apply WState.eq
    · rw [WState.seth_sh, WState.setv_sh, sh13, hh]
      funext i
      simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> omega
    · simp only [WState.seth_st, WState.setv_st, st13]
    · funext q
      simp only [WState.seth_val, WState.setv_val, Function.update_apply]
      by_cases hq : q ∈ rsC
      · have hro := rsC_roles q hq
        simp only [hro.2.2.2.1, hro.2.2.1, if_false]
        rw [v0 q hro.1 hro.2.1]
        by_cases hq8 : q = g 8
        · simp [hq8]
        · rw [if_neg hq8, hσ13, hσ12]
          simp [zeroL, hq8, hq]
      · have hg8 : q ≠ g 8 := fun e => hq (e ▸ g_mem 8)
        have hg6 : q ≠ g 6 := fun e => hq (e ▸ g_mem 6)
        have hnb : ∀ j, q ≠ starBlk j := fun j e => hq (e ▸ sb_mem j)
        simp only [hg8, if_false]
        rw [hσ13, hσ12]
        simp only [zeroL, WState.setv_val, Function.update_apply, hg8, hq, if_false]
        by_cases hqT : q = rT
        · subst hqT; simp [hσ11]
        · by_cases hqE : q = rE
          · subst hqE
            rw [hσ11, hσ10, hσ9, hσ8, hσ7]
            simp [nET, (g_ne 6).2.2.1.symm]
          · simp only [hqT, hqE, if_false]
            rw [v11 q hqT hg6 hqE, w5 q hnb]
    · simp only [WState.seth_cell, WState.setv_cell, ce13]
  · unfold restCost
    have := hc11
    have := hc12
    omega

end NearCubicWires.WireExponent3_5.UnionMachine.NumsC
