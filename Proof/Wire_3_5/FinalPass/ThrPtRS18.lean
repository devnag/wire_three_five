import Proof.Wire_3_5.FinalPass.ThrPtRS17

/-! # S2 (THR per point), part 32: the setup's and cleanup's steps on the working state

Each step on `t.w σB`: **`cpD_spec`** (`DREM += τ₀`), **`cpK_spec`** (`KS += |occs|`), **`measT_spec`** (the width
`h` into the base's register `117`), **`fmtPos_spec`**, **`fmtNeg_spec`** (stage 2's accumulators formatted or blanked,
count `h`), **`fmtX_spec`**, **`fmtZ_spec`** (the corner word's and the population's cells, count `|occs|`), and
**`cwStep_spec`** (stage 2 writes the corner word `X` when `a ≠ 0`; with `a = 0` there are no occurrences and `X = []`).
Paper quantity: the corner word of the occurrences at the point (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable (cap : ℕ) (σB : WState 16 118)

theorem cpD_spec (t : TSt) (τ : ℕ) (h8 : σB.val 8 = τ) (ht : t.tmp = 0) (hc : t.dRem + τ ≤ cap) (hn : 2 * τ ≤ cap) :
    WExec cap (cpU.liftW (fsU 15) (frU 111 113 8)) (t.w σB) ({ t with dRem := t.dRem + τ }.w σB)
      (7 * τ + 1 + 1 + (τ * 11 + 1)) := by
  have e := cpUL_spec cap 15 111 113 8 (by decide) (by decide) (by decide) τ (t.w σB)
    ((tw_val_low σB t 8 (by decide) (by decide) (by decide) (by decide)).trans h8) ((tw_val_tmp σB t).trans ht)
    (by rw [tw_val_dRem]; exact hc) hn
  rwa [tw_val_dRem, tw_setv_dRem] at e

theorem cpK_spec (t : TSt) (M : ℕ) (h63 : σB.val 63 = M) (ht : t.tmp = 0) (hc : t.kS + M ≤ cap) (hn : 2 * M ≤ cap) :
    WExec cap (cpU.liftW (fsU 15) (frU 114 113 63)) (t.w σB) ({ t with kS := t.kS + M }.w σB)
      (7 * M + 1 + 1 + (M * 11 + 1)) := by
  have e := cpUL_spec cap 15 114 113 63 (by decide) (by decide) (by decide) M (t.w σB)
    ((tw_val_other σB t 63 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h63)
    ((tw_val_tmp σB t).trans ht) (by rw [tw_val_kS]; exact hc) hn
  rwa [tw_val_kS, tw_setv_kS] at e

theorem val117 (t : TSt) : (t.w σB).val 117 = σB.val 117 :=
  tw_val_other σB t 117 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem measT_spec (t : TSt) (H : ℕ) (hr : ∀ i < H, readTapeBit (σB.st 3) (1 + 2 * i) = true)
    (hz : readTapeBit (σB.st 3) (1 + 2 * H) = false) (hsh : σB.sh 3 = 0) (hp : t.prH = 0) (h117 : σB.val 117 = 0)
    (hcap : 2 * H + 2 ≤ cap) :
    WExec cap (measU.liftW (fsU 3) (frU 110 115 117)) (t.w σB) (t.w (σB.setv 117 H))
      (5 + 1 + (H * 17 + 1 + 1 + (5 * (1 + 2 * H) + 1))) := by
  have e := measUL_spec cap 3 110 115 117 (by decide) (by decide) (by decide) H (t.w σB)
    (fun i hi => by rw [tw_st_other σB t 3 (by decide)]; exact hr i hi)
    (by rw [tw_st_other σB t 3 (by decide)]; exact hz)
    ((tw_sh_other σB t 3 (by decide) (by decide) (by decide)).trans hsh) ((tw_val_prH σB t).trans hp)
    ((val117 σB t).trans h117) hcap
  rwa [tw_setv_117] at e

theorem fmtPos_spec (t : TSt) (pat : List Bool) (n : ℕ) (hsh : σB.sh 10 = 0) (hc0 : t.rwH = 0) (hr0 : t.rS = 0)
    (hk : σB.val 117 = n) (hc : n * pat.length + 1 ≤ cap) (hn : n ≤ cap) :
    WExec cap ((fmtW pat).liftW (fsU 10) (frU 116 115 117)) (t.w σB)
      ({ t with pos := (List.replicate n pat).flatten ++ false :: t.pos.drop (n * pat.length + 1) }.w σB)
      (fmtCost n pat.length) := by
  have e := fmtWL_spec cap 10 116 115 117 (by decide) (by decide) (by decide) pat n (t.w σB) t.pos (tw_st_pos σB t)
    ((tw_sh_other σB t 10 (by decide) (by decide) (by decide)).trans hsh) ((tw_val_rwH σB t).trans hc0)
    ((tw_val_rS σB t).trans hr0) ((val117 σB t).trans hk) hc hn
  rwa [tw_sets_pos] at e

theorem fmtNeg_spec (t : TSt) (pat : List Bool) (n : ℕ) (hsh : σB.sh 11 = 0) (hc0 : t.rwH = 0) (hr0 : t.rS = 0)
    (hk : σB.val 117 = n) (hc : n * pat.length + 1 ≤ cap) (hn : n ≤ cap) :
    WExec cap ((fmtW pat).liftW (fsU 11) (frU 116 115 117)) (t.w σB)
      ({ t with neg := (List.replicate n pat).flatten ++ false :: t.neg.drop (n * pat.length + 1) }.w σB)
      (fmtCost n pat.length) := by
  have e := fmtWL_spec cap 11 116 115 117 (by decide) (by decide) (by decide) pat n (t.w σB) t.neg (tw_st_neg σB t)
    ((tw_sh_other σB t 11 (by decide) (by decide) (by decide)).trans hsh) ((tw_val_rwH σB t).trans hc0)
    ((tw_val_rS σB t).trans hr0) ((val117 σB t).trans hk) hc hn
  rwa [tw_sets_neg] at e

theorem fmtX_spec (t : TSt) (pat : List Bool) (n : ℕ) (hsh : σB.sh 12 = 0) (hc0 : t.rwH = 0) (hr0 : t.rS = 0)
    (hk : t.kS = n) (hc : n * pat.length + 1 ≤ cap) (hn : n ≤ cap) :
    WExec cap ((fmtW pat).liftW (fsU 12) (frU 116 115 114)) (t.w σB)
      ({ t with x := (List.replicate n pat).flatten ++ false :: t.x.drop (n * pat.length + 1) }.w σB)
      (fmtCost n pat.length) := by
  have e := fmtWL_spec cap 12 116 115 114 (by decide) (by decide) (by decide) pat n (t.w σB) t.x (tw_st_x σB t)
    ((tw_sh_other σB t 12 (by decide) (by decide) (by decide)).trans hsh) ((tw_val_rwH σB t).trans hc0)
    ((tw_val_rS σB t).trans hr0) ((tw_val_kS σB t).trans hk) hc hn
  rwa [tw_sets_x] at e

theorem fmtZ_spec (t : TSt) (pat : List Bool) (n : ℕ) (hsh : σB.sh 14 = 0) (hc0 : t.rwH = 0) (hr0 : t.rS = 0)
    (hk : t.kS = n) (hc : n * pat.length + 1 ≤ cap) (hn : n ≤ cap) :
    WExec cap ((fmtW pat).liftW (fsU 14) (frU 116 115 114)) (t.w σB)
      ({ t with z := (List.replicate n pat).flatten ++ false :: t.z.drop (n * pat.length + 1) }.w σB)
      (fmtCost n pat.length) := by
  have e := fmtWL_spec cap 14 116 115 114 (by decide) (by decide) (by decide) pat n (t.w σB) t.z (tw_st_z σB t)
    ((tw_sh_other σB t 14 (by decide) (by decide) (by decide)).trans hsh) ((tw_val_rwH σB t).trans hc0)
    ((tw_val_rS σB t).trans hr0) ((tw_val_kS σB t).trans hk) hc hn
  rwa [tw_sets_z] at e

/-- Stage 2 lifted onto the layout. -/
def cwT : TProg := Corner.cw.liftW fsC frC

theorem cwStep_spec (t : TSt) (a M H : ℕ) {n : ℕ} (Gs : List (NormalizedThresholdGate n)) (c u v : BitInput n)
    (hsh : ∀ j, σB.sh j = 0) (h5 : σB.val 5 = a)
    (hzero : ∀ q : Fin 118, 102 ≤ q.val → q.val ≤ 108 → σB.val q = 0)
    (hGs : a ≠ 0 → σB.st 3 = Corner.gatesW H Gs) (ha0 : a = 0 → Gs = []) (hGM : Gs.length = M)
    (hC : σB.st 0 = frame (List.ofFn c)) (hU : σB.st 1 = frame (List.ofFn u)) (hV : σB.st 2 = frame (List.ofFn v))
    (hov : ∀ g ∈ Gs, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ H ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ H)
    (hpos : t.pos = (List.replicate H [true, false]).flatten ++ [false])
    (hneg : t.neg = (List.replicate H [true, false]).flatten ++ [false])
    (hx : t.x = List.replicate (8 * M) false ++ [false])
    (hc : 1 ≤ cap) (hR : 2 * H ≤ cap) (hnc : 2 * n ≤ cap) (hK : M * (1 + (n + 1) * (2 * (2 * H + 1))) ≤ cap)
    (ho : 8 * M ≤ cap) :
    ∃ P N : List Bool, P.length = 2 * H + 1 ∧ N.length = 2 * H + 1 ∧
      WExec cap (.ifr 5 cwT .skip) (t.w σB)
        ({ t with
          pos := P, neg := N,
          x := frameP (Pop.cornerWord (Gs.map NormalizedThresholdGate.eval) c u v) ++ [false] }.w σB)
        (Corner.cwCost H n M + 1) := by
  have hl : ((List.replicate H [true, false]).flatten ++ [false]).length = 2 * H + 1 := by
    rw [List.length_append, flat_len]; simp; ring
  by_cases ha : a = 0
  · have hG0 := ha0 ha
    subst hG0
    have hM0 : M = 0 := by simp at hGM; omega
    refine ⟨t.pos, t.neg, by rw [hpos, hl], by rw [hneg, hl], ?_⟩
    have e := WExec.ifrF (cap := cap) (P := cwT) (show (t.w σB).val 5 = 0 by
      rw [tw_val_low σB t 5 (by decide) (by decide) (by decide) (by decide), h5, ha]) (WExec.skip (cap := cap) (t.w σB))
    have hx' : t.x = frameP (Pop.cornerWord (([] : List (NormalizedThresholdGate n)).map
        NormalizedThresholdGate.eval) c u v) ++ [false] := by
      rw [hx, hM0]; rfl
    refine WExec.mono (WExec.cast cap e (tw_eq ?_) le_rfl) (by omega)
    rw [← hx']
  · have hG := hGs ha
    obtain ⟨A', B', e⟩ := cwL_spec cap H Gs c u v 0 0 [] [] [] [] [false] [false] [] (List.replicate (8 * M) false)
      (t.w σB) (by rw [tw_st_other σB t 3 (by decide), hG, List.append_nil])
      ((tw_sh_other σB t 3 (by decide) (by decide) (by decide)).trans (hsh 3))
      (by rw [tw_st_other σB t 3 (by decide), hG, gatesW_len])
      (by rw [tw_st_other σB t 0 (by decide), hC, frame_len]) (by rw [tw_st_other σB t 1 (by decide), hU, frame_len])
      (by rw [tw_st_other σB t 2 (by decide), hV, frame_len]) (by rw [tw_st_pos, hpos, binary_zero, frameP_rep])
      (by rw [tw_st_neg, hneg, binary_zero, frameP_rep]) (by rw [tw_st_x, hx]) (by rw [List.length_replicate, hGM])
      ((tw_sh_other σB t 0 (by decide) (by decide) (by decide)).trans (hsh 0))
      ((tw_sh_other σB t 1 (by decide) (by decide) (by decide)).trans (hsh 1))
      ((tw_sh_other σB t 2 (by decide) (by decide) (by decide)).trans (hsh 2))
      ((tw_sh_other σB t 10 (by decide) (by decide) (by decide)).trans (hsh 10))
      ((tw_sh_other σB t 11 (by decide) (by decide) (by decide)).trans (hsh 11))
      ((tw_sh_other σB t 12 (by decide) (by decide) (by decide)).trans (hsh 12))
      (fun k h1 h2 => (tw_val_mid σB t k (by omega) h2).trans (hzero k h1 h2)) hc hR hnc (by rw [hGM]; exact hK)
      (by rw [hGM]; exact ho) hov
    rw [tw_sets_pos, tw_sets_neg, tw_sets_x, hGM] at e
    refine ⟨frameP (RepairOrdinary.SignedSortKey.binary H A') ++ false :: [],
      frameP (RepairOrdinary.SignedSortKey.binary H B') ++ false :: [], by simp [Corner.binary_length'],
      by simp [Corner.binary_length'], ?_⟩
    exact WExec.cast cap (WExec.ifrT (show (t.w σB).val 5 ≠ 0 by
      rw [tw_val_low σB t 5 (by decide) (by decide) (by decide) (by decide), h5]; exact ha) e) (tw_eq rfl) le_rfl

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
