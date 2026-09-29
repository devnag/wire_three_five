import Proof.Wire_3_5.FinalPass.ThrPtRS19

/-! # S2 (THR per point), part 34: the cleanup (P3:3170-3178)

`cleanup`: `g`'s index moved back into `GREM` (the call's number `|𝒢|` restored), stage 2's accumulators, the
corner word's and the population's cells blanked, `DREM`, `KS` and the width cleared. **`cleanup_spec`**: from the
state the rows leave (`RowReady`), every scratch stream reads blank and every register but the accumulator is back
at entry. Paper quantity: none beyond the machine model (the per-point exit `PtOut`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem blank2 (n : ℕ) (l : List Bool) (hl : l.length ≤ n * [false, false].length + 1) :
    (List.replicate n [false, false]).flatten ++ false :: l.drop (n * [false, false].length + 1) =
      List.replicate (2 * n + 1) false := by
  rw [List.drop_eq_nil_of_le hl, show ([false, false] : List Bool) = List.replicate 2 false from rfl, flat_rep_false,
    List.replicate_succ', Nat.mul_comm]

theorem blank8 (n : ℕ) (l : List Bool) (hl : l.length ≤ n * (List.replicate 8 false).length + 1) :
    (List.replicate n (List.replicate 8 false)).flatten ++ false :: l.drop (n * (List.replicate 8 false).length + 1) =
      List.replicate (8 * n + 1) false := by
  rw [List.drop_eq_nil_of_le hl, flat_rep_false, List.replicate_succ', Nat.mul_comm]

/-- **The cleanup.** -/
def cleanup : TProg :=
  .seq (WM.move 6 109) (.seq ((fmtW [false, false]).liftW (fsU 10) (frU 116 115 117))
    (.seq ((fmtW [false, false]).liftW (fsU 11) (frU 116 115 117))
    (.seq ((fmtW (List.replicate 8 false)).liftW (fsU 12) (frU 116 115 114))
    (.seq ((fmtW [false, false]).liftW (fsU 14) (frU 116 115 114))
    (.seq (WM.clear 111) (.seq (WM.clear 114) (WM.clear 117)))))))

/-- The cleanup's step bound. -/
def cleanCost (G τ M H : ℕ) : ℕ :=
  (7 * G + 1) + 1 + (fmtCost H [false, false].length + 1 + (fmtCost H [false, false].length + 1 +
    (fmtCost M (List.replicate 8 false).length + 1 + (fmtCost M [false, false].length + 1 +
    ((3 * τ + 1) + 1 + ((3 * M + 1) + 1 + (3 * H + 1)))))))

variable (cap : ℕ)

theorem cleanup_spec (σB : WState 16 118) (t : TSt) (M τ G H : ℕ) (X : List Bool) (hR : RowReady t M τ X)
    (hXl : X.length = 4 * M) (hP : t.pos.length = 2 * H + 1) (hN : t.neg.length = 2 * H + 1) (hgi : t.gi = G)
    (hgR : t.gRem = 0) (hshB : ∀ j, σB.sh j = 0) (h117 : σB.val 117 = H)
    (hc : G + 2 * H + 8 * M + τ + 1 ≤ cap) :
    WExec cap cleanup (t.w σB) ({ t with
        gi := 0, gRem := G, pos := List.replicate (2 * H + 1) false, neg := List.replicate (2 * H + 1) false,
        x := List.replicate (8 * M + 1) false, z := List.replicate (2 * M + 1) false, dRem := 0,
        kS := 0 }.w (σB.setv 117 0)) (cleanCost G τ M H) := by
  obtain ⟨_, hhRw, hrwH, ⟨zr0, hz, hzr⟩, _, _, _, _, _, hdRem, hkS, hrS, _, _, hx⟩ := hR
  -- 1: `g`'s index back into `GREM`
  have e1 : WExec cap (WM.move 6 109) (t.w σB) ({ { t with gi := 0 } with gRem := t.gRem + t.gi }.w σB)
      (7 * G + 1) := by
    have e := wmove_spec cap (6 : Fin 118) 109 (by decide) G (t.w σB) (by rw [tw_val_gi, hgi])
      (by rw [tw_val_gi]; omega) (by rw [tw_val_gRem, tw_val_gi]; omega)
    rwa [tw_setv_gi, tw_val_gRem, tw_val_gi, tw_setv_gRem] at e
  obtain ⟨t1, ht1⟩ : ∃ s : TSt, s = { { t with gi := 0 } with gRem := t.gRem + t.gi } := ⟨_, rfl⟩
  rw [← ht1] at e1
  -- 2, 3: stage 2's accumulators blanked
  have e2 := fmtPos_spec cap σB t1 [false, false] H (hshB 10) (by subst ht1; exact hrwH) (by subst ht1; exact hrS)
    h117 (by simp; omega) (by omega)
  obtain ⟨t2, ht2⟩ : ∃ s : TSt, s = { t1 with
      pos := (List.replicate H [false, false]).flatten ++ false :: t1.pos.drop (H * [false, false].length + 1) } :=
    ⟨_, rfl⟩
  rw [← ht2] at e2
  have e3 := fmtNeg_spec cap σB t2 [false, false] H (hshB 11) (by subst ht2 ht1; exact hrwH)
    (by subst ht2 ht1; exact hrS) h117 (by simp; omega) (by omega)
  obtain ⟨t3, ht3⟩ : ∃ s : TSt, s = { t2 with
      neg := (List.replicate H [false, false]).flatten ++ false :: t2.neg.drop (H * [false, false].length + 1) } :=
    ⟨_, rfl⟩
  rw [← ht3] at e3
  -- 4, 5: the corner word's and the population's cells blanked
  have e4 := fmtX_spec cap σB t3 (List.replicate 8 false) M (hshB 12) (by subst ht3 ht2 ht1; exact hrwH)
    (by subst ht3 ht2 ht1; exact hrS) (by subst ht3 ht2 ht1; exact hkS) (by simp; omega) (by omega)
  obtain ⟨t4, ht4⟩ : ∃ s : TSt, s = { t3 with
      x := (List.replicate M (List.replicate 8 false)).flatten ++ false ::
        t3.x.drop (M * (List.replicate 8 false).length + 1) } := ⟨_, rfl⟩
  rw [← ht4] at e4
  have e5 := fmtZ_spec cap σB t4 [false, false] M (hshB 14) (by subst ht4 ht3 ht2 ht1; exact hrwH)
    (by subst ht4 ht3 ht2 ht1; exact hrS) (by subst ht4 ht3 ht2 ht1; exact hkS) (by simp; omega) (by omega)
  obtain ⟨t5, ht5⟩ : ∃ s : TSt, s = { t4 with
      z := (List.replicate M [false, false]).flatten ++ false :: t4.z.drop (M * [false, false].length + 1) } :=
    ⟨_, rfl⟩
  rw [← ht5] at e5
  -- 6, 7, 8: the counters and the width cleared
  have e6 : WExec cap (WM.clear 111) (t5.w σB) ({ t5 with dRem := 0 }.w σB) (3 * τ + 1) := by
    have h5 : t5.dRem = τ := by subst ht5 ht4 ht3 ht2 ht1; exact hdRem
    have e := wclear_spec cap (111 : Fin 118) τ (t5.w σB) (by rw [tw_val_dRem, h5]) (by rw [tw_val_dRem, h5]; omega)
    rwa [tw_setv_dRem] at e
  have e7 : WExec cap (WM.clear 114) ({ t5 with dRem := 0 }.w σB) ({ { t5 with dRem := 0 } with kS := 0 }.w σB)
      (3 * M + 1) := by
    have h5 : t5.kS = M := by subst ht5 ht4 ht3 ht2 ht1; exact hkS
    have e := wclear_spec cap (114 : Fin 118) M ({ t5 with dRem := 0 }.w σB) (by rw [tw_val_kS]; exact h5)
      (by rw [tw_val_kS]; show t5.kS ≤ cap; omega)
    rwa [tw_setv_kS] at e
  have e8 : WExec cap (WM.clear 117) ({ { t5 with dRem := 0 } with kS := 0 }.w σB)
      ({ { t5 with dRem := 0 } with kS := 0 }.w (σB.setv 117 0)) (3 * H + 1) := by
    have e := wclear_spec cap (117 : Fin 118) H ({ { t5 with dRem := 0 } with kS := 0 }.w σB)
      ((val117 σB _).trans h117) (by rw [val117, h117]; omega)
    rwa [tw_setv_117] at e
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) (tw_eq ?_) (by unfold cleanCost; omega)
  clear e1 e2 e3 e4 e5 e6 e7 e8
  have hxl : t.x.length ≤ M * (List.replicate 8 false).length + 1 := by
    rw [hx]; simp [hXl]; omega
  have hzl : t.z.length ≤ M * [false, false].length + 1 := by
    rw [hz]; simp [hzr]; omega
  have hPl : t.pos.length ≤ H * [false, false].length + 1 := by rw [hP]; simp; omega
  have hNl : t.neg.length ≤ H * [false, false].length + 1 := by rw [hN]; simp; omega
  subst ht5 ht4 ht3 ht2 ht1
  simp only [blank2 H t.pos hPl, blank2 H t.neg hNl, blank8 M t.x hxl, blank2 M t.z hzl, hgR, hgi, Nat.zero_add]

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
