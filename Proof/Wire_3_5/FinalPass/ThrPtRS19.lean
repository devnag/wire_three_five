import Proof.Wire_3_5.FinalPass.ThrPtRS18

/-! # S2 (THR per point), part 33: the setup (P3:3170-3178)

`tInit G`: the working state at entry (`GREM = |𝒢|` is the call's number, everything else zero, the scratch empty).
`setup`: `DREM := τ₀`, `KS := |occs|`, the width `h` measured, stage 2's accumulators formatted `(1 0)^h 0`, the
corner word's cells `0^{8|occs|+1}`, stage 2 (when `a ≠ 0`), the population's cells `0^{2|occs|+1}`.
**`setup_spec`**: the state after it, over the base with `h` in register `117`: the corner word
`frameP X ++ [false]` of the occurrences at the point in place, ready for the rows. Paper quantity: the occurrences'
corner word `X` (P3:3170-3178, `occCorners`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The working state at entry. -/
def tInit (G : ℕ) : TSt :=
  { acc := 0, gi := 0, p := 0, d := 0, r82 := 0, w92 := 0, gRem := G, prH := 0, dRem := 0, rH := 0, tmp := 0,
    kS := 0, rS := 0, rwH := 0, hPr := 0, hRw := 0, hRep := 0, pos := [], neg := [], x := [], rw := [], z := [],
    ss := [], rep := [] }

/-- **The setup.** -/
def setup : TProg :=
  .seq (cpU.liftW (fsU 15) (frU 111 113 8)) (.seq (cpU.liftW (fsU 15) (frU 114 113 63))
    (.seq (measU.liftW (fsU 3) (frU 110 115 117)) (.seq ((fmtW [true, false]).liftW (fsU 10) (frU 116 115 117))
    (.seq ((fmtW [true, false]).liftW (fsU 11) (frU 116 115 117))
    (.seq ((fmtW (List.replicate 8 false)).liftW (fsU 12) (frU 116 115 114))
    (.seq (.ifr 5 cwT .skip) ((fmtW [false, false]).liftW (fsU 14) (frU 116 115 114))))))))

/-- The setup's step bound (`cwc`: stage 2's). -/
def setupCost (τ M H cwc : ℕ) : ℕ :=
  (7 * τ + 1 + 1 + (τ * 11 + 1)) + 1 + ((7 * M + 1 + 1 + (M * 11 + 1)) + 1 +
    ((5 + 1 + (H * 17 + 1 + 1 + (5 * (1 + 2 * H) + 1))) + 1 + (fmtCost H [true, false].length + 1 +
    (fmtCost H [true, false].length + 1 + (fmtCost M (List.replicate 8 false).length + 1 +
    ((cwc + 1) + 1 + fmtCost M [false, false].length))))))

theorem z_fmt (M k : ℕ) :
    (List.replicate M [false, false]).flatten ++ false :: ([] : List Bool).drop k = List.replicate (2 * M + 1) false := by
  rw [show ([false, false] : List Bool) = List.replicate 2 false from rfl, flat_rep_false, List.drop_nil,
    List.replicate_succ', Nat.mul_comm]

variable (cap : ℕ)

theorem setup_spec (σ0 : WState 16 118) (a G τ M H : ℕ) {n : ℕ} (Gs : List (NormalizedThresholdGate n))
    (c u v : BitInput n) (hsh : ∀ j, σ0.sh j = 0) (h5 : σ0.val 5 = a) (h8 : σ0.val 8 = τ) (h63 : σ0.val 63 = M)
    (h117 : σ0.val 117 = 0) (hzero : ∀ q : Fin 118, 102 ≤ q.val → q.val ≤ 108 → σ0.val q = 0)
    (hmeas : ∀ i < H, readTapeBit (σ0.st 3) (1 + 2 * i) = true) (hmz : readTapeBit (σ0.st 3) (1 + 2 * H) = false)
    (hGs : a ≠ 0 → σ0.st 3 = Corner.gatesW H Gs) (ha0 : a = 0 → Gs = []) (hGM : Gs.length = M)
    (hC : σ0.st 0 = frame (List.ofFn c)) (hU : σ0.st 1 = frame (List.ofFn u)) (hV : σ0.st 2 = frame (List.ofFn v))
    (hov : ∀ g ∈ Gs, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ H ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ H)
    (hc1 : 2 * τ + 10 * M + 2 * H + 2 ≤ cap) (hcn : 2 * n ≤ cap)
    (hcK : M * (1 + (n + 1) * (2 * (2 * H + 1))) ≤ cap) :
    ∃ P N : List Bool, P.length = 2 * H + 1 ∧ N.length = 2 * H + 1 ∧
      WExec cap setup ((tInit G).w σ0) ({ tInit G with
          dRem := τ, kS := M, pos := P, neg := N,
          x := frameP (Pop.cornerWord (Gs.map NormalizedThresholdGate.eval) c u v) ++ [false],
          z := List.replicate (2 * M + 1) false }.w (σ0.setv 117 H)) (setupCost τ M H (Corner.cwCost H n M)) := by
  have e1 := cpD_spec cap σ0 (tInit G) τ h8 rfl (by show 0 + τ ≤ cap; omega) (by omega)
  obtain ⟨t1, ht1⟩ : ∃ s : TSt, s = { tInit G with dRem := (tInit G).dRem + τ } := ⟨_, rfl⟩
  rw [← ht1] at e1
  have e2 := cpK_spec cap σ0 t1 M h63 (by subst ht1; rfl) (by subst ht1; show 0 + M ≤ cap; omega) (by omega)
  obtain ⟨t2, ht2⟩ : ∃ s : TSt, s = { t1 with kS := t1.kS + M } := ⟨_, rfl⟩
  rw [← ht2] at e2
  have e3 := measT_spec cap σ0 t2 H hmeas hmz (hsh 3) (by subst ht2 ht1; rfl) h117 (by omega)
  obtain ⟨σB, hσB⟩ : ∃ s, s = σ0.setv 117 H := ⟨_, rfl⟩
  rw [← hσB] at e3
  have hshB : ∀ j, σB.sh j = 0 := fun j => by rw [hσB]; exact hsh j
  have hB117 : σB.val 117 = H := by rw [hσB]; simp
  have e4 := fmtPos_spec cap σB t2 [true, false] H (hshB 10) (by subst ht2 ht1; rfl) (by subst ht2 ht1; rfl) hB117
    (by simp; omega) (by omega)
  obtain ⟨t3, ht3⟩ : ∃ s : TSt, s = { t2 with
      pos := (List.replicate H [true, false]).flatten ++ false :: t2.pos.drop (H * [true, false].length + 1) } :=
    ⟨_, rfl⟩
  rw [← ht3] at e4
  have e5 := fmtNeg_spec cap σB t3 [true, false] H (hshB 11) (by subst ht3 ht2 ht1; rfl) (by subst ht3 ht2 ht1; rfl)
    hB117 (by simp; omega) (by omega)
  obtain ⟨t4, ht4⟩ : ∃ s : TSt, s = { t3 with
      neg := (List.replicate H [true, false]).flatten ++ false :: t3.neg.drop (H * [true, false].length + 1) } :=
    ⟨_, rfl⟩
  rw [← ht4] at e5
  have e6 := fmtX_spec cap σB t4 (List.replicate 8 false) M (hshB 12) (by subst ht4 ht3 ht2 ht1; rfl)
    (by subst ht4 ht3 ht2 ht1; rfl) (by subst ht4 ht3 ht2 ht1; show 0 + M = M; omega) (by simp; omega) (by omega)
  obtain ⟨t5, ht5⟩ : ∃ s : TSt, s = { t4 with
      x := (List.replicate M (List.replicate 8 false)).flatten ++ false ::
        t4.x.drop (M * (List.replicate 8 false).length + 1) } := ⟨_, rfl⟩
  rw [← ht5] at e6
  obtain ⟨P, N, hP, hN, e7⟩ := cwStep_spec cap σB t5 a M H Gs c u v hshB (by rw [hσB]; simp [h5])
    (fun q h1 h2 => by
      rw [hσB, WState.setv_val, Function.update_of_ne (fun h => by subst h; simp at h2)]
      exact hzero q h1 h2)
    (fun ha => by rw [hσB]; exact hGs ha) ha0 hGM (by rw [hσB]; exact hC) (by rw [hσB]; exact hU)
    (by rw [hσB]; exact hV) hov
    (by subst ht5 ht4 ht3 ht2 ht1; show _ ++ false :: ([] : List Bool).drop _ = _; rw [List.drop_nil])
    (by subst ht5 ht4 ht3 ht2 ht1; show _ ++ false :: ([] : List Bool).drop _ = _; rw [List.drop_nil])
    (by subst ht5 ht4 ht3 ht2 ht1
        show (List.replicate M (List.replicate 8 false)).flatten ++ false :: ([] : List Bool).drop _ = _
        rw [flat_rep_false, List.drop_nil, Nat.mul_comm])
    (by omega) (by omega) hcn hcK (by omega)
  obtain ⟨t6, ht6⟩ : ∃ s : TSt, s = { t5 with
      pos := P, neg := N, x := frameP (Pop.cornerWord (Gs.map NormalizedThresholdGate.eval) c u v) ++ [false] } :=
    ⟨_, rfl⟩
  rw [← ht6] at e7
  have e8 := fmtZ_spec cap σB t6 [false, false] M (hshB 14) (by subst ht6 ht5 ht4 ht3 ht2 ht1; rfl)
    (by subst ht6 ht5 ht4 ht3 ht2 ht1; rfl) (by subst ht6 ht5 ht4 ht3 ht2 ht1; show 0 + M = M; omega)
    (by simp; omega) (by omega)
  refine ⟨P, N, hP, hN, ?_⟩
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_ (by unfold setupCost; omega)
  clear e1 e2 e3 e4 e5 e6 e7 e8
  subst hσB
  apply tw_eq
  subst ht6 ht5 ht4 ht3 ht2 ht1
  simp only [tInit, TSt.mk.injEq, true_and, and_true, Nat.zero_add, z_fmt]

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
