import Proof.Wire_3_5.FinalPass.ThrPtRS15

/-! # S2 (THR per point), part 30: formatting, copying, measuring on the evaluator's layout

The one-stream pieces lifted exactly (`liftU_upd`): **`fmtWL_spec`** (stream `X` becomes `pat^n 0 ++ …`),
**`cpUL_spec`** (register `c` gains register `k`'s value), **`measUL_spec`** (register `k` gets the table's width).
`tw_setv_117`: register `117` (the width) belongs to the base. Paper quantity: none beyond the machine model. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem tw_setv_117 (σB : WState 16 118) (t : TSt) (v : ℕ) : (t.w σB).setv 117 v = t.w (σB.setv 117 v) := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 117
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl

variable (cap : ℕ)

theorem fmtWL_spec (X : Fin 17) (c r k : Fin 118) (hcr : c ≠ r) (hck : c ≠ k) (hrk : r ≠ k) (pat : List Bool) (n : ℕ)
    (ω : WState 16 118) (B : List Bool) (hs : ω.st X = B) (hh : ω.sh X = 0) (hc0 : ω.val c = 0) (hr0 : ω.val r = 0)
    (hk : ω.val k = n) (hc : n * pat.length + 1 ≤ cap) (hn : n ≤ cap) :
    WExec cap ((fmtW pat).liftW (fsU X) (frU c r k)) ω
      (ω.sets X ((List.replicate n pat).flatten ++ false :: B.drop (n * pat.length + 1))) (fmtCost n pat.length) := by
  have e := liftU_upd cap X c r k hcr hck hrk ω _ 0 0 0 n _
    (fmtW_spec cap pat n (toU ω X c r k) B hs hh hc0 hr0 hk hc hn)
  refine WExec.cast cap e ?_ le_rfl
  unfold ustOut
  apply WState.eq
  · funext j
    by_cases hj : j = X
    · subst hj; simp [hh]
    · simp [hj]
  · rfl
  · funext q
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

theorem cpUL_spec (X : Fin 17) (c r k : Fin 118) (hcr : c ≠ r) (hck : c ≠ k) (hrk : r ≠ k) (n : ℕ)
    (ω : WState 16 118) (hk : ω.val k = n) (hr : ω.val r = 0) (hc : ω.val c + n ≤ cap) (hn : 2 * n ≤ cap) :
    WExec cap (cpU.liftW (fsU X) (frU c r k)) ω (ω.setv c (ω.val c + n)) (7 * n + 1 + 1 + (n * 11 + 1)) := by
  have e := liftU_upd cap X c r k hcr hck hrk ω _ _ _ _ _ _ (cpU_spec cap (toU ω X c r k) n hk hr hc hn)
  refine WExec.cast cap e ?_ le_rfl
  unfold ustOut
  apply WState.eq
  · funext j
    by_cases hj : j = X
    · subst hj; simp [toU]
    · simp [hj]
  · funext j
    by_cases hj : j = X
    · subst hj; simp [toU]
    · simp [hj]
  · funext q
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> simp_all [toU]
  · rfl

theorem measUL_spec (X : Fin 17) (c r k : Fin 118) (hcr : c ≠ r) (hck : c ≠ k) (hrk : r ≠ k) (h : ℕ)
    (ω : WState 16 118) (hr : ∀ i < h, readTapeBit (ω.st X) (1 + 2 * i) = true)
    (hz : readTapeBit (ω.st X) (1 + 2 * h) = false) (hh : ω.sh X = 0) (hc : ω.val c = 0) (hk : ω.val k = 0)
    (hcap : 2 * h + 2 ≤ cap) :
    WExec cap (measU.liftW (fsU X) (frU c r k)) ω (ω.setv k h) (5 + 1 + (h * 17 + 1 + 1 + (5 * (1 + 2 * h) + 1))) := by
  have e := liftU_upd cap X c r k hcr hck hrk ω _ _ _ _ _ _ (measU_spec cap h (toU ω X c r k) hr hz hh hc hk hcap)
  refine WExec.cast cap e ?_ le_rfl
  unfold ustOut
  apply WState.eq
  · funext j
    by_cases hj : j = X
    · subst hj; simp [toU]
    · simp [hj]
  · funext j
    by_cases hj : j = X
    · subst hj; simp [toU]
    · simp [hj]
  · funext q
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> simp_all [toU]
  · rfl

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
