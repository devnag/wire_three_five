import Proof.Wire_3_5.FinalPass.SdG4

/-! # S4 (the seeds phase), part 45: the seed loop's cost, per seed and per point (P3:3170-3178)

The seed loop's step bound `slCost` over the seeds `es` splits as `|es|·tab + |es|·(2^{dRow}·2^{dR}·L)·pt + 1`
(**`slCost_le`**): per seed `tabB` (the tables' copies, the saved position's moves, the counters' last steps), per
point `ptB` (the pair's decoding, the mask, the evaluator, the accumulation; the center's own steps and the counters'
per-cell and per-row steps, charged to the cell's first point since `L ≥ 1`). Every seed costs the same
(`sbCost_indep`: the tables' lengths do not depend on the seed, `tab_len`).

Paper quantity of the main type: the seeds phase's cost shape `|E|·tab + (|centers|·|E|·Q)·pt` (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR)

theorem cntCost_eq (d T cb : ℕ) : cntCost d T cb = cb + cntCost d T 0 := by unfold cntCost; omega

theorem key_le (x y L a b c : ℕ) (hy : 1 ≤ y) (hL : 1 ≤ L) :
    x * (y * (L * a + b) + c) ≤ x * y * L * (a + b + c) := by
  have h1 : x * y * b ≤ x * y * L * b := by
    have := Nat.mul_le_mul_left (x * y) (Nat.le_mul_of_pos_left b hL)
    calc x * y * b ≤ x * y * (L * b) := this
      _ = x * y * L * b := by ring
  have h2 : x * c ≤ x * y * L * c := by
    have hyL : 0 < y * L := Nat.mul_pos (by omega) (by omega)
    have := Nat.mul_le_mul_left x (Nat.le_mul_of_pos_left c hyL)
    calc x * c ≤ x * (y * L * c) := this
      _ = x * y * L * c := by ring
  have e1 : x * (y * (L * a + b) + c) = x * y * L * a + x * y * b + x * c := by ring
  have e2 : x * y * L * (a + b + c) = x * y * L * a + x * y * L * b + x * y * L * c := by ring
  rw [e1, e2]
  omega

section Cost
variable (FP : GapParams) (P : StarParams) (carriers : List (Stars.Carrier P.n)) (L s bb h tl nE Vm T Lw : ℕ)

theorem sbCost_indep (e e' : GapSeed FP) :
    sbCost FP e P carriers L s bb h tl nE Vm T Lw = sbCost FP e' P carriers L s bb h tl nE Vm T Lw := by
  simp only [sbCost, clCost, rbCost, cbCost, sCost, ptCost, mkC, tb, tab_len]

/-- **One point's steps** (with the center's and the counters' per-cell and per-row steps). -/
def ptB (e : GapSeed FP) : ℕ :=
  (sCost FP e carriers s bb h tl nE Vm T + 2 + 5 * (2 * (2 * (s * h) + 1))) +
    (PrimT.Ctr.ctrCost P + 4 + cntCost (dR P) T 0) +
    (3 + 1 + 1 + 1 + (dR P * 20 + 1 + 1 + (5 * (2 * dR P) + 1)) + cntCost (dRow P) T 0)

/-- **One seed's own steps.** -/
def tabB (e : GapSeed FP) : ℕ :=
  1 + 1 + ((9 * Lw + 1) + 1 + (cpCost (tb FP e (Seams.carLen carriers 0)).length + 1 +
    (cpCost (tb FP e (Seams.carLen carriers 1)).length + 1 + ((9 * Lw + 1) + 1 +
      ((3 + 1 + 1 + 1 + (dRow P * 20 + 1 + 1 + (5 * (2 * dRow P) + 1))) + 1 +
        (9 * Lw + 1 + 1 + (4 + 1 + (9 * Lw + 1)))))))) + 2

theorem cb_eq (e : GapSeed FP) : cbCost FP e P carriers L s bb h tl nE Vm T =
    L * (sCost FP e carriers s bb h tl nE Vm T + 2 + 5 * (2 * (2 * (s * h) + 1))) + (PrimT.Ctr.ctrCost P + 4) := by
  unfold cbCost; ring

theorem rb_eq (e : GapSeed FP) : rbCost FP e P carriers L s bb h tl nE Vm T =
    2 ^ dR P * (cbCost FP e P carriers L s bb h tl nE Vm T + cntCost (dR P) T 0) +
      (3 + 1 + 1 + 1 + (dR P * 20 + 1 + 1 + (5 * (2 * dR P) + 1))) := by
  unfold rbCost; rw [cntCost_eq (dR P) T]; ring

theorem cl_eq (e : GapSeed FP) : clCost FP e P carriers L s bb h tl nE Vm T =
    2 ^ dRow P * (rbCost FP e P carriers L s bb h tl nE Vm T + cntCost (dRow P) T 0) +
      (3 + 1 + 1 + 1 + (dRow P * 20 + 1 + 1 + (5 * (2 * dRow P) + 1))) := by
  unfold clCost; rw [cntCost_eq (dRow P) T]; ring

theorem sbCost_le (e : GapSeed FP) (hL : 1 ≤ L) :
    sbCost FP e P carriers L s bb h tl nE Vm T Lw + 2 ≤
      tabB FP P carriers Lw e + 2 ^ dRow P * 2 ^ dR P * L * ptB FP P carriers s bb h tl nE Vm T e := by
  have hk := key_le (2 ^ dRow P) (2 ^ dR P) L (sCost FP e carriers s bb h tl nE Vm T + 2 + 5 * (2 * (2 * (s * h) + 1)))
    (PrimT.Ctr.ctrCost P + 4 + cntCost (dR P) T 0)
    (3 + 1 + 1 + 1 + (dR P * 20 + 1 + 1 + (5 * (2 * dR P) + 1)) + cntCost (dRow P) T 0)
    (Nat.one_le_two_pow) hL
  have hcl : clCost FP e P carriers L s bb h tl nE Vm T =
      2 ^ dRow P * (2 ^ dR P * (L * (sCost FP e carriers s bb h tl nE Vm T + 2 + 5 * (2 * (2 * (s * h) + 1))) +
        (PrimT.Ctr.ctrCost P + 4 + cntCost (dR P) T 0)) +
        (3 + 1 + 1 + 1 + (dR P * 20 + 1 + 1 + (5 * (2 * dR P) + 1)) + cntCost (dRow P) T 0)) +
      (3 + 1 + 1 + 1 + (dRow P * 20 + 1 + 1 + (5 * (2 * dRow P) + 1))) := by
    rw [cl_eq, rb_eq, cb_eq]; ring
  unfold sbCost tabB ptB
  rw [hcl]
  omega

theorem slCost_le (e0 : GapSeed FP) (hL : 1 ≤ L) (es : List (GapSeed FP)) :
    slCost FP P carriers L s bb h tl nE Vm T Lw es ≤
      es.length * tabB FP P carriers Lw e0 +
        es.length * (2 ^ dRow P * 2 ^ dR P * L) * ptB FP P carriers s bb h tl nE Vm T e0 + 1 := by
  unfold slCost
  have := lsum_le es (fun e => sbCost FP e P carriers L s bb h tl nE Vm T Lw + 2)
    (tabB FP P carriers Lw e0 + 2 ^ dRow P * 2 ^ dR P * L * ptB FP P carriers s bb h tl nE Vm T e0)
    (fun e _ => by rw [sbCost_indep FP P carriers L s bb h tl nE Vm T Lw e e0]; exact sbCost_le FP P carriers L s bb h tl nE Vm T Lw e0 hL)
  have e : es.length * (tabB FP P carriers Lw e0 + 2 ^ dRow P * 2 ^ dR P * L * ptB FP P carriers s bb h tl nE Vm T e0) =
      es.length * tabB FP P carriers Lw e0 +
        es.length * (2 ^ dRow P * 2 ^ dR P * L) * ptB FP P carriers s bb h tl nE Vm T e0 := by ring
  omega

end Cost

end NearCubicWires.WireExponent3_5.FinalPass.Sd
