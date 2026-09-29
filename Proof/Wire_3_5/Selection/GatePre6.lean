import Proof.Wire_3_5.Selection.GatePre5

/-! # C1.4: the gate routine's zero words and level word (P3:1339-1358)

Paper: "Enumerate each half's score vectors" (P3:1344-1345). The routine's words start at `0`: the counters `X`, `XP`
(width `lw + 1`), `U`, `UP` (width `s·h + 1`), `CI`, `SY` (width `s`), and the width-`W` words `AC`, `AC'`, `WV`, `TK`, `HT`,
`PW`, `CNT`, `JT`, `ACC`, `EW` (`zws`, sixteen `zw`s); then `PW := 2` (`pwP`). Main declarations: **`zws_spec`**,
**`pwP_spec`**. Paper quantity: none (the machine's words). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat

variable {ns nr : ℕ}

/-- **The zero words.** -/
def zws (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (zw (G 4) (R 44) (R 42) (R 37)) (.seq (zw (G 14) (R 44) (R 42) (R 37)) (.seq (zw (G 5) (R 44) (R 43) (R 37)) (.seq (zw (G 15) (R 44) (R 43) (R 37)) (.seq (zw (G 8) (R 44) (R 2) (R 37)) (.seq (zw (G 9) (R 44) (R 2) (R 37)) (.seq (zw (G 10) (R 44) (R 23) (R 37)) (.seq (zw (G 11) (R 44) (R 23) (R 37)) (.seq (zw (G 12) (R 44) (R 23) (R 37)) (.seq (zw (G 13) (R 44) (R 23) (R 37)) (.seq (zw (G 16) (R 44) (R 23) (R 37)) (.seq (zw (G 17) (R 44) (R 23) (R 37)) (.seq (zw (G 22) (R 44) (R 23) (R 37)) (.seq (zw (G 23) (R 44) (R 23) (R 37)) (.seq (zw (G 24) (R 44) (R 23) (R 37)) (zw (G 25) (R 44) (R 23) (R 37))))))))))))))))

/-- The zero words' cost. -/
def zwsCost (lx ux s W : ℕ) : ℕ :=
  zwCost lx + 1 + (zwCost lx + 1 + (zwCost ux + 1 + (zwCost ux + 1 + (zwCost s + 1 + (zwCost s + 1 + (zwCost W + 1 + (zwCost W + 1 + (zwCost W + 1 + (zwCost W + 1 + (zwCost W + 1 + (zwCost W + 1 + (zwCost W + 1 + (zwCost W + 1 + (zwCost W + 1 + (zwCost W)))))))))))))))

/-- The zero words' state. -/
def zwsSt (G : Fin 28 → Fin (ns + 1)) (σ : WState ns nr) (lx ux s W : ℕ) : WState ns nr :=
  ((((((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))).sets (G 17) (frame (binary W 0))).sets (G 22) (frame (binary W 0))).sets (G 23) (frame (binary W 0))).sets (G 24) (frame (binary W 0))).sets (G 25) (frame (binary W 0))

section ZS
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (cap : ℕ)
include hG hR

set_option maxHeartbeats 4000000 in
/-- **The zero words**: sixteen words at `0`, over their old contents. -/
theorem zws_spec (σ : WState ns nr) (lx ux s W : ℕ) (hsh : ∀ i : Fin 28, σ.sh (G i) = 0) (r40 : σ.val (R 40) = 0)
    (r44 : σ.val (R 44) = 0) (r37 : σ.val (R 37) = 0) (r42 : σ.val (R 42) = lx) (r43 : σ.val (R 43) = ux)
    (r2 : σ.val (R 2) = s) (r23 : σ.val (R 23) = W)
    (hl4 : (σ.st (G 4)).length ≤ 2 * lx + 1) (hl14 : (σ.st (G 14)).length ≤ 2 * lx + 1)
    (hl5 : (σ.st (G 5)).length ≤ 2 * ux + 1) (hl15 : (σ.st (G 15)).length ≤ 2 * ux + 1)
    (hl8 : (σ.st (G 8)).length ≤ 2 * s + 1) (hl9 : (σ.st (G 9)).length ≤ 2 * s + 1)
    (hl10 : (σ.st (G 10)).length ≤ 2 * W + 1) (hl11 : (σ.st (G 11)).length ≤ 2 * W + 1)
    (hl12 : (σ.st (G 12)).length ≤ 2 * W + 1) (hl13 : (σ.st (G 13)).length ≤ 2 * W + 1)
    (hl16 : (σ.st (G 16)).length ≤ 2 * W + 1) (hl17 : (σ.st (G 17)).length ≤ 2 * W + 1)
    (hl22 : (σ.st (G 22)).length ≤ 2 * W + 1) (hl23 : (σ.st (G 23)).length ≤ 2 * W + 1)
    (hl24 : (σ.st (G 24)).length ≤ 2 * W + 1) (hl25 : (σ.st (G 25)).length ≤ 2 * W + 1)
    (hcap : 2 * lx + 2 * ux + 2 * s + 2 * W + 2 ≤ cap) :
    WExec cap (zws G R) σ (zwsSt G σ lx ux s W) (zwsCost lx ux s W) := by
  have zwG' : ∀ (z : Fin 28) (hz : z.val ≠ 2) (nr' : Fin 48) (hnr : nr'.val ≠ 37 ∧ nr'.val ≠ 40 ∧ nr'.val ≠ 44)
      (n : ℕ) (σ' : WState ns nr) (hs : σ'.sh = σ.sh) (hv : σ'.val = σ.val) (hN : σ.val (R nr') = n)
      (hlen : (σ'.st (G z)).length ≤ 2 * n + 1) (hc : 2 * n + 2 ≤ cap),
      WExec cap (zw (G z) (R 44) (R nr') (R 37)) σ' (σ'.sets (G z) (frame (binary n 0))) (zwCost n) := by
    intro z hz nr' hnr n σ' hs hv hN hlen hc
    exact zwG G hG R hR cap z hz nr' hnr n σ' (fun i => by rw [hs]; exact hsh i) (by rw [hv]; exact r40)
      (by rw [hv]; exact r44) (by rw [hv]; exact r37) (by rw [hv]; exact hN) hlen hc
  have x0 := zwG' 4 (by decide) 42 (by decide) lx (σ) rfl rfl r42
    (by rw [show (σ).st (G 4) = σ.st (G 4) by simp [Function.update_apply, hG.eq_iff]]; exact hl4)
    (by omega)
  have x1 := zwG' 14 (by decide) 42 (by decide) lx ((σ).sets (G 4) (frame (binary lx 0))) rfl rfl r42
    (by rw [show ((σ).sets (G 4) (frame (binary lx 0))).st (G 14) = σ.st (G 14) by simp [Function.update_apply, hG.eq_iff]]; exact hl14)
    (by omega)
  have x2 := zwG' 5 (by decide) 43 (by decide) ux (((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))) rfl rfl r43
    (by rw [show (((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).st (G 5) = σ.st (G 5) by simp [Function.update_apply, hG.eq_iff]]; exact hl5)
    (by omega)
  have x3 := zwG' 15 (by decide) 43 (by decide) ux ((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))) rfl rfl r43
    (by rw [show ((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).st (G 15) = σ.st (G 15) by simp [Function.update_apply, hG.eq_iff]]; exact hl15)
    (by omega)
  have x4 := zwG' 8 (by decide) 2 (by decide) s (((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))) rfl rfl r2
    (by rw [show (((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).st (G 8) = σ.st (G 8) by simp [Function.update_apply, hG.eq_iff]]; exact hl8)
    (by omega)
  have x5 := zwG' 9 (by decide) 2 (by decide) s ((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))) rfl rfl r2
    (by rw [show ((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).st (G 9) = σ.st (G 9) by simp [Function.update_apply, hG.eq_iff]]; exact hl9)
    (by omega)
  have x6 := zwG' 10 (by decide) 23 (by decide) W (((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))) rfl rfl r23
    (by rw [show (((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).st (G 10) = σ.st (G 10) by simp [Function.update_apply, hG.eq_iff]]; exact hl10)
    (by omega)
  have x7 := zwG' 11 (by decide) 23 (by decide) W ((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))) rfl rfl r23
    (by rw [show ((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).st (G 11) = σ.st (G 11) by simp [Function.update_apply, hG.eq_iff]]; exact hl11)
    (by omega)
  have x8 := zwG' 12 (by decide) 23 (by decide) W (((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))) rfl rfl r23
    (by rw [show (((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).st (G 12) = σ.st (G 12) by simp [Function.update_apply, hG.eq_iff]]; exact hl12)
    (by omega)
  have x9 := zwG' 13 (by decide) 23 (by decide) W ((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))) rfl rfl r23
    (by rw [show ((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).st (G 13) = σ.st (G 13) by simp [Function.update_apply, hG.eq_iff]]; exact hl13)
    (by omega)
  have x10 := zwG' 16 (by decide) 23 (by decide) W (((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))) rfl rfl r23
    (by rw [show (((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).st (G 16) = σ.st (G 16) by simp [Function.update_apply, hG.eq_iff]]; exact hl16)
    (by omega)
  have x11 := zwG' 17 (by decide) 23 (by decide) W ((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))) rfl rfl r23
    (by rw [show ((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))).st (G 17) = σ.st (G 17) by simp [Function.update_apply, hG.eq_iff]]; exact hl17)
    (by omega)
  have x12 := zwG' 22 (by decide) 23 (by decide) W (((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))).sets (G 17) (frame (binary W 0))) rfl rfl r23
    (by rw [show (((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))).sets (G 17) (frame (binary W 0))).st (G 22) = σ.st (G 22) by simp [Function.update_apply, hG.eq_iff]]; exact hl22)
    (by omega)
  have x13 := zwG' 23 (by decide) 23 (by decide) W ((((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))).sets (G 17) (frame (binary W 0))).sets (G 22) (frame (binary W 0))) rfl rfl r23
    (by rw [show ((((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))).sets (G 17) (frame (binary W 0))).sets (G 22) (frame (binary W 0))).st (G 23) = σ.st (G 23) by simp [Function.update_apply, hG.eq_iff]]; exact hl23)
    (by omega)
  have x14 := zwG' 24 (by decide) 23 (by decide) W (((((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))).sets (G 17) (frame (binary W 0))).sets (G 22) (frame (binary W 0))).sets (G 23) (frame (binary W 0))) rfl rfl r23
    (by rw [show (((((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))).sets (G 17) (frame (binary W 0))).sets (G 22) (frame (binary W 0))).sets (G 23) (frame (binary W 0))).st (G 24) = σ.st (G 24) by simp [Function.update_apply, hG.eq_iff]]; exact hl24)
    (by omega)
  have x15 := zwG' 25 (by decide) 23 (by decide) W ((((((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))).sets (G 17) (frame (binary W 0))).sets (G 22) (frame (binary W 0))).sets (G 23) (frame (binary W 0))).sets (G 24) (frame (binary W 0))) rfl rfl r23
    (by rw [show ((((((((((((((((σ).sets (G 4) (frame (binary lx 0))).sets (G 14) (frame (binary lx 0))).sets (G 5) (frame (binary ux 0))).sets (G 15) (frame (binary ux 0))).sets (G 8) (frame (binary s 0))).sets (G 9) (frame (binary s 0))).sets (G 10) (frame (binary W 0))).sets (G 11) (frame (binary W 0))).sets (G 12) (frame (binary W 0))).sets (G 13) (frame (binary W 0))).sets (G 16) (frame (binary W 0))).sets (G 17) (frame (binary W 0))).sets (G 22) (frame (binary W 0))).sets (G 23) (frame (binary W 0))).sets (G 24) (frame (binary W 0))).st (G 25) = σ.st (G 25) by simp [Function.update_apply, hG.eq_iff]]; exact hl25)
    (by omega)
  unfold zws zwsSt zwsCost
  exact (WExec.seq x0 (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 (WExec.seq x6 (WExec.seq x7 (WExec.seq x8 (WExec.seq x9 (WExec.seq x10 (WExec.seq x11 (WExec.seq x12 (WExec.seq x13 (WExec.seq x14 x15)))))))))))))))

end ZS

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
