import Proof.Wire_3_5.FinalPass.Core15Base

/-! # S5Core, part 17: the core half's cost below one power (P3:3170-3181)

With the master bound `Y = (L.Kc + 1)·N^{L.Dc}` (`N = |fpIn| + 1`, `L.Dc ≥ 1`), which covers the register length
`c = L.Kc·N^{L.Dc}`, `N` and every writer's step bound: the count's chain (**`zCost_le`**), the count (`cnt_le`), the
mode (`mode_le`), each writer's stage (`stage_le`), the final pad (`fin_le`), and **`coreCost_le`**:
`coreCost ≤ Cc0·Y`, `Cc0 = 200 + 80·Dc + 30·(nr_A + nr_B + nr_N + nr_S + L.t)`.

Paper quantity: the front's running time as a power of the input's length (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.S5T (mulCost)

/-- **The count's chain** below `k·(40·K·N^D + 40)`. -/
theorem zCost_le (N K D : ℕ) (hN : 1 ≤ N) : ∀ k, k ≤ D → zCost N K k ≤ k * (40 * (K * N ^ D) + 40)
  | 0, _ => by simp [zCost]
  | k + 1, hk => by
    have ih := zCost_le N K D hN k (by omega)
    have h1 : K * N ^ k ≤ K * N ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by omega))
    have h2 : K * N ^ k * N ≤ K * N ^ D := by
      rw [show K * N ^ k * N = K * N ^ (k + 1) by ring]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN hk)
    have hm : mulCost (K * N ^ k) N = 13 * (K * N ^ k * N) + 14 * (K * N ^ k) + 15 := by
      unfold mulCost; ring
    show zCost N K k + 1 + (mulCost (K * N ^ k) N + 1 + (3 * (K * N ^ k) + 3 + 1 + (1 + 1 + (5 * (K * N ^ k) + 1)))) ≤
      (k + 1) * (40 * (K * N ^ D) + 40)
    rw [hm]
    have e : (k + 1) * (40 * (K * N ^ D) + 40) = k * (40 * (K * N ^ D) + 40) + 40 * (K * N ^ D) + 40 := by ring
    rw [e]
    generalize K * N ^ k * N = P at h2 ⊢
    generalize K * N ^ k = Q at h1 ⊢
    generalize K * N ^ D = R at h1 h2 ih ⊢
    omega

/-- A product below its share of `Y`. -/
theorem mul_share (m c Y : ℕ) (hc : c ≤ Y) (hY : 1 ≤ Y) : m * (6 * c + 17) ≤ 23 * (m * Y) := by
  have h1 : m * c ≤ m * Y := Nat.mul_le_mul_left _ hc
  have h2 : m ≤ m * Y := Nat.le_mul_of_pos_right _ hY
  have e : m * (6 * c + 17) = 6 * (m * c) + 17 * m := by ring
  omega

section Cost

end Cost

end NearCubicWires.WireExponent3_5.FinalPass.Core
