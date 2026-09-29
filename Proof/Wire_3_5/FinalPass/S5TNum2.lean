import Proof.Wire_3_5.FinalPass.S5TNum1

/-! # S5-THR, part 36: the THR half's whole cost as a multiple of `W` (P3:3105-3115)

The THR half on the scrub layout (`thrM_step`) costs the prelude, the scrub of a stage within `W`, and the erasers
(`128` registers, the driver): all within `(43·D + 6000)·y^{D+1}` at the padded count base `y = |u| + 1 + c_0`
(**`total_le`**; `mulCost_le`, `chainCost_le`, `preTotal3_le`), and `y^{e} ≤ (c_0+1)^{e}·(|u|+1)^{e}`
(**`pow_split`**).

Paper quantity of the main type: the front's running time within the preprocessing form `C·(|input|+1)^{D}`
(P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T

section Tot

theorem mulCost_le (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : mulCost a b ≤ 42 * (a * b) := by
  unfold mulCost
  have : a ≤ a * b := Nat.le_mul_of_pos_right _ hb
  have : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  nlinarith

theorem chainCost_le (b D : ℕ) (hb : 1 ≤ b) : ∀ k, k ≤ D → chainCost b k ≤ 43 * k * b ^ (D + 1)
  | 0, _ => by simp [chainCost]
  | k + 1, hk => by
    have ih := chainCost_le b D hb k (by omega)
    have hm := mulCost_le (b ^ (k + 1)) b (Nat.one_le_pow _ _ hb) hb
    have e : b ^ (k + 1) * b = b ^ (k + 2) := by ring
    have hp : b ^ (k + 2) ≤ b ^ (D + 1) := Nat.pow_le_pow_right hb (by omega)
    have h1 : 1 ≤ b ^ (D + 1) := Nat.one_le_pow _ _ hb
    show chainCost b k + 1 + mulCost (b ^ (k + 1)) b ≤ 43 * (k + 1) * b ^ (D + 1)
    rw [e] at hm
    have e2 : 43 * (k + 1) * b ^ (D + 1) = 43 * k * b ^ (D + 1) + 43 * b ^ (D + 1) := by ring
    omega

theorem preTotal3_le (b c0 D : ℕ) (hb : 1 ≤ b) : preTotal3 b c0 D ≤ (43 * D + 183) * (b + c0) ^ (D + 1) := by
  have hy : 1 ≤ b + c0 := by omega
  have hc := chainCost_le (b + c0) D hy D le_rfl
  have hY : b + c0 ≤ (b + c0) ^ (D + 1) := Nat.le_self_pow (by omega) _
  unfold preTotal3 preCost3 preCost2
  have e : (43 * D + 183) * (b + c0) ^ (D + 1) = 43 * D * (b + c0) ^ (D + 1) + 183 * (b + c0) ^ (D + 1) := by ring
  omega

/-- **The THR half's whole cost** (`thrM_step`'s count) at a stage within `W = y^{D+1}`. -/
theorem total_le (b c0 D n : ℕ) (hb : 1 ≤ b) (hn : n ≤ (b + c0) ^ (D + 1)) :
    preTotal3 b c0 D + 1 + (2 * n + 2 + 1 + (2 * (b + c0) ^ (D + 1) + 4)) + 1 +
      (nrL * (6 * (2 * (b + c0) ^ (D + 1) + 3) + 12) + 1 + (6 * (b + c0) ^ (D + 1) + 8)) ≤
      (43 * D + 6000) * (b + c0) ^ (D + 1) := by
  have hp := preTotal3_le b c0 D hb
  have h1 : 1 ≤ (b + c0) ^ (D + 1) := Nat.one_le_pow _ _ (by omega)
  have e : (43 * D + 6000) * (b + c0) ^ (D + 1) = (43 * D + 183) * (b + c0) ^ (D + 1) + 5817 * (b + c0) ^ (D + 1) := by
    ring
  show _ ≤ _
  simp only [nrL]
  omega

/-- The padded base below a multiple of the input's length. -/
theorem pow_split (N c0 e : ℕ) (hN : 1 ≤ N) : (N + c0) ^ e ≤ (c0 + 1) ^ e * N ^ e := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by nlinarith) e

end Tot

end NearCubicWires.WireExponent3_5.FinalPass.S5T
