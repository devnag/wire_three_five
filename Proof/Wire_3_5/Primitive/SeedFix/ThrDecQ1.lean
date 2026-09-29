import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF4

/-! # THR decode front, packaging part 1: the quasi-polynomial calculus

`ThrDecFront`'s capacity `need` and cost `bound` are `RadSetup.QuasiBounded`: `v ≤ C·(n+2)^D·2^{K·L²}`,
`L = ⌈log₂(n+2)⌉` (the paper's `2^{O(L²)}` expansion, P3:2597-2599), with the exponents `D`, `K` fixed before the gate
(`StageU`) and the coefficient `C` after it. The closure rules: constants, `n + c`, `2^{c·L}`, `2^{c·L²}`, sums,
products, powers, and monotonicity.

Paper quantity of the main type: none (the class `2^{O(L²)}` of P3:2597-2599, 3089-3108, as a calculus). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimThrW.RadSetup

theorem two_pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 (n + 2) ≤ 2 * (n + 2) := by
  rcases Nat.eq_zero_or_pos (Nat.clog 2 (n + 2)) with h | h
  · rw [h]; omega
  · have h1 : 2 ^ (Nat.clog 2 (n + 2) - 1) < n + 2 := by
      have := Nat.pow_pred_clog_lt_self (b := 2) (x := n + 2) (by norm_num) (by omega)
      simpa [Nat.pred_eq_sub_one] using this
    have e : 2 ^ Nat.clog 2 (n + 2) = 2 * 2 ^ (Nat.clog 2 (n + 2) - 1) := by
      rw [← pow_succ']; congr 1
    omega

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
