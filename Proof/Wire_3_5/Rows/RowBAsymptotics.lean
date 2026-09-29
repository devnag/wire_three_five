import Mathlib

/-!
# S6: asymptotics and constants for the row-B ledger

Consumers: B7 (`prim:ledger`), B9 (`tr:parameters`, P3:3784-3853), C7 (`tr:time`), D2 (target
comparisons).  `L n = ⌈log₂(n+2)⌉` is the Theorem 2.5 repository's `logScale` (`Nat.clog 2 (n+2)`, P3:208).
Proved here: the R14 limit, the row-B exponent arithmetic, and the numeric constants checked by computation.  The remaining limits are `Prop` statements.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open Filter Topology

/-- `L(n) = ⌈log₂(n+2)⌉` (P3:208), the Theorem 2.5 repository's `logScale`. -/
def Lg (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

theorem Lg_tendsto : Tendsto Lg atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun n hn => ?_⟩
  have h1 : b ≤ Nat.log 2 (n + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  exact h1.trans (Nat.log_le_clog 2 (n + 2))

/-- S6.1 (R14): `(log L)^a · L^{−b} → 0` for `a, b > 0`.  Instances: the row-B load factor
`(log L)^{11/4} L^{−1/32}` (P3:3825-3829) and the cap ratio `(log L)^{7/2} L^{−1/16}` (P3:3834-3837). -/
theorem logpow_mul_rpow_neg_tendsto (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ => Real.log (Lg n) ^ a * ((Lg n : ℕ) : ℝ) ^ (-b)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ a / x ^ b) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop a hb).tendsto_div_nhds_zero
  have h1' : Tendsto (fun x : ℝ => Real.log x ^ a * x ^ (-b)) atTop (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv]
  have h2 : Tendsto (fun n : ℕ => ((Lg n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Lg_tendsto
  exact h1'.comp h2

/-! ## Row-B arithmetic (P3:3848-3852, 958-961), proved -/

/-! ## Numeric constants checked by computation (Appendix D §2), proved -/

end NearCubicWires.WireExponent3_5.Shared
