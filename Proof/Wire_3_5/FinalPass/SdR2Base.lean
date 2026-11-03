import Proof.Wire_3_5.FinalPass.SdI10Base
import Proof.Wire_3_5.Primitive.Writers.CallIndexRBase

/-! # S4 v2, part R2: the numbers' width with the degree on `(l, fe)` alone (P3:3044-3048, 3114-3115)

S4 v1's exponents (`Sd.ZV`, `Sd.ZT`, `Sd.C1m`) come from `CallIndex`, whose cap exponent `capZ l F` carries `51·c_r`,
so S4's degrees depend on `F`. Here the same width is bounded through `CallIndexR` (the exponents on `l` and the
filter error degree `fe` only, `c_r` in the coefficients: `gapSeed_leR`, `flatSeed_leR`, `symCount_leR`,
`thrCount_leR`): **`ZV`**, **`ZT`** on `(l, fe)`, **`KT`** on `F`, the width **`Tf r = KT·(n+2)^{ZT}`**,
**`ptv_lt`** (`ptCount·vmax < 2^{Tf r}`), **`fpNum_lt`**, **`n2_le_Tf`**. Namespace `Sd.R`: S4 v2's names shadow v1's.

Paper quantity of the main type: the width of the printed numerator, its powers of `n` fixed before the gate
(P3:3044-3048, 3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd.R
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split

/-- **The exponent sum below the width**, the coefficients inside. -/
theorem expo_ltR (n g q v a b c Z : ℕ) (ha : a ≤ Z) (hb : b ≤ Z) (hc : c ≤ Z) (h2 : 2 ≤ Z) :
    n + g * (n + 2) ^ a + ((2 * (n * n) + 1) + q * (n + 2) ^ b) + v * (n + 2) ^ c <
      (g + q + v + 8) * (n + 2) ^ Z := by
  have hN : 1 ≤ n + 2 := by omega
  have hy2 : (n + 2) ^ 2 ≤ (n + 2) ^ Z := Nat.pow_le_pow_right hN h2
  have ha' := Nat.mul_le_mul_left g (Nat.pow_le_pow_right hN ha)
  have hb' := Nat.mul_le_mul_left q (Nat.pow_le_pow_right hN hb)
  have hc' := Nat.mul_le_mul_left v (Nat.pow_le_pow_right hN hc)
  have hsq : n * n + 4 * n + 4 = (n + 2) ^ 2 := by ring
  have e : (g + q + v + 8) * (n + 2) ^ Z = g * (n + 2) ^ Z + q * (n + 2) ^ Z + v * (n + 2) ^ Z + 8 * (n + 2) ^ Z := by
    ring
  rw [e]
  generalize (n + 2) ^ Z = y at hy2 ha' hb' hc' ⊢
  generalize (n + 2) ^ 2 = s at hsq hy2
  generalize n * n = m at hsq ⊢
  omega

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R
